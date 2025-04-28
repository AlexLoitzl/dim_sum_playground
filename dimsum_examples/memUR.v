From iris.algebra Require Export dfrac.
From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core.iris Require Export biown.
From dimsum.core.iris Require Import weak_embed.
From dimsum.examples Require Import asm.

Set Default Proof Using "Type".

(** * memUR *)
Definition memUR : ucmra :=
  (gmap_viewUR Z (agreeR (option Z))).

Global Instance memUR_shrink : Shrink memUR.
Proof. solve_shrink. Qed.

Section memUR.
  Context {PROP : bi} `{!BiBUpd PROP} (Own : BiOwn PROP memUR).

  Definition memUR_inj (m : gmap_viewUR Z (agreeR (option Z))) : PROP :=
    bi_own Own m.

  Definition memUR_auth (mem : gmap Z (option Z)) : PROP :=
    memUR_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> mem).

  Definition memUR_ptsto (a : Z) (dq : dfrac) (v : option Z) : PROP :=
    memUR_inj $ gmap_view_frag a dq (to_agree v).

  Definition memUR_inv (mem : gmap Z (option Z)) : PROP :=
    memUR_auth mem.
End memUR.

Notation "a ↦[ O ]ₘ dq v" := (memUR_ptsto O a dq v)
  (at level 20, dq custom dfrac at level 1, format "a  ↦[ O ]ₘ dq  v") : bi_scope.

Section memUR.
  Context {PROP : bi} `{!BiBUpd PROP} (O : BiOwn PROP memUR).

  (** _auth lemmas are internal lemmas *)
  Lemma memUR_auth_ext mem mem':
    mem = mem' →
    memUR_auth O mem ⊢ memUR_auth O mem'.
  Proof. by move => ->. Qed.

  Lemma memUR_auth_alloc mem a v :
    mem !! a = None →
    memUR_auth O mem ⊢ |==>
    memUR_auth O (<[a:=v]>mem) ∗ a ↦[O]ₘ v.
  Proof.
    move => ?. rewrite -bi_own_op. apply bi_own_bupd.
    rewrite fmap_insert. apply gmap_view_alloc; [|done..].
    by rewrite lookup_fmap fmap_None.
  Qed.

  Lemma memUR_auth_alloc_big mem' mem :
    mem' ##ₘ mem →
    memUR_auth O mem ==∗
    memUR_auth O (mem' ∪ mem) ∗ [∗ map] a↦v∈mem', a ↦[O]ₘ v.
  Proof.
    iIntros (?) "Hmem".
    iInduction mem' as [|a v mem' ?] "IH" using map_ind;
      rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
    { rewrite left_id big_sepM_empty. by iFrame. }
    iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
    iMod (memUR_auth_alloc with "[$]") as "[$ ?]".
    { apply lookup_union_None. split!. }
    rewrite big_sepM_insert //. by iFrame.
  Qed.

  Lemma memUR_auth_lookup mem a dq v :
    memUR_auth O mem -∗
    a ↦[O]ₘ{dq} v -∗
    ⌜mem !! a = Some v⌝.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    move => /(gmap_view_both_dfrac_valid_discrete_total _ _ _)+.
    move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
    move => /to_agree_included_L. naive_solver.
  Qed.

  Lemma memUR_auth_lookup_big mem mem' dq:
    memUR_auth O mem -∗
    ([∗ map] a↦v∈mem', a ↦[O]ₘ{dq} v) -∗
    ⌜mem' ⊆ mem⌝.
  Proof.
    iIntros "Hmem Hmem'".
    iInduction mem' as [|a v mem' ?] "IH" using map_ind.
    { iPureIntro. apply map_empty_subseteq. }
    iDestruct (big_sepM_insert with "Hmem'") as "[??]"; [done|].
    iDestruct ("IH" with "[$] [$]") as %?.
    iDestruct (memUR_auth_lookup with "[$] [$]") as %?.
    iPureIntro. by apply insert_subseteq_l.
  Qed.


  Lemma memUR_auth_update v' mem a v :
    memUR_auth O mem ∗ a ↦[O]ₘ v ⊢ |==>
    memUR_auth O (<[a:=v']>mem) ∗ a ↦[O]ₘ v'.
  Proof.
    rewrite -!bi_own_op. apply bi_own_bupd. rewrite fmap_insert.
    by apply gmap_view_replace.
  Qed.

  Lemma memUR_auth_free mem a v :
    memUR_auth O mem ∗ a ↦[O]ₘ v ⊢ |==>
    memUR_auth O (delete a mem).
  Proof.
    rewrite -!bi_own_op. apply bi_own_bupd. rewrite fmap_delete.
    by apply gmap_view_delete.
  Qed.

  Lemma memUR_ptsto_auth_free_big mem' mem :
    memUR_auth O mem -∗
    ([∗ map] a↦v∈mem', a  ↦[O]ₘ v) ==∗
    memUR_auth O (mem ∖ mem').
  Proof.
    iIntros "Hmem Hmem'".
    iInduction mem' as [|a v mem' ?] "IH" using map_ind;
      rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
    { rewrite right_id. by iFrame. }
    iDestruct (big_sepM_insert with "Hmem'") as "[??]"; [done|].
    iMod ("IH" with "[$] [$]") as "?".
    iMod (memUR_auth_free with "[$]") as "?".
    by rewrite -delete_difference.
  Qed.

  (** clients should not unfold _inv and only use the lemmas starting from here *)
  Lemma memUR_ptsto_excl a v1 v2 :
    a ↦[O]ₘ v1 -∗ a ↦[O]ₘ v2 -∗ False.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    move => /(gmap_view_frag_op_valid _ _ _)[??].
    done.
  Qed.

  Lemma memUR_alloc mem a v :
    mem !! a = None →
    memUR_inv O mem ==∗
    memUR_inv O (<[a:=v]>mem) ∗
    a ↦[O]ₘ v.
  Proof. iIntros (?) "?". by iApply (memUR_auth_alloc with "[$]"). Qed.

  Lemma memUR_alloc_big mem' mem :
    mem' ##ₘ mem →
    memUR_inv O mem ==∗
    memUR_inv O (mem' ∪ mem) ∗ [∗ map] a↦v∈mem', a ↦[O]ₘ v.
  Proof. iIntros (?). by iApply memUR_auth_alloc_big. Qed.

  Lemma memUR_lookup mem a dq v:
    memUR_inv O mem -∗
    a ↦[O]ₘ{dq} v -∗
    ⌜mem !! a = Some v⌝.
  Proof. iApply memUR_auth_lookup. Qed.

  Lemma memUR_lookup_big mem m dq:
    memUR_inv O mem -∗
    ([∗ map]a↦v∈m, a ↦[O]ₘ{dq} v) -∗
    ⌜m ⊆ mem⌝.
  Proof. iApply memUR_auth_lookup_big. Qed.

  Lemma memUR_update v' mem a v:
    memUR_inv O mem -∗
    a ↦[O]ₘ v ==∗
    memUR_inv O (<[a := v']>mem) ∗ a ↦[O]ₘ v'.
  Proof. iIntros "??". iApply memUR_auth_update. iFrame. Qed.

  Lemma memUR_free a mem v:
    memUR_inv O mem -∗
    a ↦[O]ₘ v ==∗
    memUR_inv O (delete a mem).
  Proof. iIntros "Hinv Hb". iApply memUR_auth_free. iFrame. Qed.

  Lemma memUR_free_big mem' mem :
    memUR_inv O mem -∗
    ([∗ map] a↦v∈mem', a  ↦[O]ₘ v) ==∗
    memUR_inv O (mem ∖ mem').
  Proof. iApply memUR_ptsto_auth_free_big. Qed.

  (** init *)
  Definition memUR_init : memUR :=
    (gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)).

  Lemma memUR_init_valid :
    ✓ memUR_init.
  Proof. by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1)). Qed.

  Lemma memUR_init_own :
    bi_own O memUR_init ⊢ memUR_inv O ∅.
  Proof.
    have ? := bi_own_proper _ _ O. rewrite /memUR_init. iIntros "$".
  Qed.

End memUR.

Global Typeclasses Opaque memUR_ptsto memUR_inv.
Global Opaque memUR_ptsto memUR_inv.

(** * Trader for memUR *)

Section trader.
  Context {PROP1 PROP2 PROP : bi} `{!BiBUpd PROP1} `{!BiBUpd PROP2}.
  Context (W1 : BiWeakEmbed PROP1 PROP) (W2 : BiWeakEmbed PROP2 PROP).
  Context (O1 : BiOwn PROP1 memUR) (O2 : BiOwn PROP2 memUR).

  Definition memUR_ptsto_trader (a : Z) (v : option Z) : PROP :=
    ⌈a ↦[O1]ₘ v @ W1⌉ ∨ ⌈a ↦[O2]ₘ v @ W2⌉.
  Definition memUR_mem_trader (mem : gmap Z (option Z)) : PROP :=
    ⌈memUR_inv O1 mem @ W1⌉ ∗
    ([∗ map] a↦v∈mem, memUR_ptsto_trader a v).

  Definition memUR_trader : PROP := ∃ h, memUR_mem_trader h.

  Context `{!BiBUpd PROP} `{!BiAffine PROP} `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.

  Lemma memUR_ptsto_trader_in_1 mem2 a v :
    mem2 !! a = None →
    ⌈memUR_inv O2 mem2 @ W2⌉ -∗
    memUR_ptsto_trader a v -∗
    ⌈a ↦[O1]ₘ v @ W1⌉ ∗ ⌈memUR_inv O2 mem2 @ W2⌉.
  Proof using BiAffine0.
    iIntros (?) "? [$|?]" => //.
    iDestruct (memUR_lookup O2 with "[$] [$]") as %?.
    naive_solver.
  Qed.

  Lemma memUR_mem_trader_equalize mem1 mem2 :
    memUR_mem_trader mem1 -∗
    ⌈memUR_inv O2 mem2 @ W2⌉ ==∗⌈W1⌉
    memUR_mem_trader mem2 ∗
    ⌈memUR_inv O2 mem2 @ W2⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "(Hinv1 & Hb) Hinv2".
    iInduction mem1 as [a v ? Hp1 Hp2|a v ? Hp1 Hp2|a v1 v2 ? Hp1 Hp2|] "IH" using (map_equalize_ind mem2).
    - iMod (memUR_alloc O1 _ a v with "Hinv1") as "[? Hbs]"; [done|].
      iApply ("IH" with "[$] [Hb Hbs] [$]").
      iApply (big_sepM_insert_2 with "[Hbs] Hb"). by iLeft.
    - iDestruct (big_sepM_delete with "Hb") as "[? Hm]"; [done|].
      iDestruct (memUR_ptsto_trader_in_1 with "[$] [$]") as "[? ?]"; [done|].
      iMod (memUR_free O1 with "[$] [$]").
      by iApply ("IH" with "[$] [Hm] [$]").
    - iDestruct (big_sepM_insert_acc with "Hb") as "[Hb Hc]"; [done|].
      iDestruct "Hb" as "[Hb|Hb]".
      + iMod (memUR_update O1 with "[$] Hb") as "[??]".
        iDestruct ("Hc" with "[$]") as "?".
        iApply ("IH" with "[$] [$] [$]").
      + iDestruct (memUR_lookup O2 with "[$] [$]") as %?. simplify_map_eq.
        iDestruct ("Hc" with "[$]") as "?".
        rewrite insert_id //.
        iApply ("IH" with "[$] [$] [$]").
    - by iFrame.
  Qed.

  Lemma memUR_ptsto_trader_trade a v :
    ⌈a ↦[O2]ₘ v @ W2⌉ -∗
    memUR_ptsto_trader a v -∗
    memUR_ptsto_trader a v ∗
    ⌈a ↦[O1]ₘ v @ W1⌉.
  Proof using BiAffine0.
    iIntros "Hl [?|?]".
    - by iFrame "Hl".
    - iDestruct (memUR_ptsto_excl O2 with "[$] [$]") as %[].
  Qed.

  (** Trader lemmas  *)
  Lemma memUR_trader_init mem :
    ⌈memUR_inv O1 mem @ W1⌉ -∗
    ⌈[∗ map] a↦v∈mem, a↦[O2]ₘ v @ W2⌉ -∗
    memUR_trader.
  Proof using BiAffine0.
    iIntros "? Hinit". iFrame.
    rewrite !weak_embed_big_sepM.
    iApply (big_sepM_impl with "Hinit"). iIntros "!>" (???) "?". by iRight.
  Qed.

  Lemma memUR_trade_ptsto mem a v:
    memUR_trader -∗
    ⌈memUR_inv O2 mem @ W2⌉ -∗
    ⌈a ↦[O2]ₘ v @ W2⌉ ==∗⌈W1⌉
    memUR_trader ∗
    ⌈memUR_inv O2 mem @ W2⌉ ∗
    ⌈a ↦[O1]ₘ v @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "[%m1 Hinv1] Hinv2 Hl".
    iMod (memUR_mem_trader_equalize with "Hinv1 [$]") as "[[Hinv1 Hbs] Hinv2]".
    iDestruct (memUR_lookup O2 with "[$] Hl") as %?.
    iDestruct (big_sepM_lookup_acc with "Hbs") as "[Hm Hc]"; [done|].
    iDestruct (memUR_ptsto_trader_trade with "[$] [$]") as "[? $]".
    iDestruct ("Hc" with "[$]") as "?".
    by iFrame.
  Qed.

  Lemma memUR_trade_ptsto_big mem m:
    memUR_trader -∗
    ⌈memUR_inv O2 mem @ W2⌉ -∗
    ⌈[∗ map] a↦v∈m, a ↦[O2]ₘ v @ W2⌉ ==∗⌈W1⌉
    memUR_trader ∗
    ⌈memUR_inv O2 mem @ W2⌉ ∗
    ⌈[∗ map] a↦v∈m, a ↦[O1]ₘ v @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "Ht Hinv Hl".
    iInduction m as [|] "IH" using map_ind.
    { iModIntro. iFrame. iModIntro. done. }
    rewrite !big_sepM_insert //. iDestruct "Hl" as "[??]".
    iMod (memUR_trade_ptsto with "[$] [$] [$]") as "[? [? $]]".
    iApply ("IH" with "[$] [$] [$]").
  Qed.
End trader.

Section trader.
  Context {PROP1 PROP2 PROP : bi} `{!BiBUpd PROP1} `{!BiBUpd PROP2}.
  Context (W1 : BiWeakEmbed PROP1 PROP) (W2 : BiWeakEmbed PROP2 PROP).
  Context (O1 : BiOwn PROP1 memUR) (O2 : BiOwn PROP2 memUR).
  Context `{!BiBUpd PROP} `{!BiAffine PROP} `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.

  Lemma memUR_ptsto_trader_switch a v :
    memUR_ptsto_trader W1 W2 O1 O2 a v -∗
    memUR_ptsto_trader W2 W1 O2 O1 a v.
  Proof using BiAffine0. iIntros "[$|$]". Qed.

  (** Trader lemmas  *)
  Lemma memUR_trader_switch mem :
    memUR_trader W1 W2 O1 O2 -∗
    ⌈memUR_inv O2 mem @ W2⌉ ==∗⌈W1⌉
    memUR_trader W2 W1 O2 O1 ∗
    ⌈memUR_inv O1 mem @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "[%h1 Hinv1] Hinv2".
    iMod (memUR_mem_trader_equalize with "Hinv1 [$]") as "[[??] ?]".
    iModIntro. iFrame. iApply (big_sepM_impl with "[$]").
    iIntros "!>" (???) "?". by iApply memUR_ptsto_trader_switch.
  Qed.

End trader.

Global Typeclasses Opaque memUR_trader.
Global Opaque memUR_trader.
