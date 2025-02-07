From iris.algebra Require Export dfrac.
From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core.iris Require Export biown.
From dimsum.examples Require Import rec.

Set Default Proof Using "Type".

(** * heapUR *)
Canonical Structure valO := leibnizO val.
Canonical Structure locO := leibnizO loc.

Definition heapUR : ucmra :=
  (prodUR (gmap_viewUR loc (agreeR valO))
     (gmap_viewUR prov (agreeR (gsetO Z)))).

Global Instance : Shrink (gmap_viewUR loc (agreeR valO)).
Proof. solve_shrink. Qed.
Global Instance : Shrink (gmap_viewUR prov (agreeR (gsetO Z))).
Proof. solve_shrink. Qed.

Global Instance heapUR_shrink : Shrink heapUR.
Proof. solve_shrink. Qed.

Section heapUR.
  Context {PROP : bi} `{!BiBUpd PROP} (Own : BiOwn PROP heapUR).

  Definition heapUR_heap_inj (h : gmap_viewUR loc (agreeR valO)) : PROP :=
    bi_own Own (h, ε).

  Definition heapUR_dom_inj (h : gmap_viewUR prov (agreeR (gsetO Z))) : PROP :=
    bi_own Own (ε, h).

  Definition heapUR_ptsto_auth (h : gmap loc val) : PROP :=
    heapUR_heap_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> h).
  Definition heapUR_dom_auth (d : gmap prov (gset Z)) : PROP :=
    heapUR_dom_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> d).

  Definition heapUR_ptsto (l : loc) (dq : dfrac) (v : val) : PROP :=
    heapUR_heap_inj $ gmap_view_frag l dq (to_agree v).
  Definition heapUR_dom (p : prov) (dq : dfrac) (d : gset Z) : PROP :=
    heapUR_dom_inj $ gmap_view_frag p dq (to_agree d).

  Definition heapUR_block (p : prov) (dq : dfrac) (b : gmap Z val) : PROP :=
    heapUR_dom p dq (dom b) ∗ [∗ map] l↦v∈kmap (pair p) b, heapUR_ptsto l dq v.

  Definition heapUR_uninit_block (p : prov) (dq : dfrac) (b : gset Z) : PROP :=
    heapUR_dom p dq b ∗ [∗ set] l∈set_map (pair p) b, ∃ v, heapUR_ptsto l dq v.

  Definition heapUR_inv (h : heap_state) : PROP :=
    heapUR_ptsto_auth (h_heap h) ∗
    heapUR_dom_auth (set_to_map (λ p, (p, dom (h_block h p))) (h_provs h)).

  (** _auth lemmas are internal lemmas *)
  Lemma heapUR_ptsto_auth_ext h h':
    h = h' →
    heapUR_ptsto_auth h ⊢ heapUR_ptsto_auth h'.
  Proof. by move => ->. Qed.

  Lemma heapUR_dom_auth_ext d d':
    d = d' →
    heapUR_dom_auth d ⊢ heapUR_dom_auth d'.
  Proof. by move => ->. Qed.


  Lemma heapUR_ptsto_auth_alloc h l v :
    h !! l = None →
    heapUR_ptsto_auth h ⊢ |==>
    heapUR_ptsto_auth (<[l:=v]>h) ∗ heapUR_ptsto l (DfracOwn 1) v.
  Proof.
    move => ?. rewrite -bi_own_op. apply bi_own_bupd.
    apply prod_update; [|done] => /=. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
  Qed.

  Lemma heapUR_ptsto_auth_alloc_big h' h :
    h' ##ₘ h →
    heapUR_ptsto_auth h ==∗
    heapUR_ptsto_auth (h' ∪ h) ∗ [∗ map] l↦v∈h', heapUR_ptsto l (DfracOwn 1) v.
  Proof.
    iIntros (?) "Hh".
    iInduction h' as [|l v h' ?] "IH" using map_ind;
      rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
    { rewrite left_id big_sepM_empty. by iFrame. }
    iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
    iMod (heapUR_ptsto_auth_alloc with "[$]") as "[$ ?]".
    { apply lookup_union_None. split!. }
    rewrite big_sepM_insert //. by iFrame.
  Qed.

  Lemma heapUR_ptsto_auth_lookup h l dq v :
    heapUR_ptsto_auth h -∗
    heapUR_ptsto l dq v -∗
    ⌜h !! l = Some v⌝.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op.
    move => [/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _].
    move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
    move => /to_agree_included_L. naive_solver.
  Qed.

  Lemma heapUR_ptsto_auth_lookup_big h h' dq:
    heapUR_ptsto_auth h -∗
    ([∗ map] l↦v∈h', heapUR_ptsto l dq v) -∗
    ⌜h' ⊆ h⌝.
  Proof.
    iIntros "Hh Hh'".
    iInduction h' as [|l v h' ?] "IH" using map_ind.
    { iPureIntro. apply map_empty_subseteq. }
    iDestruct (big_sepM_insert with "Hh'") as "[??]"; [done|].
    iDestruct ("IH" with "[$] [$]") as %?.
    iDestruct (heapUR_ptsto_auth_lookup with "[$] [$]") as %?.
    iPureIntro. by apply insert_subseteq_l.
  Qed.


  Lemma heapUR_ptsto_auth_update v' h l v :
    heapUR_ptsto_auth h ∗ heapUR_ptsto l (DfracOwn 1) v ⊢ |==>
    heapUR_ptsto_auth (<[l:=v']>h) ∗ heapUR_ptsto l (DfracOwn 1) v'.
  Proof.
    rewrite -!bi_own_op. apply bi_own_bupd. rewrite -!pair_op.
    apply prod_update; [|done] => /=. rewrite fmap_insert.
    by apply gmap_view_replace.
  Qed.

  Lemma heapUR_ptsto_auth_free h l v :
    heapUR_ptsto_auth h ∗ heapUR_ptsto l (DfracOwn 1) v ⊢ |==>
    heapUR_ptsto_auth (delete l h).
  Proof.
    rewrite -!bi_own_op. rewrite -!pair_op. apply bi_own_bupd.
    apply prod_update; [|done] => /=. rewrite fmap_delete.
    by apply gmap_view_delete.
  Qed.

  Lemma heapUR_ptsto_auth_free_big h' h :
    heapUR_ptsto_auth h -∗
    ([∗ map] l↦v∈h', heapUR_ptsto l (DfracOwn 1) v) ==∗
    heapUR_ptsto_auth (h ∖ h').
  Proof.
    iIntros "Hh Hh'".
    iInduction h' as [|l v h' ?] "IH" using map_ind;
      rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
    { rewrite right_id. by iFrame. }
    iDestruct (big_sepM_insert with "Hh'") as "[??]"; [done|].
    iMod ("IH" with "[$] [$]") as "?".
    iMod (heapUR_ptsto_auth_free with "[$]") as "?".
    by rewrite -delete_difference.
  Qed.


  Lemma heapUR_dom_auth_alloc d p s :
    d !! p = None →
    heapUR_dom_auth d ⊢ |==>
    heapUR_dom_auth (<[p:=s]>d) ∗ heapUR_dom p (DfracOwn 1) s.
  Proof.
    move => ?. rewrite -bi_own_op. rewrite -pair_op. apply bi_own_bupd.
    apply prod_update; [done|] => /=. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
  Qed.

  Lemma heapUR_dom_auth_lookup d p dq s :
    heapUR_dom_auth d -∗
    heapUR_dom p dq s -∗
    ⌜d !! p = Some s⌝.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op.
    move => [_ /(gmap_view_both_dfrac_valid_discrete_total _ _ _)+].
    move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
    move => /to_agree_included_L. naive_solver.
  Qed.

  Lemma heapUR_dom_auth_update s' d p s :
    heapUR_dom_auth d ∗ heapUR_dom p (DfracOwn 1) s ⊢ |==>
    heapUR_dom_auth (<[p:=s']>d) ∗ heapUR_dom p (DfracOwn 1) s'.
  Proof.
    rewrite -!bi_own_op. rewrite -!pair_op. apply bi_own_bupd.
    apply prod_update; [done|] => /=. rewrite fmap_insert.
    by apply gmap_view_replace.
  Qed.

  (** clients should not unfold _inv and only use the lemmas starting from here *)
  Lemma heapUR_uninit_block_eq p dq d `{!BiAffine PROP}:
    heapUR_uninit_block p dq d ⊣⊢ ∃ b, ⌜d = dom b⌝ ∗ heapUR_block p dq b.
  Proof.
    iSplit.
    - iIntros "[? Hd]". rewrite big_opS_set_map.
      iDestruct (big_sepS_exist with "[$]") as (? ->) "?".
      iExists _. iSplit; [done|]. iFrame. by rewrite big_sepM_kmap_intro.
    - iIntros "[% [-> [??]]]". iFrame.
      rewrite big_sepM_kmap_intro big_opS_set_map -big_sepM_dom.
      iApply (big_sepM_impl with "[$]"). iIntros "!>" (???) "$".
  Qed.

  Lemma heapUR_dom_excl p d1 d2 :
    heapUR_dom p (DfracOwn 1) d1 -∗ heapUR_dom p (DfracOwn 1) d2 -∗ False.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op. move => [_ /(gmap_view_frag_op_valid _ _ _)[??]].
    done.
  Qed.

  Lemma heapUR_ptsto_excl l v1 v2 :
    heapUR_ptsto l (DfracOwn 1) v1 -∗ heapUR_ptsto l (DfracOwn 1) v2 -∗ False.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op. move => [/(gmap_view_frag_op_valid _ _ _)[??] _].
    done.
  Qed.

  Lemma heapUR_block_excl p d1 d2 :
    heapUR_block p (DfracOwn 1) d1 -∗ heapUR_block p (DfracOwn 1) d2 -∗ False.
  Proof. iIntros "[??] [??]". iDestruct (heapUR_dom_excl with "[$] [$]") as %[]. Qed.

  Lemma heapUR_alloc h l n :
    heap_is_fresh h l →
    heapUR_inv h ==∗
    heapUR_inv (heap_alloc h l n) ∗
    heapUR_block l.1 (DfracOwn 1) (zero_block n).
  Proof.
    iIntros ([Hl [? ?]]) "[Hh Hd]".
    iMod (heapUR_ptsto_auth_alloc_big with "Hh") as "[Hh $]". {
      apply map_disjoint_spec => ??? /lookup_kmap_Some[?[->?]] /lookup_heap_Some_elem_of_h_provs. done. }
    iMod (heapUR_dom_auth_alloc with "Hd") as "[Hd $]".
    { apply eq_None_ne_Some => ?. rewrite lookup_set_to_map; naive_solver. }
    iModIntro. iFrame. iApply (heapUR_dom_auth_ext with "Hd").
    apply map_eq => p. apply option_eq => ?.
    rewrite lookup_insert_Some. rewrite !lookup_set_to_map //=.
    destruct (decide (l.1 = p)); split => ?; destruct!; split!; try set_solver.
    all: by rewrite ?h_block_heap_alloc // ?h_block_heap_alloc_ne.
  Qed.

  Lemma heapUR_alloc_block h p b:
    p ∉ h_provs h →
    heapUR_inv h ==∗
    heapUR_inv (heap_merge (heap_from_blocks {[p := b]}) h) ∗
    heapUR_block p (DfracOwn 1) b.
  Proof.
    iIntros (?) "[Hh Hd]".
    iMod (heapUR_ptsto_auth_alloc_big with "Hh") as "[Hh $]". {
      apply map_disjoint_spec => ??? /lookup_kmap_Some[?[->?]] /lookup_heap_Some_elem_of_h_provs. done. }
    iMod (heapUR_dom_auth_alloc with "Hd") as "[Hd $]".
    { apply eq_None_ne_Some => ?. rewrite lookup_set_to_map; naive_solver. }
    iModIntro. iSplitL "Hh".
    - iApply (heapUR_ptsto_auth_ext with "Hh") => /=. f_equal.
      apply map_eq => -[??]. apply option_eq => ?. rewrite lookup_kmap_Some lookup_gmap_uncurry bind_Some.
      setoid_rewrite lookup_singleton_Some. naive_solver.
    - iApply (heapUR_dom_auth_ext with "Hd").
      apply map_eq => p2. apply option_eq => ?.
      rewrite lookup_insert_Some. rewrite !lookup_set_to_map //=.
      destruct (decide (p = p2)); split => ?; destruct!; split!; try set_solver.
      all: by rewrite ?h_block_heap_merge_block // ?h_block_heap_merge_block_ne.
  Qed.

  Lemma heapUR_alloc_blocks h bs :
    dom bs ## h_provs h →
    heapUR_inv h ==∗
    heapUR_inv (heap_merge (heap_from_blocks bs) h) ∗
    [∗ map] p↦b∈ bs, heapUR_block p (DfracOwn 1) b.
  Proof.
    iIntros (Hbs) "Hinv".
    iInduction bs as [|???] "IH" using map_ind forall (h Hbs). {
      iModIntro. rewrite heap_from_blocks_empty left_id_L. by iFrame.
    }
    rewrite heap_from_blocks_insert // -assoc_L.
    iMod ("IH" with "[%] [$]") as "[??]"; [set_solver|].
    iMod (heapUR_alloc_block with "[$]") as "[$ ?]".
    { simpl. apply not_elem_of_union. split; [|set_solver]. by apply not_elem_of_dom. }
    iModIntro. iApply big_sepM_insert; [done|]. iFrame.
  Qed.

  Lemma heapUR_lookup h l dq v:
    heapUR_inv h -∗
    heapUR_ptsto l dq v -∗
    ⌜h_heap h !! l = Some v⌝.
  Proof.
    iIntros "[Hh Hd] Hl".
    iDestruct (heapUR_ptsto_auth_lookup with "[$] [$]") as "$".
  Qed.

  Lemma heapUR_lookup_dom h p dq d:
    heapUR_inv h -∗
    heapUR_dom p dq d -∗
    ⌜dom (h_block h p) = d⌝.
  Proof.
    iIntros "[Hh Hd] Hdom".
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? [= ? Hdom]]]%lookup_set_to_map => //.
    naive_solver.
  Qed.

  Lemma heapUR_lookup_dom_prov h p dq d:
    heapUR_inv h -∗
    heapUR_dom p dq d -∗
    ⌜p ∈ h_provs h⌝.
  Proof.
    iIntros "[??] ?".
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %Hs%lookup_set_to_map => //.
    iPureIntro. naive_solver.
  Qed.

  Lemma heapUR_lookup_block h p dq b:
    heapUR_inv h -∗
    heapUR_block p dq b -∗
    ⌜h_block h p = b⌝.
  Proof.
    iIntros "[Hh Hd] [Hdom Hpts]".
    iDestruct (heapUR_ptsto_auth_lookup_big with "[$] [$]") as %?.
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? [= ? Hdom]]]%lookup_set_to_map => //.
    simplify_eq/=. iPureIntro. apply map_eq => o.
    destruct (b !! o) eqn:Hb.
    - rewrite h_block_lookup. apply: lookup_weaken; [|done].
      apply lookup_kmap_Some; [apply _|naive_solver].
    - apply not_elem_of_dom_1. rewrite Hdom. by apply not_elem_of_dom.
  Qed.

  Lemma heapUR_lookup_block1 h dq b l v:
    h_heap h !! l = Some v →
    heapUR_inv h -∗
    heapUR_block l.1 dq b -∗
    ⌜b !! l.2 = Some v⌝.
  Proof.
    iIntros (?) "Hinv Hblock".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iPureIntro. by rewrite h_block_lookup -surjective_pairing.
  Qed.

  Lemma heapUR_lookup_block_prov h p dq b:
    heapUR_inv h -∗
    heapUR_block p dq b -∗
    ⌜p ∈ h_provs h⌝.
  Proof. iIntros "?[??]". iApply (heapUR_lookup_dom_prov with "[$] [$]"). Qed.

  Lemma heapUR_update v' h l v:
    heapUR_inv h -∗
    heapUR_ptsto l (DfracOwn 1) v ==∗
    heapUR_inv (heap_update h l v') ∗ heapUR_ptsto l (DfracOwn 1) v'.
  Proof.
    iIntros "[Hh Hd] Hl".
    iDestruct (heapUR_ptsto_auth_lookup with "[$] [$]") as %?.
    iMod (heapUR_ptsto_auth_update with "[$]") as "[Hh $]". iModIntro.
    iSplitL "Hh" => /=.
    - iApply (heapUR_ptsto_auth_ext with "[$]"). apply partial_alter_ext.
      move => ??. by simplify_map_eq.
    - iApply (heapUR_dom_auth_ext with "[$]").
      apply map_eq => ?. apply option_eq => ?.
      rewrite !lookup_set_to_map //=. f_equiv => ?. do 3 f_equiv. apply set_eq => ?.
      by rewrite !elem_of_dom !h_block_lookup/= lookup_alter_is_Some.
  Qed.

  Lemma heapUR_update_block v' h l b:
    heap_alive h l →
    heapUR_inv h -∗
    heapUR_block l.1 (DfracOwn 1) b ==∗
    heapUR_inv (heap_update h l v') ∗ heapUR_block l.1 (DfracOwn 1) (<[l.2:=v']> b).
  Proof.
    iIntros ([??]) "? [Hdom Hl]".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iDestruct (big_sepM_insert_acc with "Hl") as "[? Hl]". {
      apply lookup_kmap_Some; [apply _|]. split!. by erewrite <-h_block_lookup2.
    }
    rewrite - {1 2}surjective_pairing.
    iMod (heapUR_update with "[$] [$]") as "[$ ?]". iModIntro.
    iSplitL "Hdom".
    - rewrite dom_insert_lookup_L //. eexists _. by rewrite -h_block_lookup2.
    - rewrite kmap_insert. by iApply "Hl".
  Qed.

  Lemma heapUR_free l h b:
    heapUR_inv h -∗
    heapUR_block l.1 (DfracOwn 1) b ==∗
    heapUR_inv (heap_free h l) ∗ heapUR_block l.1 (DfracOwn 1) ∅.
  Proof.
    iIntros "Hinv Hb".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iDestruct (heapUR_lookup_block_prov with "[$] [$]") as %?.
    iDestruct "Hinv" as "[Hh Hd]". iDestruct "Hb" as "[Hdom Hpts]".
    iMod (heapUR_ptsto_auth_free_big with "Hh Hpts") as "Hh".
    iMod (heapUR_dom_auth_update with "[$]") as "[? $]". iModIntro.
    iSplitL; [|done]. iSplitL "Hh".
    - iApply (heapUR_ptsto_auth_ext with "[$]") => /=.
      apply map_eq => ?. apply option_eq => ?.
      rewrite lookup_difference_Some map_lookup_filter_Some lookup_kmap_None.
      split; [|naive_solver].
      move => [Hh Hi]. split; [done|]. move => Heq.
      rewrite h_block_lookup2 Heq Hi // in Hh. by rewrite -Heq -surjective_pairing.
    - iApply (heapUR_dom_auth_ext with "[$]").
      rewrite h_provs_heap_free //.
      apply map_eq => p. apply option_eq => ?.
      rewrite lookup_insert_Some !lookup_set_to_map //=.
      destruct (decide (l.1 = p)); split => ?; destruct!; split!.
      + by rewrite h_block_free.
      + by rewrite h_block_free.
      + by rewrite h_block_free_ne.
      + by rewrite h_block_free_ne.
  Qed.

  Lemma heapUR_free_uninit l h b `{!BiAffine PROP}:
    heapUR_inv h -∗
    heapUR_uninit_block l.1 (DfracOwn 1) b ==∗
    heapUR_inv (heap_free h l) ∗ heapUR_block l.1 (DfracOwn 1) ∅.
  Proof.
    iIntros "Hinv Hb".
    iDestruct (heapUR_uninit_block_eq with "Hb") as (? ->) "?".
    by iApply (heapUR_free with "[$]").
  Qed.

  (** init *)
  Definition heapUR_init : heapUR :=
    (gmap_view_auth (DfracOwn 1) ∅, gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)).

  Lemma heapUR_init_valid :
    ✓ heapUR_init.
  Proof. split; by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1)). Qed.

  Lemma heapUR_init_own :
    bi_own Own heapUR_init ⊢ heapUR_inv ∅.
  Proof.
    have ? := bi_own_proper _ _ Own. rewrite /heapUR_init pair_split bi_own_op.
    iIntros "[$ Ho]" => /=. iApply (heapUR_dom_auth_ext with "Ho").
    apply map_eq => ?. apply option_eq => ?. by rewrite lookup_set_to_map.
  Qed.

End heapUR.

Global Typeclasses Opaque heapUR_ptsto heapUR_dom heapUR_inv.
Global Opaque heapUR_ptsto heapUR_dom heapUR_inv.
Global Arguments heapUR_block : simpl never.
