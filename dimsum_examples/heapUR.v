From iris.algebra Require Export dfrac.
From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core.iris Require Export biown.
From dimsum.core.iris Require Import weak_embed.
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
    heapUR_dom_auth (dom <$> h_blocks h).
End heapUR.

Notation "l ↦[ O ] dq v" := (heapUR_ptsto O l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦[ O ] dq  v") : bi_scope.
Notation "p ↦∗[ O ] dq b" := (heapUR_block O p dq b)
  (at level 20, dq custom dfrac at level 1, format "p  ↦∗[ O ] dq  b") : bi_scope.
Notation "p ⤚[ O ] dq d" := (heapUR_dom O p dq d)
  (at level 20, dq custom dfrac at level 1, format "p  ⤚[ O ] dq  d") : bi_scope.

Section heapUR.
  Context {PROP : bi} `{!BiBUpd PROP} (O : BiOwn PROP heapUR).

  (** _auth lemmas are internal lemmas *)
  Lemma heapUR_ptsto_auth_ext h h':
    h = h' →
    heapUR_ptsto_auth O h ⊢ heapUR_ptsto_auth O h'.
  Proof. by move => ->. Qed.

  Lemma heapUR_dom_auth_ext d d':
    d = d' →
    heapUR_dom_auth O d ⊢ heapUR_dom_auth O d'.
  Proof. by move => ->. Qed.


  Lemma heapUR_ptsto_auth_alloc h l v :
    h !! l = None →
    heapUR_ptsto_auth O h ⊢ |==>
    heapUR_ptsto_auth O (<[l:=v]>h) ∗ l ↦[O] v.
  Proof.
    move => ?. rewrite -bi_own_op. apply bi_own_bupd.
    apply prod_update; [|done] => /=. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
  Qed.

  Lemma heapUR_ptsto_auth_alloc_big h' h :
    h' ##ₘ h →
    heapUR_ptsto_auth O h ==∗
    heapUR_ptsto_auth O (h' ∪ h) ∗ [∗ map] l↦v∈h', l ↦[O] v.
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
    heapUR_ptsto_auth O h -∗
    l ↦[O]{dq} v -∗
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
    heapUR_ptsto_auth O h -∗
    ([∗ map] l↦v∈h', l ↦[O]{dq} v) -∗
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
    heapUR_ptsto_auth O h ∗ l ↦[O] v ⊢ |==>
    heapUR_ptsto_auth O (<[l:=v']>h) ∗ l ↦[O] v'.
  Proof.
    rewrite -!bi_own_op. apply bi_own_bupd. rewrite -!pair_op.
    apply prod_update; [|done] => /=. rewrite fmap_insert.
    by apply gmap_view_replace.
  Qed.

  Lemma heapUR_ptsto_auth_free h l v :
    heapUR_ptsto_auth O h ∗ l ↦[O] v ⊢ |==>
    heapUR_ptsto_auth O (delete l h).
  Proof.
    rewrite -!bi_own_op. rewrite -!pair_op. apply bi_own_bupd.
    apply prod_update; [|done] => /=. rewrite fmap_delete.
    by apply gmap_view_delete.
  Qed.

  Lemma heapUR_ptsto_auth_free_big h' h :
    heapUR_ptsto_auth O h -∗
    ([∗ map] l↦v∈h', l ↦[O] v) ==∗
    heapUR_ptsto_auth O (h ∖ h').
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
    heapUR_dom_auth O d ⊢ |==>
    heapUR_dom_auth O (<[p:=s]>d) ∗ p ⤚[O] s.
  Proof.
    move => ?. rewrite -bi_own_op. rewrite -pair_op. apply bi_own_bupd.
    apply prod_update; [done|] => /=. rewrite fmap_insert.
    apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
  Qed.

  Lemma heapUR_dom_auth_lookup d p dq s :
    heapUR_dom_auth O d -∗
    p ⤚[O]{dq} s -∗
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
    heapUR_dom_auth O d ∗ p ⤚[O] s ⊢ |==>
    heapUR_dom_auth O (<[p:=s']>d) ∗ p ⤚[O] s'.
  Proof.
    rewrite -!bi_own_op. rewrite -!pair_op. apply bi_own_bupd.
    apply prod_update; [done|] => /=. rewrite fmap_insert.
    by apply gmap_view_replace.
  Qed.

  Lemma heapUR_dom_auth_free d p s :
    heapUR_dom_auth O d ∗ p ⤚[O] s ⊢ |==>
    heapUR_dom_auth O (delete p d).
  Proof.
    rewrite -!bi_own_op. rewrite -!pair_op. apply bi_own_bupd.
    apply prod_update; [done|] => /=. rewrite fmap_delete.
    by apply gmap_view_delete.
  Qed.

  (** clients should not unfold _inv and only use the lemmas starting from here *)
  Lemma heapUR_uninit_block_eq p dq d `{!BiAffine PROP}:
    heapUR_uninit_block O p dq d ⊣⊢ ∃ b, ⌜d = dom b⌝ ∗ p ↦∗[O]{dq} b.
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
    p ⤚[O] d1 -∗ p ⤚[O] d2 -∗ False.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op. move => [_ /(gmap_view_frag_op_valid _ _ _)[??]].
    done.
  Qed.

  Lemma heapUR_ptsto_excl l v1 v2 :
    l ↦[O] v1 -∗ l ↦[O] v2 -∗ False.
  Proof.
    apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
    rewrite -bi_own_op. etrans; [apply bi_own_valid|]. iPureIntro.
    rewrite -pair_op. move => [/(gmap_view_frag_op_valid _ _ _)[??] _].
    done.
  Qed.

  Lemma heapUR_block_excl p d1 d2 :
    p ↦∗[O] d1 -∗ p ↦∗[O] d2 -∗ False.
  Proof. iIntros "[??] [??]". iDestruct (heapUR_dom_excl with "[$] [$]") as %[]. Qed.

  Lemma heapUR_alloc h l n :
    heap_is_fresh h l →
    heapUR_inv O h ==∗
    heapUR_inv O (heap_alloc h l n) ∗
    l.1 ↦∗[O] zero_block n.
  Proof.
    iIntros ([Hl [? ?]]) "[Hh Hd]".
    iMod (heapUR_ptsto_auth_alloc_big with "Hh") as "[Hh $]". {
      apply map_disjoint_spec => ??? /lookup_kmap_Some[?[->?]] /lookup_heap_Some_elem_of_h_provs. done. }
    iMod (heapUR_dom_auth_alloc with "Hd") as "[Hd $]".
    { rewrite lookup_fmap fmap_None. by apply h_blocks_lookup_None. }
    iModIntro. iFrame. iApply (heapUR_dom_auth_ext with "Hd").
    apply map_eq => p. apply option_eq => ?.
    rewrite lookup_insert_Some !lookup_fmap_Some.
    setoid_rewrite h_blocks_heap_alloc => //.
    setoid_rewrite lookup_insert_Some. naive_solver.
  Qed.

  Lemma heapUR_alloc_list h h' xs ls :
    heap_alloc_list xs ls h h' →
    heapUR_inv O h ==∗
    heapUR_inv O h' ∗
    [∗ list] l;x∈ls;xs, l.1 ↦∗[O] zero_block x.
  Proof.
    iIntros (Ha) "Hinv".
    iInduction xs as [|x xs] "IH" forall (ls h Ha); destruct!/=. 1: by iFrame.
    iMod (heapUR_alloc with "Hinv") as "[? $]"; [done|].
    iApply ("IH" with "[//] [$]").
  Qed.

  Lemma heapUR_alloc_loc h l v s Hp:
    h_heap h !! l = None →
    heapUR_inv O h -∗
    l.1 ⤚[O] s ==∗
    heapUR_inv O (heap_alloc_loc h l v Hp) ∗
    l.1 ⤚[O] ({[l.2]} ∪ s) ∗
    l ↦[O] v.
  Proof.
    iIntros (Hl) "[Hh Hd] ?".
    iMod (heapUR_ptsto_auth_alloc with "Hh") as "[Hh $]"; [done|].
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? Hb]]%lookup_fmap_Some.
    iMod (heapUR_dom_auth_update with "[$]") as "[Hd $]".
    iModIntro. iFrame. iApply (heapUR_dom_auth_ext with "Hd").
    apply map_eq => p. apply option_eq => ?.
    rewrite lookup_insert_Some !lookup_fmap_Some.
    setoid_rewrite h_blocks_heap_alloc_loc => //.
    setoid_rewrite lookup_insert_Some.
    split => ?; destruct!; split!; by rewrite dom_insert_L.
  Qed.

  Lemma heapUR_alloc_block h p b:
    p ∉ h_provs h →
    heapUR_inv O h ==∗
    heapUR_inv O (heap_merge (heap_from_blocks {[p := b]}) h) ∗ p ↦∗[O] b.
  Proof.
    iIntros (?) "[Hh Hd]".
    iMod (heapUR_ptsto_auth_alloc_big with "Hh") as "[Hh $]". {
      apply map_disjoint_spec => ??? /lookup_kmap_Some[?[->?]] /lookup_heap_Some_elem_of_h_provs. done. }
    iMod (heapUR_dom_auth_alloc with "Hd") as "[Hd $]".
    { rewrite lookup_fmap fmap_None. by apply h_blocks_lookup_None. }
    iModIntro. iSplitL "Hh".
    - iApply (heapUR_ptsto_auth_ext with "Hh") => /=. f_equal.
      apply map_eq => -[??]. apply option_eq => ?. rewrite lookup_kmap_Some lookup_gmap_uncurry bind_Some.
      setoid_rewrite lookup_singleton_Some. naive_solver.
    - iApply (heapUR_dom_auth_ext with "Hd").
      apply map_eq => p2. apply option_eq => ?.
      rewrite lookup_insert_Some !lookup_fmap_Some.
      setoid_rewrite h_blocks_heap_merge_block => //.
      setoid_rewrite lookup_insert_Some. naive_solver.
  Qed.

  Lemma heapUR_alloc_blocks bs h :
    dom bs ## h_provs h →
    heapUR_inv O h ==∗
    heapUR_inv O (heap_merge (heap_from_blocks bs) h) ∗
    [∗ map] p↦b∈ bs, p ↦∗[O] b.
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
    heapUR_inv O h -∗
    l ↦[O]{dq} v -∗
    ⌜h_heap h !! l = Some v⌝.
  Proof.
    iIntros "[Hh Hd] Hl".
    iDestruct (heapUR_ptsto_auth_lookup with "[$] [$]") as "$".
  Qed.

  Lemma heapUR_lookup_dom h p dq d:
    heapUR_inv O h -∗
    p ⤚[O]{dq} d -∗
    ⌜dom (h_block h p) = d⌝.
  Proof.
    iIntros "[Hh Hd] Hdom".
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? [??]%h_blocks_lookup_Some]]%lookup_fmap_Some.
    naive_solver.
  Qed.

  Lemma heapUR_lookup_dom_prov h p dq d:
    heapUR_inv O h -∗
    p ⤚[O]{dq} d -∗
    ⌜p ∈ h_provs h⌝.
  Proof.
    iIntros "[??] ?".
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? [??]%h_blocks_lookup_Some]]%lookup_fmap_Some.
    iPureIntro. naive_solver.
  Qed.

  Lemma heapUR_lookup_block h p dq b:
    heapUR_inv O h -∗
    p ↦∗[O]{dq} b -∗
    ⌜h_block h p = b⌝.
  Proof.
    iIntros "[Hh Hd] [Hdom Hpts]".
    iDestruct (heapUR_ptsto_auth_lookup_big with "[$] [$]") as %?.
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[Hdom [? ?]%h_blocks_lookup_Some]]%lookup_fmap_Some.
    simplify_eq/=. iPureIntro. apply map_eq => o.
    destruct (b !! o) eqn:Hb.
    - rewrite h_block_lookup. apply: lookup_weaken; [|done].
      apply lookup_kmap_Some; [apply _|naive_solver].
    - apply not_elem_of_dom_1. rewrite Hdom. by apply not_elem_of_dom.
  Qed.

  Lemma heapUR_lookup_block1 h dq b l v:
    h_heap h !! l = Some v →
    heapUR_inv O h -∗
    l.1 ↦∗[O]{dq} b -∗
    ⌜b !! l.2 = Some v⌝.
  Proof.
    iIntros (?) "Hinv Hblock".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iPureIntro. by rewrite h_block_lookup -surjective_pairing.
  Qed.

  Lemma heapUR_lookup_block_prov h p dq b:
    heapUR_inv O h -∗
    p ↦∗[O]{dq} b -∗
    ⌜p ∈ h_provs h⌝.
  Proof. iIntros "?[??]". iApply (heapUR_lookup_dom_prov with "[$] [$]"). Qed.

  Lemma heapUR_lookup_block_big h m dq `{!BiPureForall PROP}:
    heapUR_inv O h -∗
    ([∗ map] p↦b∈m, p ↦∗[O]{dq} b) -∗
    ⌜m ⊆ h_blocks h⌝.
  Proof.
    iIntros "? Hm". rewrite map_subseteq_spec.
    iIntros (???). iDestruct (big_sepM_lookup_acc with "[$]") as "[??]"; [done|].
    iDestruct (heapUR_lookup_block_prov with "[$] [$]") as %?.
    iDestruct (heapUR_lookup_block with "[$] [$]") as %?. subst.
    iPureIntro. by apply h_blocks_lookup_Some.
  Qed.

  Lemma heapUR_update v' h l v:
    heapUR_inv O h -∗
    l ↦[O] v ==∗
    heapUR_inv O (heap_update h l v') ∗ l ↦[O] v'.
  Proof.
    iIntros "[Hh Hd] Hl".
    iDestruct (heapUR_ptsto_auth_lookup with "[$] [$]") as %?.
    iMod (heapUR_ptsto_auth_update with "[$]") as "[Hh $]". iModIntro.
    iSplitL "Hh" => /=.
    - iApply (heapUR_ptsto_auth_ext with "[$]"). apply partial_alter_ext.
      move => ??. by simplify_map_eq.
    - iApply (heapUR_dom_auth_ext with "[$]").
      rewrite h_blocks_heap_update.
      apply map_eq => p. apply option_eq => ?.
      rewrite !lookup_fmap_Some.
      setoid_rewrite lookup_alter_Some.
      destruct (decide (p = l.1)); split => ?; destruct!; split!; by rewrite dom_alter_L.
  Qed.

  Lemma heapUR_update_in_block v' h l b:
    heap_alive h l →
    heapUR_inv O h -∗
    l.1 ↦∗[O] b ==∗
    heapUR_inv O (heap_update h l v') ∗ l.1 ↦∗[O] <[l.2:=v']> b.
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

  Lemma heapUR_update_block b' h p b:
    heapUR_inv O h -∗
    p ↦∗[O] b ==∗
    heapUR_inv O (heap_update_block h p b') ∗ p ↦∗[O] b'.
  Proof.
    iIntros "Hinv Hb".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iDestruct "Hinv" as "[Hh Hd]". iDestruct "Hb" as "[Hdom Hpts]".
    iMod (heapUR_ptsto_auth_free_big with "Hh Hpts") as "Hh".
    rewrite h_heap_difference_block.
    iMod (heapUR_dom_auth_update with "[$]") as "[Hdom $]".
    iMod (heapUR_ptsto_auth_alloc_big with "Hh") as "[Hh $]". {
      apply map_disjoint_spec => ???/lookup_kmap_Some[?[??]].
      move => /map_lookup_filter_Some. naive_solver.
    }
    iModIntro. iFrame.
    by rewrite h_blocks_heap_update_block fmap_insert.
  Qed.

  Lemma heapUR_free l h b:
    heapUR_inv O h -∗
    l.1 ↦∗[O] b ==∗
    heapUR_inv O (heap_free h l) ∗ l.1 ↦∗[O] ∅.
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
      rewrite h_blocks_free -fmap_insert alter_eq_insert_const //.
      by apply h_blocks_lookup_is_Some.
  Qed.

  Lemma heapUR_free_uninit l h b `{!BiAffine PROP}:
    heapUR_inv O h -∗
    heapUR_uninit_block O l.1 (DfracOwn 1) b ==∗
    heapUR_inv O (heap_free h l) ∗ l.1 ↦∗[O] ∅.
  Proof.
    iIntros "Hinv Hb".
    iDestruct (heapUR_uninit_block_eq with "Hb") as (? ->) "?".
    by iApply (heapUR_free with "[$]").
  Qed.

  Lemma heapUR_free_list h ls szs `{!BiAffine PROP} :
    Forall (λ l : loc, is_ProvBlock l.1 ∧ l.2 = 0) ls →
    heapUR_inv O h -∗
    ([∗ list] l;sz ∈ ls;szs, heapUR_uninit_block O l.1 (DfracOwn 1) (dom (zero_block sz))) ==∗
    ∃ h', ⌜heap_free_list (zip ls szs) h h'⌝ ∗ heapUR_inv O h'.
  Proof.
    iIntros (Hblock) "Hinv Hls".
    iInduction szs as [|sz szs] "IH" forall (h ls Hblock).
    { iModIntro. iDestruct (big_sepL2_nil_inv_r with "Hls") as %?. simplify_eq/=. iSplit!. }
    iDestruct (big_sepL2_cons_inv_r with "Hls") as (???) "[Hb ?]". simplify_eq/=.
    move: Hblock => /Forall_cons[[??]?].
    iDestruct (heapUR_uninit_block_eq with "Hb") as (? ?) "?".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iMod (heapUR_free with "[$] [$]") as "[??]".
    iMod ("IH" with "[//] [$] [$]") as (??) "?".
    iModIntro. iSplit! => //. by apply heap_range_dom_h_block.
  Qed.


  Lemma heapUR_remove_prov p h b:
    heapUR_inv O h -∗
    p ↦∗[O] b ==∗
    heapUR_inv O (heap_remove_prov h p).
  Proof.
    iIntros "Hinv Hb".
    iDestruct (heapUR_lookup_block with "[$] [$]") as %<-.
    iDestruct (heapUR_lookup_block_prov with "[$] [$]") as %?.
    iDestruct "Hinv" as "[Hh Hd]". iDestruct "Hb" as "[Hdom Hpts]".
    iMod (heapUR_ptsto_auth_free_big with "Hh Hpts") as "Hh".
    iMod (heapUR_dom_auth_free with "[$]") as "?". iModIntro.
    iSplitL "Hh".
    - iApply (heapUR_ptsto_auth_ext with "[$]") => /=. by rewrite h_heap_difference_block.
    - iApply (heapUR_dom_auth_ext with "[$]").
      apply map_eq => p'. apply option_eq => ?.
      rewrite lookup_delete_Some !lookup_fmap_Some.
      setoid_rewrite h_blocks_heap_remove_prov.
      setoid_rewrite lookup_delete_Some.
      naive_solver.
  Qed.

  Lemma heapUR_remove_loc h l v s:
    heapUR_inv O h -∗
    l ↦[O] v -∗
    l.1 ⤚[O] s ==∗
    heapUR_inv O (heap_remove_loc h l) ∗
    l.1 ⤚[O] (s ∖ {[l.2]}).
  Proof.
    iIntros "[Hh Hd] ? ?".
    iMod (heapUR_ptsto_auth_free with "[$]") as "Hh".
    iDestruct (heapUR_dom_auth_lookup with "[$] [$]") as %[?[? ?]]%lookup_fmap_Some.
    iMod (heapUR_dom_auth_update with "[$]") as "[Hd $]".
    iModIntro. iFrame. iApply (heapUR_dom_auth_ext with "Hd").
    apply map_eq => p. apply option_eq => ?.
    rewrite lookup_insert_Some !lookup_fmap_Some.
    setoid_rewrite h_blocks_heap_remove_loc => //.
    setoid_rewrite lookup_insert_Some.
    split => ?; destruct!; split!; by rewrite dom_delete_L.
  Qed.

  (** init *)
  Definition heapUR_init : heapUR :=
    (gmap_view_auth (DfracOwn 1) ∅, gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)).

  Lemma heapUR_init_valid :
    ✓ heapUR_init.
  Proof. split; by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1)). Qed.

  Lemma heapUR_init_own :
    bi_own O heapUR_init ⊢ heapUR_inv O ∅.
  Proof.
    have ? := bi_own_proper _ _ O. rewrite /heapUR_init pair_split bi_own_op.
    iIntros "[$ Ho]" => /=. iApply (heapUR_dom_auth_ext with "Ho").
    apply map_eq => ?. apply option_eq => ?. by rewrite lookup_fmap_Some.
  Qed.

End heapUR.

Global Typeclasses Opaque heapUR_ptsto heapUR_dom heapUR_inv.
Global Opaque heapUR_ptsto heapUR_dom heapUR_inv.
Global Arguments heapUR_block : simpl never.

(** * Trader for HeapUR *)
(* TODO: Better name? Trade Post? Warp Gate? *)

Section trader.
  Context {PROP1 PROP2 PROP : bi} `{!BiBUpd PROP1} `{!BiBUpd PROP2}.
  Context (W1 : BiWeakEmbed PROP1 PROP) (W2 : BiWeakEmbed PROP2 PROP).
  Context (O1 : BiOwn PROP1 heapUR) (O2 : BiOwn PROP2 heapUR).

  Definition heapUR_ptsto_trader (l : loc) (v : val) : PROP :=
    ⌈l ↦[O1] v @ W1⌉ ∨ ⌈l ↦[O2] v @ W2⌉.
  Definition heapUR_dom_trader (p : prov) (d : gset Z) : PROP :=
    ⌈p ⤚[O1] d @ W1⌉ ∨ ⌈p ⤚[O2] d @ W2⌉.
  Definition heapUR_block_trader (p : prov) (b : gmap Z val) : PROP :=
    heapUR_dom_trader p (dom b) ∗
    ([∗ map] l↦v∈kmap (pair p) b, heapUR_ptsto_trader l v).
  Definition heapUR_heap_trader (h : heap_state) : PROP :=
    ⌈heapUR_inv O1 h @ W1⌉ ∗
    ([∗ map] p↦b∈h_blocks h, heapUR_block_trader p b).

  Definition heapUR_trader : PROP := ∃ h, heapUR_heap_trader h.

  Context `{!BiBUpd PROP} `{!BiAffine PROP} `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.

  Lemma heapUR_block_trader_or p b :
    ⌈p ↦∗[O1] b @ W1⌉ ∨ ⌈p ↦∗[O2] b @ W2⌉ ⊢ heapUR_block_trader p b.
  Proof using BiAffine0.
    rewrite /heapUR_block_trader.
    iIntros "[[Hd ?]|[Hd ?]]"; (iSplitL "Hd"; [(by iLeft) || by iRight|]).
    all: rewrite weak_embed_big_sepM.
    all: iApply (big_sepM_impl with "[$]").
    all: iIntros "!>" (???) "?".
    - by iLeft.
    - by iRight.
  Qed.

  Global Instance from_or_heapUR_block_trader p b :
    FromOr (heapUR_block_trader p b) ⌈p ↦∗[O1] b @ W1⌉ ⌈p ↦∗[O2] b @ W2⌉.
  Proof using BiAffine0. by rewrite /FromOr heapUR_block_trader_or. Qed.

  Lemma heapUR_ptsto_trader_in_1 h2 l v :
    h_heap h2 !! l = None →
    ⌈heapUR_inv O2 h2 @ W2⌉ -∗
    heapUR_ptsto_trader l v -∗
    ⌈l ↦[O1] v @ W1⌉ ∗ ⌈heapUR_inv O2 h2 @ W2⌉.
  Proof using BiAffine0.
    iIntros (?) "? [$|?]" => //.
    iDestruct (heapUR_lookup O2 with "[$] [$]") as %?.
    naive_solver.
  Qed.

  Lemma heapUR_dom_trader_in_1 h2 p d :
    p ∉ h_provs h2 ∨ d ≠ dom (h_block h2 p) →
    ⌈heapUR_inv O2 h2 @ W2⌉ -∗
    heapUR_dom_trader p d -∗
    ⌈p ⤚[O1] d @ W1⌉ ∗ ⌈heapUR_inv O2 h2 @ W2⌉.
  Proof using BiAffine0.
    iIntros (?) "? [$|?]" => //.
    iDestruct (heapUR_lookup_dom O2 with "[$] [$]") as %?.
    iDestruct (heapUR_lookup_dom_prov O2 with "[$] [$]") as %?.
    naive_solver.
  Qed.

  Lemma heapUR_block_trader_in_1 h2 p bs :
    p ∉ h_provs h2 →
    ⌈heapUR_inv O2 h2 @ W2⌉ -∗
    heapUR_block_trader p bs -∗
    ⌈p ↦∗[O1] bs @ W1⌉ ∗ ⌈heapUR_inv O2 h2 @ W2⌉.
  Proof using BiAffine0.
    iIntros (?) "? [??]".
    iDestruct (heapUR_dom_trader_in_1 with "[$] [$]") as "[$ ?]". 1: naive_solver.
    rewrite weak_embed_big_sepM.
    iApply (big_sepM_impl_frame with "[$]"). 2: done.
    iIntros "!>" (?? Hk) "??". iDestruct (heapUR_ptsto_trader_in_1 with "[$] [$]") as "[$ $]".
    apply not_elem_of_h_provs_lookup_heap. move: Hk => /lookup_kmap_Some. naive_solver.
  Qed.


  Lemma heapUR_heap_trader_equalize h1 h2 :
    heapUR_heap_trader h1 -∗
    ⌈heapUR_inv O2 h2 @ W2⌉ ==∗⌈W1⌉
    heapUR_heap_trader h2 ∗
    ⌈heapUR_inv O2 h2 @ W2⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "(Hinv1 & Hb) Hinv2".
    have [bs Hbs] : ∃ bs, bs = h_blocks h1 by naive_solver.
    iInduction bs as [p bs ? Hp1 Hp2|p bs ? Hp1 Hp2|p bs1 bs2 ? Hp1 Hp2|] "IH" using (map_equalize_ind (h_blocks h2)) forall (h1 Hbs); subst.
    - move: Hp1 => /h_blocks_lookup_None ?.
      iMod (heapUR_alloc_block O1 _ p bs with "Hinv1") as "[? Hbs]"; [done|].
      iApply ("IH" with "[%] [$] [Hb Hbs] [$]").
      + rewrite h_blocks_heap_merge /= ?dom_singleton_L; [|set_solver].
        by rewrite h_blocks_heap_from_blocks insert_union_singleton_l.
      + rewrite h_blocks_heap_merge /= ?dom_singleton_L; [|set_solver].
        rewrite h_blocks_heap_from_blocks -insert_union_singleton_l.
        iApply (big_sepM_insert_2 with "[Hbs] Hb"). by iLeft.
    - iDestruct (big_sepM_delete with "Hb") as "[? Hm]"; [done|].
      iDestruct (heapUR_block_trader_in_1 with "[$] [$]") as "[? ?]".
      { by apply h_blocks_lookup_None. }
      iMod (heapUR_remove_prov O1 with "[$] [$]").
      by iApply ("IH" with "[%] [$] [Hm] [$]"); rewrite h_blocks_heap_remove_prov.
    - iInduction bs1 as [o v ? Hb1 Hb2|o v ? Hb1 Hb2|o v1 v2|] "IH2" using (map_equalize_ind bs2) forall (h1 Hp1) "IH".
      + iDestruct (big_sepM_insert_acc with "Hb") as "[[Hd Hls] Hc]"; [done|].
        iDestruct (heapUR_dom_trader_in_1 with "[$] [$]") as "[??]". {
          right. move => Hd. move: Hp1 => /h_blocks_lookup_Some[??].
          move: Hp2 => /h_blocks_lookup_Some[??]. subst.
          move: Hb1 => /not_elem_of_dom. rewrite Hd => /not_elem_of_dom.
          naive_solver.
        }
        iDestruct (heapUR_lookup_dom_prov O1 with "Hinv1 [$]") as %Hp.
        iMod (heapUR_alloc_loc O1 _ (p, o) _ _ Hp with "[$] [$]") as "[? [Hp Hl]]" => /=.
        { rewrite -h_block_lookup. by move: Hp1 => /h_blocks_lookup_Some[? <-]. }
        erewrite <-dom_insert_L.
        iDestruct ("Hc" with "[$Hp Hl Hls]") as "Hb".
        { rewrite kmap_insert. iApply (big_sepM_insert_2 with "[Hl] [$]"). by iLeft. }
        iApply ("IH2" with "[%] [$] [Hb] [$]").
        * erewrite h_blocks_heap_alloc_loc => //=. by simplify_map_eq.
        * erewrite h_blocks_heap_alloc_loc => //=.
        * iIntros "!>" (? Heq). iApply "IH". iPureIntro. rewrite -Heq.
          erewrite h_blocks_heap_alloc_loc => //=. by rewrite insert_insert.
      + iDestruct (big_sepM_insert_acc with "Hb") as "[[Hd Hls] Hc]"; [done|].
        iDestruct (heapUR_dom_trader_in_1 with "[$] [$]") as "[??]". {
          right. move => Hd. move: Hp1 => /h_blocks_lookup_Some[??].
          move: Hp2 => /h_blocks_lookup_Some[??]. subst.
          move: Hb2 => /not_elem_of_dom. rewrite -Hd => /not_elem_of_dom.
          naive_solver.
        }
        iDestruct (big_sepM_delete with "Hls") as "[? Hls]".
        { apply/lookup_kmap_Some. naive_solver. }
        iDestruct (heapUR_ptsto_trader_in_1 with "[$] [$]") as "[??]".
        { rewrite -h_block_lookup. by move: Hp2 => /h_blocks_lookup_Some[? <-]. }
        iMod (heapUR_remove_loc O1 with "[$] [$] [$]") as "[? Hp]" => /=.
        erewrite <-dom_delete_L. rewrite -kmap_delete.
        iDestruct ("Hc" with "[$Hp $Hls]") as "Hb".
        iApply ("IH2" with "[%] [$] [Hb] [$]").
        * erewrite h_blocks_heap_remove_loc => //=. by simplify_map_eq.
        * erewrite h_blocks_heap_remove_loc => //=.
        * iIntros "!>" (? Heq). iApply "IH". iPureIntro. rewrite -Heq.
          erewrite h_blocks_heap_remove_loc => //=. by rewrite insert_insert.
      + iDestruct (big_sepM_insert_acc with "Hb") as "[[Hd Hls] Hc]"; [done|].
        iDestruct (big_sepM_insert_acc with "Hls") as "[Ht Hc2]".
        { apply/lookup_kmap_Some. naive_solver. }
        iDestruct "Ht" as "[Ht|Ht]".
        * iMod (heapUR_update O1 with "[$] [$]") as "[? Hl]".
          iDestruct ("Hc2" with "[Hl]") as "Hb"; [by iLeft|]. rewrite -kmap_insert.
          iDestruct ("Hc" with "[$Hb Hd]") as "Hb". { by rewrite dom_insert_lookup_L. }
          iApply ("IH2" with "[%] [$] [Hb] [$]").
          -- rewrite h_blocks_heap_update /= lookup_alter Hp1 /= alter_eq_insert_const //.
          -- rewrite h_blocks_heap_update /=. erewrite (alter_eq_insert (h_blocks h1)) => //.
             rewrite alter_eq_insert_const //.
          -- iIntros "!>" (? Heq). iApply "IH". iPureIntro. rewrite -Heq.
             by rewrite h_blocks_heap_update /= insert_alter.
        * iDestruct (heapUR_lookup O2 with "[$] [$]") as %Hpo.
          have ? : v2 = v1. {
            move: Hp2 => /h_blocks_lookup_Some[??]. move: Hpo. rewrite -h_block_lookup. naive_solver.
          } subst.
          iDestruct ("Hc2" with "[Ht]") as "Hb"; [by iRight|].
          rewrite -kmap_insert insert_id //.
          iDestruct ("Hc" with "[$Hb $Hd]") as "Hb". rewrite (insert_id _ p bs1) //.
          iApply ("IH2" with "[//] [$] [$] [$] [$]").
      + iApply ("IH" with "[%] [$] [$] [$]"). by rewrite insert_id.
    - move: Hbs => /heap_state_blocks_eq ->. by iFrame.
  Qed.

  Lemma heapUR_ptsto_trader_trade l v :
    ⌈l ↦[O2] v @ W2⌉ -∗
    heapUR_ptsto_trader l v -∗
    heapUR_ptsto_trader l v ∗
    ⌈l ↦[O1] v @ W1⌉.
  Proof using BiAffine0.
    iIntros "Hl [?|?]".
    - by iFrame "Hl".
    - iDestruct (heapUR_ptsto_excl O2 with "[$] [$]") as %[].
  Qed.

  Lemma heapUR_dom_trader_trade p d :
    ⌈p ⤚[O2] d @ W2⌉ -∗
    heapUR_dom_trader p d -∗
    heapUR_dom_trader p d ∗
    ⌈p ⤚[O1] d @ W1⌉.
  Proof using BiAffine0.
    iIntros "Hl [?|?]".
    - by iFrame "Hl".
    - iDestruct (heapUR_dom_excl O2 with "[$] [$]") as %[].
  Qed.


  (** Trader lemmas  *)
  Lemma heapUR_trader_init_blocks hinit :
    ⌈heapUR_inv O1 (heap_from_blocks hinit) @ W1⌉ -∗
    ⌈[∗ map] p↦b∈hinit, p↦∗[O2] b @ W2⌉ -∗
    heapUR_trader.
  Proof using BiAffine0.
    iIntros "? Hinit". iFrame.
    rewrite !weak_embed_big_sepM h_blocks_heap_from_blocks.
    iApply (big_sepM_impl with "Hinit"). iIntros "!>" (???) "?". by iRight.
  Qed.

  Lemma heapUR_trade_ptsto h l v:
    heapUR_trader -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈l ↦[O2] v @ W2⌉ ==∗⌈W1⌉
    heapUR_trader ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈l ↦[O1] v @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "[%h1 Hinv1] Hinv2 Hl".
    iMod (heapUR_heap_trader_equalize with "Hinv1 [$]") as "[[Hinv1 Hbs] Hinv2]".
    iDestruct (heapUR_lookup O2 with "[$] Hl") as %?.
    iDestruct (big_sepM_lookup_acc with "Hbs") as "[[Hd Hls] Hc]".
    { apply h_blocks_lookup_Some. split!. by apply: lookup_heap_Some_elem_of_h_provs. }
    iDestruct (big_sepM_lookup_acc with "Hls") as "[Hp Hc2]".
    { apply/lookup_kmap_Some. eexists l.2. split!. by rewrite -h_block_lookup2. }
    rewrite -surjective_pairing.
    iDestruct (heapUR_ptsto_trader_trade with "[$] [$]") as "[? $]".
    iDestruct ("Hc2" with "[$]") as "?".
    iDestruct ("Hc" with "[$]") as "?".
    by iFrame.
  Qed.

  Lemma heapUR_trade_dom h p d:
    heapUR_trader -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈p ⤚[O2] d @ W2⌉ ==∗⌈W1⌉
    heapUR_trader ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈p ⤚[O1] d @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "[%h1 Hinv1] Hinv2 Hl".
    iMod (heapUR_heap_trader_equalize with "Hinv1 [$]") as "[[Hinv1 Hbs] Hinv2]".
    iDestruct (heapUR_lookup_dom O2 with "[$] Hl") as %<-.
    iDestruct (heapUR_lookup_dom_prov O2 with "[$] Hl") as %?.
    iDestruct (big_sepM_lookup_acc with "Hbs") as "[[Hd Hls] Hc]".
    { by apply h_blocks_lookup_Some. }
    iDestruct (heapUR_dom_trader_trade with "[$] [$]") as "[? $]".
    iDestruct ("Hc" with "[$]") as "?".
    by iFrame.
  Qed.

  Lemma heapUR_trade_ptsto_big h m:
    heapUR_trader -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈[∗ map] l↦v∈m, l ↦[O2] v @ W2⌉ ==∗⌈W1⌉
    heapUR_trader ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈[∗ map] l↦v∈m, l ↦[O1] v @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "Ht Hinv Hl".
    iInduction m as [|] "IH" using map_ind.
    { iModIntro. iFrame. iModIntro. done. }
    rewrite !big_sepM_insert //. iDestruct "Hl" as "[??]".
    iMod (heapUR_trade_ptsto with "[$] [$] [$]") as "[? [? $]]".
    iApply ("IH" with "[$] [$] [$]").
  Qed.

  Lemma heapUR_trade_block h p b:
    heapUR_trader -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈p ↦∗[O2] b @ W2⌉ ==∗⌈W1⌉
    heapUR_trader ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈p ↦∗[O1] b @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "Ht Hinv [Hd Hl]".
    iMod (heapUR_trade_dom with "[$] [$] [$]") as "[? [? $]]".
    by iMod (heapUR_trade_ptsto_big with "[$] [$] [$]") as "$".
  Qed.

  Lemma heapUR_trade_block_big h bs:
    heapUR_trader -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈[∗ map] p↦b∈ bs, p ↦∗[O2] b @ W2⌉ ==∗⌈W1⌉
    heapUR_trader ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈[∗ map] p↦b∈ bs, p ↦∗[O1] b @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "Ht Hinv Hbs".
    rewrite !weak_embed_big_sepM.
    iMod (big_sepM_impl_weak_bupd_frame with "Hbs [] [-]") as "[$ ?]". 2: iAccu. 2: by iModIntro.
    iIntros "!>" (???) "[??] ?".
    by iMod (heapUR_trade_block with "[$] [$] [$]") as "[$ [$ $]]".
  Qed.
End trader.

Section trader.
  Context {PROP1 PROP2 PROP : bi} `{!BiBUpd PROP1} `{!BiBUpd PROP2}.
  Context (W1 : BiWeakEmbed PROP1 PROP) (W2 : BiWeakEmbed PROP2 PROP).
  Context (O1 : BiOwn PROP1 heapUR) (O2 : BiOwn PROP2 heapUR).
  Context `{!BiBUpd PROP} `{!BiAffine PROP} `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.

  Lemma heapUR_ptsto_trader_switch l v :
    heapUR_ptsto_trader W1 W2 O1 O2 l v -∗
    heapUR_ptsto_trader W2 W1 O2 O1 l v.
  Proof using BiAffine0. iIntros "[$|$]". Qed.

  Lemma heapUR_dom_trader_switch p d :
    heapUR_dom_trader W1 W2 O1 O2 p d -∗
    heapUR_dom_trader W2 W1 O2 O1 p d.
  Proof using BiAffine0. iIntros "[$|$]". Qed.

  Lemma heapUR_block_trader_switch p b :
    heapUR_block_trader W1 W2 O1 O2 p b -∗
    heapUR_block_trader W2 W1 O2 O1 p b.
  Proof using BiAffine0.
    iIntros "[??]".
    iDestruct (heapUR_dom_trader_switch with "[$]") as "$".
    iApply (big_sepM_impl with "[$]"). iIntros "!>" (???) "?".
    by iApply heapUR_ptsto_trader_switch.
  Qed.

  (** Trader lemmas  *)
  Lemma heapUR_trader_switch h :
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W2 W1 O2 O1 ∗
    ⌈heapUR_inv O1 h @ W1⌉.
  Proof using BiWeakEmbedBUpd1 BiWeakEmbedBUpd0 BiAffine0.
    iIntros "[%h1 Hinv1] Hinv2".
    iMod (heapUR_heap_trader_equalize with "Hinv1 [$]") as "[[??] ?]".
    iModIntro. iFrame. iApply (big_sepM_impl with "[$]").
    iIntros "!>" (???) "?". by iApply heapUR_block_trader_switch.
  Qed.

End trader.

(*
Section trader.
  Context {PROP1 PROP2 PROP : bi}.
  Context `{!BiBUpd PROP1} `{!BiBUpd PROP2} `{!BiBUpd PROP} `{!BiAffine PROP}.
  Context (W1 : BiWeakEmbed PROP1 PROP) (W2 : BiWeakEmbed PROP2 PROP).
  Context `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.
  Context (O1 : BiOwn PROP1 heapUR) (O2 : BiOwn PROP2 heapUR).

  Lemma heapUR_trader_init_blocks hinit :
    ⌈heapUR_inv O2 (heap_from_blocks hinit) @ W2⌉ -∗
    ⌈[∗ map] p↦b∈hinit, p↦∗[O1] b @ W1⌉ -∗
    heapUR_trader W2 W1 O2 O1.
  Proof.
    iIntros "? Hinit". iFrame. unfold heapUR_block. rewrite big_sepM_sep.
    iDestruct "Hinit" as "[??]".
    rewrite !weak_embed_big_sepM. iExists ∅, ∅.
  Abort.


  Lemma heapUR_trader_switch h :
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W2 W1 O2 O1 ∗
    ⌈heapUR_inv O1 h @ W1⌉.
  Proof.
    iIntros "(%h1 & %ls & %ds & Hinv1 & Hls1 & Hds1 & Hls2 & Hds2) Hinv".
    have [ps Hps] : ∃ ps, ps = h_provs h1 by naive_solver.
    iInduction ps as [p ps| p ps |] "IH" using (set_equalize_ind_L (h_provs h)) forall (h1 ls ds Hps); subst.
    - iMod (heapUR_alloc_block O1 _ p ∅ with "Hinv1") as "[? [Hd _]]"; [done|].
      iApply ("IH" with "[%] [$] [$] [Hd Hds1] [Hls2] [Hds2] [$]").
      + by rewrite /= dom_singleton_L.
      + by iApply (big_sepM_insert_2 with "[Hd] Hds1").
      + simpl. admit.
      + admit.
    - admit.
    -

admit.
    (* add new provenances to h1 *)
    (* delete removed provenances from h1 *)
    (* update all heap locations to match *)
  Abort.

  Lemma heapUR_trade_ptsto h l v:
    heapUR_trader W1 W2 O1 O2 -∗
    (* TODO: Do we need this? *)
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈l ↦[O2] v @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W1 W2 O1 O2 ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈l ↦[O1] v @ W1⌉.
  Proof.
    iIntros "(%h1 & %ls & %ds & Hinv1 & Hls1 & Hds1 & Hls2 & Hds2) Hinv Hl".
    (* TODO: Is there a better way to prove this via heapUR_trader_switch? *)
    destruct (h_heap h1 !! l) eqn:Hh1.
    - destruct (ls !! l) eqn: Hls.
      + iDestruct (big_sepM_delete with "Hls1") as "[Hl' Hls1]"; [done|].
        (* Set Typeclasses Debug Verbosity 2. *)
        iMod (heapUR_update O1 with "[$] [$]") as "[??]".
        iModIntro. iFrame. rewrite h_block_doms_h_update. iFrame => /=.
        erewrite difference_delete. 2: { apply lookup_alter_Some. naive_solver. }
        rewrite insert_difference insert_alter -insert_difference.
        by iApply (big_sepM_insert_2 with "[Hl]").
      + iDestruct (big_sepM_lookup_acc _ _ l with "Hls2") as "[??]".
        { by apply lookup_difference_Some. }
        iDestruct (heapUR_ptsto_excl (PROP:=PROP2) with "Hl [$]") as %[].
    - destruct (decide (l.1 ∈ h_provs h1)).
      + destruct (ds !! l.1) eqn:Hds.
        * (* get heapUR_dom O1 l.1 g, update h1 to add l to the heap, return ownership    *)
          admit.
        * iDestruct (big_sepM_lookup_acc with "Hds2") as "[Hd ?]".
          { apply lookup_difference_Some. split; [|done]. by apply h_block_doms_lookup_Some. }
          iDestruct (heapUR_lookup (PROP:=PROP2) with "Hinv Hl") as %?.
          iDestruct (heapUR_lookup_dom (PROP:=PROP2) with "Hinv Hd") as %Heq.
          exfalso. have : l.2 ∈ dom (h_block h l.1).
          -- apply elem_of_dom. by rewrite -h_block_lookup2.
          -- rewrite Heq => /elem_of_dom. by rewrite -h_block_lookup2 Hh1 => -[].
      + (* allocate the block in h1 *)
        iMod (heapUR_alloc_block O1 _ l.1 {[l.2 := v]} with "Hinv1")
          as "[Hinv1 [Hd Hl']]"; [done|]. iModIntro.
        rewrite kmap_insert kmap_empty big_sepM_singleton -surjective_pairing.
        iFrame "Hinv1 Hinv Hl' Hls1".
        iExists _. iSplitL "Hd Hds1". iApply (big_sepM_insert with "[$]"). admit.
        rewrite /= map_difference_union_distr.
        iSplitL "Hls2 Hl".
        * iApply (big_sepM_union_2 with "[Hl] Hls2").
          admit.
        * admit.
  Abort.

  Lemma heapUR_trade_dom h p d:
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈p ⤚[O2] d @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W1 W2 O1 O2 ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈p ⤚[O1] d @ W1⌉.
  Proof.
    iIntros "(%h1 & %ls & %ds & Hinv1 & Hls1 & Hds1 & Hls2 & Hds2) Hinv2 Hd".
    destruct (decide (p ∈ h_provs h1)).
    - destruct (ds !! p) as [d'|] eqn:Hds.
      + iDestruct (big_sepM_insert_acc with "Hds1") as "[??]"; [done|].

 (* deallocate all locations in p that are in ls (works because we have the pointstos for them),
           allocate all locations with 0 that are in g,
           the locations in h_heap h1 can stay unchanged since we have the pointsto *)
        admit.
      + iDestruct (big_sepM_lookup_acc with "Hds2") as "[??]".
        { apply lookup_difference_Some. split; [|done]. by apply h_block_doms_lookup_Some. }
        iDestruct (heapUR_dom_excl (PROP:=PROP2) with "Hd [$]") as %[].
    - iMod (heapUR_alloc_block O1 _ p (gset_to_gmap (ValNum 0%Z) d) with "Hinv1") as "[Hinv1 [Hd' Hls']]"; [done|].
      iModIntro. rewrite dom_gset_to_gmap weak_embed_big_sepM. iFrame "Hinv1 Hinv2 Hd' Hds1".
      iExists _. iSplitL "Hls1 Hls'"; [iApply (big_sepM_union_2 with "Hls1 Hls'")|]. iSplitL "Hls2".
      + rewrite /= map_difference_union_distr (map_difference_empty_dom (gmap_uncurry _)) ?left_id_L.
        * rewrite -map_difference_difference (map_difference_disj_id (_ ∖ _)) //.
          apply map_disjoint_spec => ??? /lookup_difference_Some[/lookup_heap_Some_elem_of_h_provs? ?] /lookup_kmap_Some. naive_solver.
        * move => [??] /elem_of_dom [?]. rewrite lookup_gmap_uncurry. move => /bind_Some[? [/lookup_singleton_Some[??] Hl]]. simplify_eq/=.
          rewrite dom_union_L. apply elem_of_union. right. apply elem_of_dom. eexists _. apply/lookup_kmap_Some. naive_solver.
      + admit.
  Abort.

  Lemma heapUR_trade_ptsto_big h m:
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈[∗ map] l↦v∈m, l ↦[O2] v @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W1 W2 O1 O2 ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈[∗ map] l↦v∈m, l ↦[O1] v @ W1⌉.
  Proof using BiAffine0.
    iIntros "Ht Hinv Hl".
    iInduction m as [|] "IH" using map_ind.
    { iModIntro. iFrame. iModIntro. done. }
    rewrite !big_sepM_insert //. iDestruct "Hl" as "[??]".
    iMod (heapUR_trade_ptsto with "[$] [$] [$]") as "[? [? $]]".
    iApply ("IH" with "[$] [$] [$]").
  Qed.

  Lemma heapUR_trade_block h p b:
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈p ↦∗[O2] b @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W1 W2 O1 O2 ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈p ↦∗[O1] b @ W1⌉.
  Proof using BiAffine0.
    iIntros "Ht Hinv [Hd Hl]".
    iMod (heapUR_trade_dom with "[$] [$] [$]") as "[? [? $]]".
    by iMod (heapUR_trade_ptsto_big with "[$] [$] [$]") as "$".
  Qed.

  Lemma heapUR_trade_block_big h bs:
    heapUR_trader W1 W2 O1 O2 -∗
    ⌈heapUR_inv O2 h @ W2⌉ -∗
    ⌈[∗ map] p↦b∈ bs, p ↦∗[O2] b @ W2⌉ ==∗⌈W1⌉
    heapUR_trader W1 W2 O1 O2 ∗
    ⌈heapUR_inv O2 h @ W2⌉ ∗
    ⌈[∗ map] p↦b∈ bs, p ↦∗[O1] b @ W1⌉.
  Proof using BiAffine0.
    iIntros "Ht Hinv Hbs".
  Abort.
End trader.
*)

Global Typeclasses Opaque heapUR_trader.
Global Opaque heapUR_trader.
