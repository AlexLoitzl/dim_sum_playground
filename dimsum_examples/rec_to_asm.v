From iris.algebra.lib Require Import gmap_view.
From dimsum.core Require Export proof_techniques prepost.
From dimsum.core Require Import link.
From dimsum.examples Require Import rec asm.

Local Open Scope Z_scope.

(** * rec_to_asm *)

(** * Registers *)
Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  args_registers ++ ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"].

Definition touched_registers : list string :=
  tmp_registers ++ saved_registers.

Definition r2a_regs_ret (rs rsold : gmap string Z) (av : Z) : Prop :=
  rs !!! "R0" = av ∧
  map_preserved saved_registers rsold rs.

(** * Mapping of provenances *)
Inductive rec_to_asm_elem :=
| R2AShared (a : Z) | R2AConstant (h : gmap Z val).

Definition r2a_rh_shared (rh : gmap prov rec_to_asm_elem) : gmap prov Z :=
  omap (λ k, if k is R2AShared a then Some a else None) rh.

Definition r2a_rh_constant (rh : gmap prov rec_to_asm_elem) : gmap prov (gmap Z val) :=
  omap (λ k, if k is R2AConstant b then Some b else None) rh.

Lemma r2a_ih_shared_Some h p a :
  r2a_rh_shared h !! p = Some a ↔ h !! p = Some (R2AShared a).
Proof.
  rewrite /r2a_rh_shared lookup_omap_Some. split.
  - move => [?[??]]. case_match; naive_solver.
  - move => ?. split!.
Qed.

Lemma r2a_rh_shared_None h p :
  r2a_rh_shared h !! p = None ↔ ¬ ∃ a, h !! p = Some (R2AShared a).
Proof. rewrite eq_None_not_Some /is_Some. setoid_rewrite r2a_ih_shared_Some. naive_solver. Qed.

Lemma r2a_rh_shared_empty:
  r2a_rh_shared ∅ = ∅.
Proof. by rewrite /r2a_rh_shared omap_empty. Qed.

Lemma r2a_rh_shared_union rh1 rh2:
  rh1 ##ₘ rh2 →
  r2a_rh_shared (rh1 ∪ rh2) = r2a_rh_shared rh1 ∪ r2a_rh_shared rh2.
Proof. apply map_omap_union. Qed.

Lemma r2a_rh_shared_fmap rh:
  r2a_rh_shared (R2AShared <$> rh) = rh.
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite r2a_ih_shared_Some lookup_fmap fmap_Some.
  naive_solver.
Qed.

Lemma r2a_rh_shared_fmap_l rh:
  R2AShared <$> r2a_rh_shared rh ⊆ rh.
Proof.
  apply map_subseteq_spec => ??.
  rewrite lookup_fmap fmap_Some. move => [? [/r2a_ih_shared_Some??]].
  naive_solver.
Qed.

Lemma r2a_rh_shared_fmap_constant rh:
  r2a_rh_shared (R2AConstant <$> rh) = ∅.
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite r2a_ih_shared_Some lookup_fmap fmap_Some. naive_solver.
Qed.

Lemma r2a_rh_shared_insert i h rh:
  r2a_rh_shared (<[i := R2AShared h]> rh) = <[i := h]> (r2a_rh_shared rh).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !r2a_ih_shared_Some.
  rewrite !lookup_insert_Some !r2a_ih_shared_Some. naive_solver.
Qed.

Lemma r2a_rh_shared_insert_const i h rh:
  (∀ x, rh !! i ≠ Some (R2AShared x)) →
  r2a_rh_shared (<[i := R2AConstant h]> rh) = r2a_rh_shared rh.
Proof.
  move => ?.
  apply map_eq => ?. apply option_eq => ?. rewrite !r2a_ih_shared_Some.
  rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma r2a_rh_shared_delete i rh:
  r2a_rh_shared (delete i rh) = delete i (r2a_rh_shared rh).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  by rewrite !r2a_ih_shared_Some !lookup_delete_Some !r2a_ih_shared_Some.
Qed.

Lemma r2a_rh_constant_Some h p a :
  r2a_rh_constant h !! p = Some a ↔ h !! p = Some (R2AConstant a).
Proof.
  rewrite /r2a_rh_constant lookup_omap_Some. split.
  - move => [?[??]]. case_match; naive_solver.
  - move => ?. split!.
Qed.

Lemma r2a_rh_constant_None h p :
  r2a_rh_constant h !! p = None ↔ ¬ ∃ a, h !! p = Some (R2AConstant a).
Proof. rewrite eq_None_not_Some /is_Some. setoid_rewrite r2a_rh_constant_Some. naive_solver. Qed.

Lemma r2a_rh_constant_empty:
  r2a_rh_constant ∅ = ∅.
Proof. by rewrite /r2a_rh_constant omap_empty. Qed.

Lemma r2a_rh_constant_union rh1 rh2:
  rh1 ##ₘ rh2 →
  r2a_rh_constant (rh1 ∪ rh2) = r2a_rh_constant rh1 ∪ r2a_rh_constant rh2.
Proof. apply map_omap_union. Qed.

Lemma r2a_rh_constant_fmap rh:
  r2a_rh_constant (R2AConstant <$> rh) = rh.
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite r2a_rh_constant_Some lookup_fmap fmap_Some.
  naive_solver.
Qed.

Lemma r2a_rh_constant_fmap_l rh:
  R2AConstant <$> r2a_rh_constant rh ⊆ rh.
Proof.
  apply map_subseteq_spec => ??.
  rewrite lookup_fmap fmap_Some. move => [? [/r2a_rh_constant_Some??]].
  naive_solver.
Qed.

Lemma r2a_rh_constant_fmap_shared rh:
  r2a_rh_constant (R2AShared <$> rh) = ∅.
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite r2a_rh_constant_Some lookup_fmap fmap_Some. naive_solver.
Qed.

Lemma r2a_rh_constant_delete i rh:
  r2a_rh_constant (delete i rh) = delete i (r2a_rh_constant rh).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  by rewrite !r2a_rh_constant_Some !lookup_delete_Some !r2a_rh_constant_Some.
Qed.

Lemma r2a_rh_constant_insert i h rh:
  r2a_rh_constant (<[i := R2AConstant h]> rh) = <[i := h]> (r2a_rh_constant rh).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !r2a_rh_constant_Some.
  rewrite !lookup_insert_Some !r2a_rh_constant_Some. naive_solver.
Qed.

Lemma r2a_rh_constant_insert_shared i a rh:
  (∀ x, rh !! i ≠ Some (R2AConstant x)) →
  r2a_rh_constant (<[i := R2AShared a]> rh) = r2a_rh_constant rh.
Proof.
  move => ?.
  apply map_eq => ?. apply option_eq => ?. rewrite !r2a_rh_constant_Some.
  rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma r2a_rh_shared_constant_disj rh:
  R2AShared <$> (r2a_rh_shared rh) ##ₘ R2AConstant <$> (r2a_rh_constant rh).
Proof.
  apply map_disjoint_spec => ???. rewrite !lookup_fmap !fmap_Some.
  setoid_rewrite r2a_ih_shared_Some. setoid_rewrite r2a_rh_constant_Some. naive_solver.
Qed.

Lemma r2a_rh_shared_constant rh :
  (R2AShared <$> r2a_rh_shared rh) ∪ (R2AConstant <$> r2a_rh_constant rh) = rh.
Proof.
  apply map_eq => ?. apply option_eq => e.
  rewrite !lookup_union_Some. 2: { apply r2a_rh_shared_constant_disj. }
  rewrite !lookup_fmap !fmap_Some.
  setoid_rewrite r2a_ih_shared_Some. setoid_rewrite r2a_rh_constant_Some.
  split; destruct e; naive_solver.
Qed.

(** * Ghost state *)
(** ** Ghost state definitions *)
Canonical Structure rec_to_asm_elemO := leibnizO rec_to_asm_elem.

Definition rec_to_asmUR : ucmra :=
  prodUR (prodUR
   (gmap_viewUR prov (agreeR rec_to_asm_elemO))
   (gmap_viewUR Z (agreeR (optionO ZO))))
   (optionUR (agreeR (leibnizO (gmap string Z)))).

Global Instance rec_to_asmUR_shrink : Shrink rec_to_asmUR.
Proof. solve_shrink. Qed.

Definition r2a_heap_inj (r : (gmap_viewUR prov (agreeR rec_to_asm_elemO))) : rec_to_asmUR := (r, ε, ε).
Definition r2a_mem_inj (r : (gmap_viewUR Z (agreeR $ optionO ZO))) : rec_to_asmUR := (ε, r, ε).
Definition r2a_f2i_inj (f2i : gmap string Z) : rec_to_asmUR := (ε, ε, Some (to_agree (f2i : leibnizO (gmap string Z)))).

Definition r2a_heap_auth (h : gmap prov rec_to_asm_elemO) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_heap_inj (gmap_view_auth (DfracOwn 1) (to_agree <$> h))).
Definition r2a_heap_shared (p : prov) (a : Z) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_heap_inj (gmap_view_frag p DfracDiscarded (to_agree $ R2AShared a))).
Definition r2a_heap_constant (p : prov) (b : gmap Z val) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_heap_inj (gmap_view_frag p (DfracOwn 1) (to_agree $ R2AConstant b))).

Definition r2a_mem_auth (amem : gmap Z (option Z)) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_mem_inj (gmap_view_auth (DfracOwn 1) (to_agree <$> amem))).
Definition r2a_mem_constant (a : Z) (v : option Z) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_mem_inj (gmap_view_frag a (DfracOwn 1) (to_agree v))).

Definition r2a_mem_map (m : gmap Z (option Z)) : uPred rec_to_asmUR :=
  ([∗ map] a↦v ∈ m, r2a_mem_constant a v).

Definition r2a_f2i_full (f2i : gmap string Z) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_f2i_inj f2i).

(* Intuitively, [r2a_f2i_incl f2i ins] means that [f2i] is part of the
global function to address map and that it is precise on the addresses
in [ins], i.e. no functions not in f2i point to [ins]. *)
Definition r2a_f2i_incl (f2i : gmap string Z) (ins : gset Z) : uPred rec_to_asmUR :=
  ∃ f2i_full, ⌜f2i ⊆ f2i_full⌝ ∗ ⌜∀ f i, i ∈ ins → f2i_full !! f = Some i → f2i !! f = Some i⌝
  ∗ r2a_f2i_full f2i_full .

(** ** Ghost state lemmas *)
Lemma r2a_mem_constant_excl a v1 v2 :
  r2a_mem_constant a v1 -∗
  r2a_mem_constant a v2 -∗
  False.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [[?/=/gmap_view_frag_op_valid[??]]?].
  naive_solver.
Qed.

Lemma r2a_mem_map_constant_excl m1 a v :
  r2a_mem_map m1 -∗
  r2a_mem_constant a v -∗
  ⌜m1 !! a = None⌝.
Proof.
  iIntros "Hmem Hc".
  destruct (m1 !! a) eqn:? => //.
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (r2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma r2a_mem_map_excl m1 m2 :
  r2a_mem_map m1 -∗
  r2a_mem_map m2 -∗
  ⌜m1 ##ₘ m2⌝.
Proof.
  iIntros "Hm1 Hm2". rewrite map_disjoint_alt. iIntros (i).
  destruct (m1 !! i) eqn:?; [|iPureIntro; naive_solver].
  destruct (m2 !! i) eqn:?; [|iPureIntro; naive_solver].
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
  iDestruct (r2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma r2a_heap_alloc' rh p b:
  rh !! p = None →
  r2a_heap_auth rh ⊢ |==> r2a_heap_auth (<[p := R2AConstant b]> rh) ∗ r2a_heap_constant p b.
Proof.
  move => ?.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update. rewrite -pair_op_1.
  apply prod_update; [|done]. apply prod_update; [|done]. rewrite fmap_insert.
  apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
Qed.

Lemma r2a_heap_alloc_big' rh rh' :
  (R2AConstant <$> rh') ##ₘ rh →
  r2a_heap_auth rh ⊢ |==> r2a_heap_auth ((R2AConstant <$> rh') ∪ rh) ∗ [∗ map] p↦a∈rh', r2a_heap_constant p a.
Proof.
  iIntros (?) "Hh".
  iInduction rh' as [|p a rh' ?] "IH" using map_ind;
    rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
  { rewrite left_id big_sepM_empty. by iFrame. }
  iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
  iMod (r2a_heap_alloc' with "[$]") as "[$ ?]".
  { apply lookup_union_None. split!. rewrite lookup_fmap. by apply fmap_None. }
  rewrite big_sepM_insert //. by iFrame.
Qed.

Lemma r2a_heap_to_shared' p h rh a:
  r2a_heap_auth rh ∗ r2a_heap_constant p h ⊢ |==> r2a_heap_auth (<[p := R2AShared a]> rh) ∗ r2a_heap_shared p a.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update. rewrite -!pair_op_1.
  apply prod_update; [|done]. apply prod_update; [|done].
  etrans.
  - by apply (gmap_view_replace _ _ _ (to_agree (R2AShared a))).
  - apply cmra_update_op; [by rewrite fmap_insert|].
    apply gmap_view_frag_persist.
Qed.

Lemma r2a_heap_alloc_shared' rh p a:
  rh !! p = None →
  r2a_heap_auth rh ⊢ |==> r2a_heap_auth (<[p := R2AShared a]> rh) ∗ r2a_heap_shared p a.
Proof.
  iIntros (?) "?".
  iMod (r2a_heap_alloc' _ _ ∅ with "[$]"); [done|].
  iMod (r2a_heap_to_shared' with "[$]"). iModIntro. by rewrite insert_insert.
Qed.

Lemma r2a_heap_alloc_shared_big' rh rh' :
  (R2AShared <$> rh') ##ₘ rh →
  r2a_heap_auth rh ⊢ |==> r2a_heap_auth ((R2AShared <$> rh') ∪ rh) ∗ [∗ map] p↦a∈rh', r2a_heap_shared p a.
Proof.
  iIntros (?) "Hh".
  iInduction rh' as [|p a rh' ?] "IH" using map_ind;
    rewrite ->?fmap_empty, ?fmap_insert in *; decompose_map_disjoint.
  { rewrite left_id big_sepM_empty. by iFrame. }
  iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
  iMod (r2a_heap_alloc_shared' with "[$]") as "[$ ?]".
  { apply lookup_union_None. split!. rewrite lookup_fmap. by apply fmap_None. }
  rewrite big_sepM_insert //. by iFrame.
Qed.

Lemma r2a_heap_update' p h h' rh :
  r2a_heap_auth rh ∗ r2a_heap_constant p h ⊢ |==> r2a_heap_auth (<[p := R2AConstant h']> rh) ∗ r2a_heap_constant p h'.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update. rewrite -!pair_op_1.
  apply prod_update; [|done]. apply prod_update; [|done]. rewrite fmap_insert.
  by apply gmap_view_replace.
Qed.

Lemma r2a_heap_free' h p h' :
  r2a_heap_auth h ∗ r2a_heap_constant p h' ⊢ |==> r2a_heap_auth (delete p h).
Proof.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update. rewrite -pair_op_1.
  apply prod_update; [|done]. apply prod_update; [|done]. rewrite fmap_delete.
  by apply gmap_view_delete.
Qed.

Lemma r2a_heap_free_big' h m :
  r2a_heap_auth h -∗
  ([∗ map] p↦a ∈m, r2a_heap_constant p a) ==∗
  r2a_heap_auth (h ∖ (R2AConstant <$> m)).
Proof.
  iIntros "Hauth Hm".
  iInduction m as [|a v m' ?] "IH" using map_ind. { iModIntro. by rewrite fmap_empty right_id_L. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[? Hm]".
  iMod ("IH" with "[$] [$]"). iMod (r2a_heap_free' with "[$]"). iModIntro.
  rewrite fmap_insert. by rewrite -delete_difference.
Qed.

Lemma r2a_heap_lookup' h p h' :
  r2a_heap_auth h -∗
  r2a_heap_constant p h' -∗
  ⌜h !! p = Some (R2AConstant h')⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [[/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _]_].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma r2a_heap_shared_lookup' h p a :
  r2a_heap_auth h -∗
  r2a_heap_shared p a -∗
  ⌜h !! p = Some (R2AShared a)⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [[/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _]_].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma r2a_heap_lookup_big' m h :
  r2a_heap_auth h -∗
  ([∗ map] p↦b∈m, r2a_heap_constant p b) -∗
  ⌜m ⊆ r2a_rh_constant h⌝.
Proof.
  iIntros "Ha Hm".
  iInduction m as [|a v m' ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
  iDestruct (r2a_heap_lookup' with "[$] [$]") as %?.
  iDestruct ("IH" with "[$] [$]") as %?. iPureIntro.
  apply insert_subseteq_l; [|done]. by apply r2a_rh_constant_Some.
Qed.

Lemma r2a_heap_shared_lookup_big' m h :
  r2a_heap_auth h -∗
  ([∗ map] p↦a∈m, r2a_heap_shared p a) -∗
  ⌜m ⊆ r2a_rh_shared h⌝.
Proof.
  iIntros "Ha Hm".
  iInduction m as [|a v m' ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
  iDestruct (r2a_heap_shared_lookup' with "[$] [$]") as %?.
  iDestruct ("IH" with "[$] [$]") as %?. iPureIntro.
  apply insert_subseteq_l; [|done]. by apply r2a_ih_shared_Some.
Qed.

Lemma r2a_heap_shared_ag p a1 a2 :
  r2a_heap_shared p a1 -∗
  r2a_heap_shared p a2 -∗
  ⌜a1 = a2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [[/=/gmap_view_frag_op_valid[?/to_agree_op_valid ?]?]?].
  naive_solver.
Qed.

Lemma r2a_heap_shared_ag_big ps p a :
  ([∗ map] p↦z∈ps, r2a_heap_shared p z) -∗
  r2a_heap_shared p a -∗
  ⌜a = default a (ps !! p)⌝.
Proof.
  iIntros "Hps Hp".
  destruct (ps !! p) as [z'|] eqn:Hp => //=.
  iDestruct (big_sepM_lookup with "Hps") as "?"; [done|].
  iAssert ⌜z' = a⌝%I as %?; [|done].
  by iApply (r2a_heap_shared_ag with "[$]").
Qed.

Lemma r2a_mem_alloc' a v amem :
  amem !! a = None →
  r2a_mem_auth amem ⊢ |==> r2a_mem_auth (<[a := v]> amem) ∗ r2a_mem_constant a v.
Proof.
  move => ?.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. rewrite -pair_op_2.
  apply prod_update; [|done]. apply prod_update; [done|]. rewrite fmap_insert.
  apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap fmap_None.
Qed.

Lemma r2a_mem_alloc_big' mem mem' :
  mem' ##ₘ mem →
  r2a_mem_auth mem ⊢ |==> r2a_mem_auth (mem' ∪ mem) ∗ r2a_mem_map mem'.
Proof.
  iIntros (?) "Hmem". rewrite /r2a_mem_map.
  iInduction mem' as [|a v mem' ?] "IH" using map_ind; decompose_map_disjoint.
  { rewrite left_id big_sepM_empty. by iFrame. }
  iMod ("IH" with "[//] [$]") as "[??]". rewrite -insert_union_l.
  iMod (r2a_mem_alloc' a with "[$]") as "[$ ?]". { by apply lookup_union_None. }
  rewrite big_sepM_insert //. by iFrame.
Qed.

Lemma r2a_mem_update' v' a v amem :
  r2a_mem_auth amem ∗ r2a_mem_constant a v ⊢ |==> r2a_mem_auth (<[a := v']> amem) ∗ r2a_mem_constant a v'.
Proof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. rewrite -!pair_op_2.
  apply prod_update; [|done]. apply prod_update; [done|]. rewrite fmap_insert.
  by apply gmap_view_replace.
Qed.

Lemma r2a_mem_delete' a v amem :
  r2a_mem_auth amem ∗ r2a_mem_constant a v ⊢ |==> r2a_mem_auth (delete a amem).
Proof.
  rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_1. rewrite -!pair_op_2.
  apply prod_update; [|done]. apply prod_update; [done|]. rewrite fmap_delete.
  by apply gmap_view_delete.
Qed.

Lemma r2a_mem_delete_big' m amem :
  r2a_mem_auth amem -∗ r2a_mem_map m ==∗ r2a_mem_auth (amem ∖ m).
Proof.
  iIntros "Hauth Hm".
  iInduction m as [|a v m' ?] "IH" using map_ind. { iModIntro. by rewrite right_id_L. }
  rewrite /r2a_mem_map big_sepM_insert //. iDestruct "Hm" as "[? Hm]".
  iMod ("IH" with "[$] [$]"). iMod (r2a_mem_delete' with "[$]"). iModIntro.
  by rewrite -delete_difference.
Qed.

Lemma r2a_mem_lookup' a v amem :
  r2a_mem_auth amem -∗
  r2a_mem_constant a v -∗
  ⌜amem !! a = Some v⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [[_ /(gmap_view_both_dfrac_valid_discrete_total _ _ _)+]_].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma r2a_mem_lookup_big' m mem :
  r2a_mem_auth mem -∗
  r2a_mem_map m -∗
  ⌜m ⊆ mem⌝.
Proof.
  iIntros "Ha Hm". rewrite /r2a_mem_map.
  iInduction m as [|a v m' ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hv Hm]".
  iDestruct (r2a_mem_lookup' with "[$] [$]") as %?.
  iDestruct ("IH" with "[$] [$]") as %?. iPureIntro.
  by apply insert_subseteq_l.
Qed.

Lemma r2a_mem_update_all mem mem' mo :
  mo ⊆ mem →
  mo ⊆ mem' →
  r2a_mem_auth mem' -∗
  r2a_mem_map (mem' ∖ mo) ==∗
  r2a_mem_auth mem ∗ r2a_mem_map (mem ∖ mo).
Proof.
  iIntros (Hsub ?) "Hmem Hconst".
  iMod (r2a_mem_delete_big' with "[$] [$]").
  iMod (r2a_mem_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???. rewrite !lookup_difference_Some lookup_difference_None /is_Some.
    move => ??. destruct!. } iModIntro.
  rewrite map_difference_id // map_union_comm ?map_difference_union //. apply map_disjoint_difference_l'.
Qed.

Lemma r2a_heap_update_all rhs rhc rh hob :
  hob ⊆ r2a_rh_constant rh →
  hob ⊆ rhc →
  r2a_rh_shared rh ⊆ rhs →
  dom rhs ## dom rhc →
  r2a_heap_auth rh -∗
  ([∗ map] p↦a∈r2a_rh_shared rh, r2a_heap_shared p a) -∗
  ([∗ map] p↦a∈r2a_rh_constant rh ∖ hob, r2a_heap_constant p a) ==∗
  r2a_heap_auth ((R2AShared <$> rhs) ∪ (R2AConstant <$> rhc)) ∗
  ([∗ map] p↦a∈rhs, r2a_heap_shared p a) ∗
  ([∗ map] p↦a∈rhc ∖ hob, r2a_heap_constant p a).
Proof.
  iIntros (Hsub1 Hsub2 Hsh Hdisj) "Hauth #Hsh Hconst".
  iMod (r2a_heap_free_big' with "[$] [$]") as "?".
  iMod (r2a_heap_alloc_shared_big' _ (rhs ∖ r2a_rh_shared rh) with "[$]") as "[??]".
  { apply map_disjoint_spec => ? x y.
    rewrite lookup_fmap fmap_Some !lookup_difference_Some lookup_fmap fmap_None lookup_difference_None.
    setoid_rewrite lookup_difference_Some. unfold is_Some.
    setoid_rewrite r2a_rh_constant_None.
    setoid_rewrite r2a_rh_shared_None.
    move => ??. destruct!.
    - destruct y; naive_solver.
    - have ? := lookup_weaken _ _ _ _ ltac:(done) Hsub2.
      apply: Hdisj; by apply elem_of_dom.
  }
  have -> : ((R2AShared <$> rhs ∖ r2a_rh_shared rh) ∪ rh ∖ (R2AConstant <$> r2a_rh_constant rh ∖ hob)) =
             (R2AShared <$> rhs) ∪ (R2AConstant <$> hob). {
    rewrite - {2}(r2a_rh_shared_constant rh).
    rewrite map_difference_union_distr assoc. f_equal.
    - rewrite (map_difference_disj_id _ (R2AConstant <$> _)).
      2: { rewrite map_difference_fmap. apply: map_disjoint_weaken_r; [apply r2a_rh_shared_constant_disj|].
           by apply map_subseteq_difference_l. }
      rewrite -map_fmap_union map_union_comm ?map_difference_union //.
      apply map_disjoint_difference_l'.
    - rewrite map_difference_fmap. apply map_difference_id. by apply map_fmap_mono.
  }
  iMod (r2a_heap_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???.
    rewrite lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None.
    setoid_rewrite lookup_difference_Some.
    move => ??. destruct!.
    apply: Hdisj; by apply elem_of_dom.
  } iModIntro.
  iAssert ([∗ map] p↦a ∈ rhs, r2a_heap_shared p a)%I as "#Hsh'". {
    rewrite - {3} (map_difference_union (r2a_rh_shared rh) rhs) //.
    by iApply big_sepM_union_2.
  } iFrame "Hsh'".
  iDestruct (r2a_heap_shared_lookup_big' with "[$] Hsh'") as %Hsub.
  have -> : ((R2AConstant <$> rhc ∖ hob) ∪ ((R2AShared <$> rhs) ∪ (R2AConstant <$> hob))) =
             ((R2AShared <$> rhs) ∪ (R2AConstant <$> rhc)). {
    rewrite assoc_L (map_union_comm _ (R2AShared <$> _)). 2: {
      rewrite map_difference_fmap. apply: map_disjoint_weaken_l; [|by apply map_subseteq_difference_l].
      apply map_disjoint_dom_2. by rewrite !dom_fmap_L.
    }
    rewrite -assoc. f_equal. rewrite -map_fmap_union. rewrite map_union_comm ?map_difference_union //.
    apply map_disjoint_difference_l'.
  }
  done.
Qed.

Lemma r2a_f2i_full_agree f2i1 f2i2 :
  r2a_f2i_full f2i1 -∗
  r2a_f2i_full f2i2 -∗
  ⌜f2i1 = f2i2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/=[??]].
  rewrite -Some_op. move => /Some_valid/to_agree_op_valid. done.
Qed.

Lemma r2a_f2i_incl_in_ins f i f2i ins :
  i ∈ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f2i !! f = Some i⌝.
Proof.
  iIntros (Hi) "(%f2i_full&%Hsub&%Hins&Hf2i1) (%&%Hsub2&%&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst. iPureIntro.
  apply: Hins; [done|]. apply: lookup_weaken; [|done]. by simplify_map_eq.
Qed.

Lemma r2a_f2i_incl_agree_f f i1 i2 f2i1 f2i2 ins1 ins2 :
  f2i1 !! f = Some i1 →
  f2i2 !! f = Some i2 →
  r2a_f2i_incl f2i1 ins1 -∗
  r2a_f2i_incl f2i2 ins2 -∗
  ⌜i1 = i2⌝.
Proof.
  move => Hf1 Hf2.
  iIntros "(%f2i_full&%Hsub&%Hins&Hf2i1) (%&%Hsub2&%&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst. iPureIntro.
  move: Hf1 => /(lookup_weaken _ _ _ _).
  move: Hf2 => /(lookup_weaken _ _ _ _). naive_solver.
Qed.

Lemma r2a_f2i_incl_subset_r f2i ins1 ins2 :
  ins2 ⊆ ins1 →
  r2a_f2i_incl f2i ins1 -∗ r2a_f2i_incl f2i ins2.
Proof.
  iIntros (Hsub) "(%f2i_full&%&%&?)". iExists _. iFrame.
  iPureIntro. split!. set_solver.
Qed.

Lemma r2a_f2i_incl_subset_l f2i1 f2i2 ins :
  f2i2 ⊆ f2i1 →
  (∀ i f, i ∈ ins → f2i1 !! f = Some i → f2i2 !! f = Some i) →
  r2a_f2i_incl f2i1 ins -∗ r2a_f2i_incl f2i2 ins.
Proof.
  iIntros (Hsub Hins) "(%f2i_full&%Hf2i&%Hins2&?)". iExists _. iFrame.
  iPureIntro. split!. { by etrans. } naive_solver.
Qed.

Lemma r2a_f2i_incl_union f2i1 f2i2 ins1 ins2 :
  map_agree f2i1 f2i2 →
  (∀ i f, i ∈ ins1 → f2i2 !! f = Some i → f2i1 !! f = Some i) →
  (∀ i f, i ∈ ins2 → f2i1 !! f = Some i → f2i2 !! f = Some i) →
  r2a_f2i_incl (f2i1 ∪ f2i2) (ins1 ∪ ins2) ⊣⊢
  r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2.
Proof.
  move => Hagree Hi1 Hi2. iSplit.
  - iIntros "(%f2i_full&%Hf2i&%Hins&?)". iSplit; iExists _; iFrame; iPureIntro; split.
    + by etrans; [apply map_union_subseteq_l|].
    + move => f i ??. exploit (Hins f i); [set_solver|done|].
      move => /lookup_union_Some_raw. naive_solver.
    + etrans; [|done]. by apply map_union_subseteq_agree_r.
    + move => f i ??. exploit (Hins f i); [set_solver|done|].
      move => /lookup_union_Some_raw. naive_solver.
  - iIntros "[(%f2i_full&%Hf2i1&%Hins1&Hf2i1) (%&%Hf2i2&%Hins2&Hf2i2)]".
    iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst.
    iExists _. iFrame. iPureIntro. split.
    + by apply map_union_least.
    + move => ????. apply lookup_union_Some_agree; set_solver.
Qed.

Lemma r2a_f2i_incl_single f2i ins f i :
  f2i !! f = Some i →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅.
Proof.
  iIntros (?) "Hf".
  iApply r2a_f2i_incl_subset_l. 3: iApply (r2a_f2i_incl_subset_r with "[$]").
  - by apply map_singleton_subseteq_l.
  - set_solver.
  - set_solver.
Qed.

Lemma r2a_f2i_full_incl f2i f2i2 ins :
 r2a_f2i_full f2i -∗
 r2a_f2i_incl f2i2 ins -∗
 ⌜f2i2 ⊆ f2i⌝.
Proof.
  iIntros "Hf2i (%&%&?&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i Hf2i2") as %?.
  iPureIntro. naive_solver.
Qed.

Lemma r2a_f2i_full_singleton f2i f i ins :
 r2a_f2i_full f2i -∗
 r2a_f2i_incl {[f := i]} ins -∗
 ⌜f2i !! f = Some i⌝.
Proof.
  iIntros "Hf2i Hincl".
  iDestruct (r2a_f2i_full_incl with "[$] [$]") as %?.
  iPureIntro. apply: lookup_weaken; [|done]. by simplify_map_eq.
Qed.

Lemma r2a_f2i_full_to_singleton f2i f i :
 f2i !! f = Some i →
 r2a_f2i_full f2i -∗
 r2a_f2i_incl {[f := i]} ∅.
Proof.
  iIntros (?) "Hf2i".
  iExists _. iFrame. iPureIntro. split; [|done].
  by apply map_singleton_subseteq_l.
Qed.

Global Instance r2a_f2i_full_pers f2i :
  Persistent (r2a_f2i_full f2i).
Proof. apply _. Qed.

Global Instance r2a_f2i_incl_pers f2i ins :
  Persistent (r2a_f2i_incl f2i ins).
Proof. apply _. Qed.

Global Typeclasses Opaque r2a_f2i_incl r2a_f2i_full.

(** ** f2i_fns_ins_wf *)
Definition f2i_fns_ins_wf (f2i : gmap string Z) (fns : gset string) (ins : gset Z) : Prop :=
  map_Forall (λ f i, i ∈ ins ↔ f ∈ fns) f2i ∧ fns ⊆ dom f2i.

Lemma f2i_fns_ins_wf_in_ins f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  i ∈ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f ∈ fns⌝.
Proof.
  iIntros ([Hall ?] ?) "Hf2i Hf".
  iDestruct (r2a_f2i_incl_in_ins with "Hf2i Hf") as %?; [done|]. iPureIntro.
  by apply/Hall.
Qed.

Lemma f2i_fns_ins_wf_in_fns f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f ∈ fns →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜i ∈ ins⌝.
Proof.
  iIntros ([Hall Hsub] Hf) "Hf2i Hf".
  have /elem_of_dom[??] : f ∈ dom f2i by set_solver.
  iDestruct (r2a_f2i_incl_agree_f with "Hf2i Hf") as %?; [done|by simplify_map_eq|].
  iPureIntro. exploit Hall; [done|]. naive_solver.
Qed.

Lemma f2i_fns_ins_wf_not_in_ins f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  i ∉ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f ∉ fns⌝.
Proof.
  iIntros (? ?) "Hf2i Hf". iIntros (Hf).
  iDestruct (f2i_fns_ins_wf_in_fns f2i with "[$] [$]") as %?; done.
Qed.

Lemma f2i_fns_ins_wf_not_in_fns f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f ∉ fns →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜i ∉ ins⌝.
Proof.
  iIntros (? ?) "Hf2i Hf". iIntros (Hf).
  iDestruct (f2i_fns_ins_wf_in_ins f2i with "[$] [$]") as %?; done.
Qed.

Lemma f2i_fns_ins_wf_in_fns_pure f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f2i !! f = Some i →
  f ∈ fns →
  i ∈ ins.
Proof. unfold f2i_fns_ins_wf, map_Forall. naive_solver. Qed.

Lemma f2i_fns_ins_wf_in_ins_pure f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f2i !! f = Some i →
  i ∈ ins →
  f ∈ fns.
Proof. unfold f2i_fns_ins_wf, map_Forall. naive_solver. Qed.

(** * invariants *)
Definition r2a_val_rel (iv : val) (av : Z) : uPred rec_to_asmUR :=
  match iv with
  | ValNum z => ⌜av = z⌝
  | ValBool b => ⌜av = bool_to_Z b⌝
  | ValFn f => r2a_f2i_incl {[ f := av ]} ∅
  | ValLoc l => ∃ z, ⌜av = (z + l.2)%Z⌝ ∗ r2a_heap_shared l.1 z
  end.

Global Instance r2a_val_rel_pers iv av : Persistent (r2a_val_rel iv av).
Proof. destruct iv; apply _. Qed.

Definition GUARD_PAGE_SIZE : Z := 4096.

(* gp is lower end of guard page *)
Definition r2a_guard_page (gp : Z) : uPred rec_to_asmUR :=
  r2a_mem_map (map_seqZ gp (replicate (locked Z.to_nat GUARD_PAGE_SIZE) None)).

Definition r2a_mem_uninit (a : Z) (len : Z) : uPred rec_to_asmUR :=
  [∗ list] a ∈ seqZ a len, ∃ v, r2a_mem_constant a (Some v).

Definition r2a_mem_stack (sp : Z) (ssz : N) : uPred rec_to_asmUR :=
  r2a_guard_page (sp - Z.of_N ssz - GUARD_PAGE_SIZE) ∗
  r2a_mem_uninit (sp - Z.of_N ssz) (Z.of_N ssz).

Definition r2a_mem_inv (sp : Z) (ssz : N) (mem : gmap Z (option Z)) : uPred rec_to_asmUR :=
  r2a_mem_stack sp ssz ∗ r2a_mem_auth mem.

Definition r2a_heap_shared_agree (h : gmap loc val) (rh : gmap prov rec_to_asm_elem) : uPred rec_to_asmUR :=
  [∗ map] l↦v∈h,
    if rh !! l.1 is Some (R2AShared a) then
      ∃ av, r2a_val_rel v av ∗ r2a_mem_constant (a + l.2) (Some av)
    else
      True.

Definition r2a_heap_inv (h : heap_state) : uPred rec_to_asmUR :=
  ∃ rh, ⌜dom rh ⊆ h_provs h⌝ ∗ ⌜heap_preserved (r2a_rh_constant rh) h⌝ ∗
         ([∗ map] p↦a ∈ r2a_rh_shared rh, r2a_heap_shared p a) ∗
         r2a_heap_shared_agree (h_heap h) rh ∗ r2a_heap_auth rh.

Definition r2a_args (o : nat) (vs : list val) (rs : gmap string Z) : uPred rec_to_asmUR :=
  ([∗ list] i↦v∈vs, ∃ r,
      ⌜args_registers !! (o + i)%nat = Some r⌝ ∗
      r2a_val_rel v (rs !!! r)).

Definition r2a_args_pure (o : nat) (vs : list Z) (rs : gmap string Z) : Prop :=
  ∀ i v, vs !! i = Some v → ∃ r, args_registers !! (o + i)%nat = Some r ∧ rs !!! r = v.

Lemma r2a_mem_uninit_split n a l :
  0 ≤ n ≤ l →
  r2a_mem_uninit a l ⊣⊢ r2a_mem_uninit a n ∗ r2a_mem_uninit (a + n) (l - n).
Proof.
  move => ?. rewrite /r2a_mem_uninit.
  have {1} -> : l = (n + (l - n)) by lia.
  rewrite seqZ_app; [|lia..]. rewrite big_sepL_app. done.
Qed.

Lemma r2a_mem_uninit_alt1 a l :
  0 ≤ l →
  r2a_mem_uninit a l -∗ ∃ vs, ⌜length vs = Z.to_nat l⌝ ∗ r2a_mem_map (map_seqZ a (Some <$> vs)).
Proof.
  iIntros (Hl) "Hm". rewrite - {1}(Z2Nat.id l) //.
  iInduction (Z.to_nat l) as [|l'] "IH" forall (a).
  { iExists []. iSplit!. by rewrite /r2a_mem_map big_sepM_empty. }
  rewrite /r2a_mem_uninit Nat2Z.inj_succ seqZ_cons ?Z.pred_succ /=; [|lia].
  iDestruct "Hm" as "[[%v ?] ?]". iDestruct ("IH" with "[$]") as (vs ?) "Hm".
  iExists (v :: vs) => /=. iSplit!. rewrite /r2a_mem_map big_sepM_insert; [by iFrame|].
  apply lookup_map_seqZ_None. lia.
Qed.

Lemma r2a_mem_uninit_alt2 a vs :
  r2a_mem_map (map_seqZ a (Some <$> vs)) -∗
  r2a_mem_uninit a (length vs).
Proof.
  iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (a); csimpl.
  { rewrite /r2a_mem_uninit /=. done. }
  rewrite /r2a_mem_map big_sepM_insert; [|apply lookup_map_seqZ_None; lia].
  iDestruct "Hvs" as "[??]". iDestruct ("IH" with "[$]") as "?".
  rewrite /r2a_mem_uninit /= Nat2Z.inj_succ (seqZ_cons a) ?Z.pred_succ /=; [|lia]. iFrame.
  by iExists _.
Qed.

Lemma r2a_heap_shared_agree_union h1 h2 rh:
  h1 ##ₘ h2 →
  r2a_heap_shared_agree (h1 ∪ h2) rh ⊣⊢ r2a_heap_shared_agree h1 rh ∗ r2a_heap_shared_agree h2 rh.
Proof. apply big_sepM_union. Qed.

Lemma r2a_heap_shared_agree_impl h1 h2 rh1 rh2:
  (∀ l v a, h2 !! l = Some v → rh2 !! l.1 = Some (R2AShared a) →
            h1 !! l = Some v ∧ rh1 !! l.1 = Some (R2AShared a)) →
  r2a_heap_shared_agree h1 rh1 -∗
  r2a_heap_shared_agree h2 rh2.
Proof.
  iIntros (Himpl) "Hag".
  iApply (big_sepM_impl_strong' with "[$]").
  iIntros "!>" (k ?) "H1". iIntros (?). destruct (rh2 !! k.1) as [[]|] eqn:? => //.
  have [??]:= Himpl _ _ _ ltac:(done) ltac:(done). by simplify_map_eq.
Qed.

Lemma r2a_guard_page_lookup a sp ssz mem :
  sp - Z.of_N ssz - GUARD_PAGE_SIZE ≤ a < sp - Z.of_N ssz →
  r2a_mem_inv sp ssz mem -∗
  ⌜mem !! a = Some None⌝.
Proof.
  iIntros (?) "((Hgp&?)&Hauth)". rewrite /r2a_guard_page.
  iDestruct (r2a_mem_lookup_big' with "[$] [$]") as %Hsub.
  iPureIntro. apply: lookup_weaken; [|done]. apply lookup_map_seqZ_Some. split; [lia|].
  apply lookup_replicate. split!. unlock. lia.
Qed.

Lemma r2a_mem_lookup a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_constant a v -∗
  ⌜mem !! a = Some v⌝.
Proof.
  iIntros "((?&?)&Hauth) Hconst".
  by iDestruct (r2a_mem_lookup' with "Hauth Hconst") as %?.
Qed.

Lemma r2a_mem_lookup_big sp ssz m mem :
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_map m -∗
  ⌜m ⊆ mem⌝.
Proof.
  iIntros "((?&?)&Hauth) Hconst".
  by iDestruct (r2a_mem_lookup_big' with "Hauth Hconst") as %?.
Qed.

Lemma r2a_mem_range a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_constant a (Some v) -∗
  ⌜¬ (sp - Z.of_N ssz ≤ a < sp)⌝.
Proof.
  iIntros "Hinv Hconst" (?).
  iDestruct (r2a_mem_lookup with "[$] [$]") as %?.
  destruct (decide (sp - Z.of_N ssz ≤ a)).
  2: { iDestruct (r2a_guard_page_lookup a with "[$]") as %?; [lia|]. simplify_eq. }
  iDestruct "Hinv" as "((?&Hsp)&?)".
  iDestruct (big_sepL_lookup _ _ (Z.to_nat (a - (sp - Z.of_N ssz))) a with "Hsp") as (?) "?".
  - apply lookup_seqZ. lia.
  - iDestruct (r2a_mem_constant_excl with "[$] [$]") as %[].
Qed.

Lemma r2a_mem_exists n sp ssz mem :
  0 < n ≤ GUARD_PAGE_SIZE →
  r2a_mem_inv sp ssz mem -∗
  ⌜∃ v, mem !! (sp - n) = Some v⌝.
Proof.
  iIntros (?) "Hinv".
  destruct (decide (n ≤ Z.of_N ssz)).
  - iDestruct "Hinv" as "((?&Hsp)&?)".
    iDestruct (big_sepL_lookup _ _ (Z.to_nat (Z.of_N ssz - n)) (sp - n) with "Hsp") as (?) "?".
    * apply lookup_seqZ. lia.
    * iDestruct (r2a_mem_lookup' with "[$] [$]") as %?. iSplit!.
  - iDestruct (r2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + iSplit!.
Qed.

Lemma r2a_mem_alloc n sp ssz mem v :
  mem !! (sp - n) = Some (Some v) →
  0 ≤ n ≤ GUARD_PAGE_SIZE →
  r2a_mem_inv sp ssz mem ==∗ ⌜n ≤ Z.of_N ssz⌝ ∗ r2a_mem_inv (sp - n) (ssz - Z.to_N n) mem ∗ r2a_mem_uninit (sp - n) n.
Proof.
  iIntros (? ?) "Hinv". iModIntro.
  destruct (decide (n ≤ Z.of_N ssz)).
  - iDestruct "Hinv" as "((?&?)&?)".
    rewrite (r2a_mem_uninit_split (Z.of_N ssz - n)). 2: lia.
    iDestruct!.
    have ->: (sp - Z.of_N ssz + (Z.of_N ssz - n)) = (sp - n) by lia.
    have ->: (Z.of_N ssz - (Z.of_N ssz - n)) = n by lia. iSplit!. iFrame.
    unfold r2a_mem_stack.
    have -> : (sp - n - Z.of_N (ssz - Z.to_N n) - GUARD_PAGE_SIZE) = (sp - Z.of_N ssz - GUARD_PAGE_SIZE) by lia.
    have -> : (sp - n - Z.of_N (ssz - Z.to_N n)) = (sp - Z.of_N ssz) by lia.
    have -> : (Z.of_N (ssz - Z.to_N n)) = (Z.of_N ssz - n) by lia.
    iFrame.
  - iDestruct (r2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + simplify_eq.
Qed.

Lemma r2a_mem_update v' a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_constant a v ==∗
  r2a_mem_inv sp ssz (<[a := Some v']> mem) ∗ r2a_mem_constant a (Some v').
Proof.
  iDestruct 1 as "((?&?)&Hauth)".
  iIntros "Hconst".
  iDestruct (r2a_mem_lookup' with "[$] [$]") as %?.
  iMod (r2a_mem_update' with "[$]") as "[? $]". iModIntro.
  by iFrame.
Qed.

Lemma r2a_mem_update_big sp ssz mem mo mo' :
  dom mo = dom mo' →
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_map mo ==∗
  r2a_mem_map mo' ∗ r2a_mem_inv sp ssz (mo' ∪ mem).
Proof.
  iIntros (Hdom) "[$ Hmem] Hconst".
  iMod (r2a_mem_delete_big' with "[$] [$]").
  iMod (r2a_mem_alloc_big' with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???. rewrite !lookup_difference_Some -not_elem_of_dom Hdom not_elem_of_dom.  naive_solver. }
  iModIntro.
  by rewrite (map_difference_eq_dom_L _ mo mo') // -map_difference_union_r.
Qed.

Lemma r2a_mem_delete n mem sp ssz:
  0 ≤ n →
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_uninit sp n ==∗
  r2a_mem_inv (sp + n) (ssz + Z.to_N n) mem.
Proof.
  move => ?.
  iDestruct 1 as "((?&?)&Hauth)".
  iIntros "Huninit". iModIntro. iFrame.
  rewrite /r2a_mem_stack.
  have -> : (sp + n - Z.of_N (ssz + Z.to_N n)) = sp - Z.of_N ssz by lia. iFrame.
  have -> : (Z.of_N (ssz + Z.to_N n)) = Z.of_N ssz + n by lia.
  iApply (r2a_mem_uninit_split (Z.of_N ssz)); [lia|]. iFrame.
  have -> : (sp - Z.of_N ssz + Z.of_N ssz) = sp by lia.
  have -> : (Z.of_N ssz + n - Z.of_N ssz) = n by lia.
  done.
Qed.

Lemma r2a_mem_delete_big adrs mem sp sp' ssz:
  sp ≤ sp' →
  Forall (λ a, sp ≤ a < sp') adrs →
  length adrs = Z.to_nat (sp' - sp) →
  r2a_mem_inv sp ssz mem -∗
  ([∗ list] a∈adrs, ∃ v, r2a_mem_constant a (Some v)) ==∗
  r2a_mem_inv sp' (ssz + Z.to_N (sp' - sp)) mem.
Proof.
  iIntros (? Hall ?) "Hinv Ha".
  iAssert ⌜NoDup adrs⌝%I as %?. {
    rewrite NoDup_alt. iIntros (a1 a2 ???).
    destruct (decide (a1 = a2)) => //.
    rewrite (big_sepL_delete _ _ a1); [|done].
    rewrite (big_sepL_delete _ _ a2); [|done].
    iDestruct!. case_decide => //. iDestruct!.
    iDestruct (r2a_mem_constant_excl with "[$] [$]") as %[].
  }
  iAssert ⌜∀ a, a ∈ adrs → a ∈ seqZ sp (sp' - sp)⌝%I as %Hsub%NoDup_submseteq => //. {
    iIntros (??).
    iDestruct (big_sepL_elem_of with "[$]") as (?) "?"; [done|].
    iDestruct (r2a_mem_range with "[$] [$]") as %?.
    iPureIntro. apply elem_of_seqZ. move: Hall => /Forall_forall. naive_solver lia.
  }
  move: Hsub => /submseteq_length_Permutation ->. 2: { rewrite seqZ_length. lia. }
  have [n [-> ->]]: ∃ n : nat, sp' - sp = Z.of_nat n ∧ sp' = sp + Z.of_nat n.
  { eexists (Z.to_nat (sp' - sp)). lia. }
  iApply (r2a_mem_delete with "[$] [$]"). lia.
Qed.

Lemma r2a_mem_swap_stack sp1 ssz1 sp2 ssz2 mem:
  r2a_mem_inv sp1 ssz1 mem -∗
  r2a_mem_stack sp2 ssz2 -∗
  r2a_mem_inv sp2 ssz2 mem ∗ r2a_mem_stack sp1 ssz1.
Proof. iIntros "[??] ?". iFrame. Qed.

Lemma r2a_heap_alloc h l n:
  heap_is_fresh h l →
  r2a_heap_inv h ==∗
  r2a_heap_inv (heap_alloc h l n) ∗ r2a_heap_constant l.1 (h_block (heap_alloc h l n) l.1).
Proof.
  iIntros ([Hl ?]).
  iDestruct 1 as (? Hdom Hc) "[Hsh [Hs Hauth]]".
  iMod (r2a_heap_alloc' with "Hauth") as "[? $]".
  { apply not_elem_of_dom. by apply: not_elem_of_weaken; [|done]. }
  iModIntro. iExists _. iFrame. rewrite r2a_rh_shared_insert_const.
  2: { move => ?. contradict Hl. apply Hdom. by apply elem_of_dom. }
  iFrame. repeat iSplit.
  - iPureIntro. rewrite dom_insert_L. set_solver.
  - iPureIntro. rewrite r2a_rh_constant_insert.
    eapply heap_preserved_insert_const.
    eapply heap_preserved_alloc. 2: apply lookup_delete.
    eapply heap_preserved_mono; [done| apply delete_subseteq].
  - rewrite /r2a_heap_shared_agree big_sepM_union. 2: {
      apply map_disjoint_list_to_map_l, Forall_forall => -[[??]?] /elem_of_list_fmap[?[??]]. simplify_eq/=.
      apply eq_None_not_Some => /heap_wf. done.
    }
    iSplitR.
    + iApply big_sepM_intro. iIntros "!>" (?? (?&?&?)%elem_of_list_to_map_2%elem_of_list_fmap). by simplify_map_eq.
    + iApply (big_sepM_impl with "Hs"). iIntros "!>" (k??) "?".
      rewrite lookup_insert_ne //. contradict Hl. rewrite Hl. by apply heap_wf.
Qed.

Lemma r2a_heap_update h l v b:
  r2a_heap_inv h -∗
  r2a_heap_constant l.1 b ==∗
  r2a_heap_inv (heap_update h l v) ∗ r2a_heap_constant l.1 (h_block (heap_update h l v) l.1).
Proof.
  iDestruct 1 as (? Hdom Hc) "[Hsh [Hs Hauth]]". iIntros "Hc".
  iDestruct (r2a_heap_lookup' with "[$] [$]") as %?.
  iMod (r2a_heap_update' with "[$Hauth $Hc]") as "[? $]".
  iModIntro. iExists _. iFrame. rewrite r2a_rh_shared_insert_const.
  2: { move => ??. simplify_map_eq. } iFrame. repeat iSplit.
  - iPureIntro. rewrite dom_insert_L. etrans; [|done]. apply union_least; [|done].
    apply singleton_subseteq_l. by apply elem_of_dom.
  - iPureIntro. rewrite r2a_rh_constant_insert.
    eapply heap_preserved_insert_const.
    eapply heap_preserved_update. 2: apply lookup_delete.
    eapply heap_preserved_mono; [done| apply delete_subseteq].
  - rewrite /r2a_heap_shared_agree /= big_sepM_alter.
    iApply (big_sepM_impl with "Hs"). iIntros "!>" (k ??) "?". case_bool_decide; subst; simplify_map_eq => //.
    by destruct (decide (k.1 = l.1)) as [->|]; simplify_map_eq.
Qed.

Lemma r2a_heap_free h l b:
  r2a_heap_inv h -∗
  r2a_heap_constant l.1 b ==∗
  r2a_heap_inv (heap_free h l).
Proof.
  iDestruct 1 as (? Hdom Hc) "[Hsh [Hs Hauth]]". iIntros "Hc".
  iDestruct (r2a_heap_lookup' with "[$] [$]") as %?.
  iMod (r2a_heap_free' with "[$Hauth $Hc]") as "?".
  iModIntro. iExists _. iFrame. repeat iSplit.
  - iPureIntro. rewrite dom_delete_L. set_solver.
  - iPureIntro. rewrite r2a_rh_constant_delete.
    eapply heap_preserved_free. 2: apply lookup_delete.
    eapply heap_preserved_mono; [done| apply delete_subseteq].
  - rewrite r2a_rh_shared_delete. by iApply big_sepM_delete_2.
  - rewrite /r2a_heap_shared_agree big_sepM_filter.
    iApply (big_sepM_impl with "Hs"). iIntros "!>" (???) "?". iIntros (?).
    by rewrite lookup_delete_ne.
Qed.

Lemma r2a_heap_lookup_shared h l v z mem ss ssz:
  h_heap h !! l = Some v →
  r2a_heap_inv h -∗
  r2a_mem_inv ss ssz mem -∗
  r2a_heap_shared l.1 z -∗
  ∃ av, ⌜mem !! (z + l.2)%Z = Some (Some av)⌝ ∗ r2a_val_rel v av.
Proof.
  iIntros (?).
  iDestruct 1 as (? ? Hag) "[Hsh [Hs Hauth]]".
  iIntros "Hmem Hl".
  iDestruct (r2a_heap_shared_lookup' with "[$] [$]") as %?.
  iDestruct (big_sepM_lookup with "Hs") as "Hv"; [done|]. simplify_map_eq.
  iDestruct "Hv" as (?) "[??]".
  iDestruct (r2a_mem_lookup with "[$] [$]") as %?. subst.
  iSplit!.
Qed.

Lemma r2a_heap_alloc_shared h l a n:
  heap_is_fresh h l →
  r2a_heap_inv h -∗
  ([∗ list] a'∈seqZ a n, r2a_mem_constant a' (Some 0)) ==∗
  r2a_heap_shared l.1 a ∗ r2a_heap_inv (heap_alloc h l n).
Proof.
  iIntros (Hf) "Hinv Ha".
  iMod (r2a_heap_alloc with "Hinv") as "[Hinv Hl]"; [done|].
  destruct Hf as [Hne ?].
  iDestruct "Hinv" as (???) "[Hsh [Hag Hauth]]".
  iMod (r2a_heap_to_shared' with "[$]") as "[? #Hs1]". iModIntro. iFrame "Hs1".
  iExists _. iFrame. iSplit!.
  - rewrite dom_insert_L. set_solver.
  - move => ?? /r2a_rh_constant_Some/lookup_insert_Some[[??]//|[??]].
    apply H0. by apply r2a_rh_constant_Some.
  - rewrite r2a_rh_shared_insert. by iApply big_sepM_insert_2.
  - rewrite /r2a_heap_shared_agree /= !big_sepM_union.
    2,3: apply map_disjoint_list_to_map_l, Forall_forall => ? /elem_of_list_fmap[?[??]];
         simplify_eq/=; apply eq_None_not_Some => /heap_wf; naive_solver.
    iDestruct "Hag" as "[_ Hh]".
    iSplitR "Hh".
    + rewrite !big_sepM_list_to_map.
      2: { rewrite -list_fmap_compose. apply NoDup_fmap; [move => ?? /= ?;simplify_eq; lia|]. apply NoDup_seqZ. }
      iEval rewrite big_sepL_fmap. simplify_map_eq/=.
      have ->: a = a + 0 by lia.
      rewrite -(fmap_add_seqZ a 0) big_sepL_fmap.
      iApply (big_sepL_impl with "[$]"). iIntros "!>" (? o ?) "?". iSplit!.
      by have -> : (a + 0 + (l.2 + o)) = a + o by lia.
    + iApply (big_sepM_impl with "Hh"). iIntros "!>" (???) "?".
      rewrite lookup_insert_ne; [done|]. contradict Hne. rewrite Hne. by apply heap_wf.
Qed.

Lemma r2a_heap_free_shared h l a n:
  l.2 = 0 →
  heap_range h l n →
  r2a_heap_inv h -∗
  r2a_heap_shared l.1 a ==∗
  r2a_mem_uninit a n ∗ r2a_heap_inv (heap_free h l).
Proof.
  iIntros (Hl2 Hr).
  iDestruct 1 as (? Hdom Hc) "[Hsh [Hs Hauth]]". iIntros "Hl".
  iDestruct (r2a_heap_shared_lookup' with "[$] [$]") as %Hl.
  iModIntro.
  rewrite /r2a_heap_shared_agree -(map_filter_union_complement (λ '(l', _), l'.1 ≠ l.1) (h_heap h)).
  rewrite big_sepM_union; [|apply map_disjoint_filter_complement].
  iDestruct "Hs" as "[Hs Ha]". iSplitL "Ha".
  - iApply big_sepM_map_seq_0.
    have ?: Inj eq eq (λ n : nat, l +ₗ n) by move => ???; simplify_eq; lia.
    iApply (big_sepM_kmap_intro (λ n : nat, l +ₗ n)).
    iApply (big_sepM_impl_strong' with "[$]").
    iIntros "!>" (??) "Hm". iIntros ([i [?[?[??]%lookup_seqZ]%lookup_map_seq_Some]]%lookup_kmap_Some); [|done].
    simplify_eq/=. rewrite map_lookup_filter_true; [|naive_solver].
    case_match. 2: { exfalso. eapply not_eq_None_Some; [|done]. apply Hr; [done|]. simpl. lia. } simplify_map_eq.
    iDestruct!. iSplit!; [done|]. by rewrite Nat.sub_0_r Hl2.
  - iExists _. iFrame. iPureIntro. split; [done|].
    apply heap_preserved_free; [done|].
    apply eq_None_ne_Some_2 => ?. rewrite r2a_rh_constant_Some. by rewrite Hl.
Qed.

Lemma r2a_heap_free_list_shared h ls h' adrs:
  heap_free_list ls h h' →
  Forall (λ l, l.2 = 0) ls.*1 →
  r2a_heap_inv h -∗
  ([∗ list] l;a∈ls.*1;adrs, r2a_heap_shared l.1 a) ==∗
  ([∗ list] a∈mjoin (zip_with (λ a n, seqZ a n) adrs ls.*2), ∃ v, r2a_mem_constant a (Some v)) ∗
    r2a_heap_inv h'.
Proof.
  elim: ls h h' adrs => /=.
  { iIntros (??? -> ?) "? Hs". iDestruct (big_sepL2_nil_inv_l with "Hs") as %->. iModIntro. by iFrame. }
  move => [l n] ls IH h h' [|a adrs]; try by [iIntros]; csimpl => -[??] /Forall_cons[??]; iIntros "Hh [Hl Hs]".
  iMod (r2a_heap_free_shared with "Hh Hl") as "[$ ?]"; [done..|].
  by iApply (IH with "[$]").
Qed.

Lemma r2a_heap_update_shared h l v z mem ss av ssz:
  heap_alive h l →
  r2a_heap_inv h -∗
  r2a_mem_inv ss ssz mem -∗
  r2a_heap_shared l.1 z -∗
  r2a_val_rel v av ==∗
  r2a_heap_inv (heap_update h l v) ∗ r2a_mem_inv ss ssz (<[z + l.2 := Some av]>mem).
Proof.
  iIntros ([??]).
  iDestruct 1 as (? Hdom Hag) "[Hsh [Hs Hauth]]".
  iIntros "Hmem Hl Hv".
  iDestruct (r2a_heap_shared_lookup' with "[$] [$]") as %Hl.
  rewrite /r2a_heap_shared_agree (big_sepM_delete _ (h_heap h)); [|done]. simplify_map_eq.
  iDestruct "Hs" as "[[% [??]] Hs]".
  iMod (r2a_mem_update with "[$] [$]") as "[$ ?]". iModIntro.
  iExists _. iFrame. repeat iSplit; [iPureIntro..|].
  - done.
  - apply heap_preserved_update; [done|].
    apply eq_None_ne_Some_2 => ?. rewrite r2a_rh_constant_Some. by rewrite Hl.
  - rewrite /r2a_heap_shared_agree/= (big_sepM_delete _ (alter (λ _, v) _ _) l); [|by simplify_map_eq].
    simplify_map_eq. rewrite delete_alter. iFrame. iExists _. iFrame.
Qed.

Lemma r2a_heap_inv_add_provs h ps :
  r2a_heap_inv h -∗
  r2a_heap_inv (heap_add_provs h ps).
Proof.
  iDestruct 1 as (???) "[??]". iExists _. iFrame.
  iPureIntro. split; [|done]. set_solver.
Qed.

Lemma r2a_res_init mem f2i:
  satisfiable (r2a_mem_auth mem ∗ ([∗ map] a↦v∈mem, r2a_mem_constant a v) ∗ r2a_heap_inv ∅
                 ∗ r2a_f2i_full f2i).
Proof.
  apply: (satisfiable_init (r2a_mem_inj (gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)) ⋅
                            r2a_heap_inj (gmap_view_auth (DfracOwn 1) (to_agree <$> ∅)) ⋅
                            r2a_f2i_inj f2i)). {
    split; [split|] => /=.
    1,2: rewrite ?left_id ?right_id; apply gmap_view_auth_valid.
    (* TODO: rewrite ?left_id ?right_id. here gives Error: Anomaly "conversion was given unreduced term (FLambda)." *)
    1: done. }
  rewrite uPred.ownM_op. iIntros "[[Hmem Hh] Hf2i]".
  iMod (r2a_mem_alloc_big' with "[$]") as "[? $]"; [solve_map_disjoint|]. rewrite right_id_L.
  unfold r2a_f2i_full. iFrame.
  iModIntro. iExists _. iFrame. iSplit!. by rewrite r2a_rh_shared_empty.
Qed.

Definition r2a_mem_stack_mem (sp : Z) (ssz : N) : gmap Z (option Z) :=
  map_seqZ (sp - Z.of_N ssz - GUARD_PAGE_SIZE) (replicate (locked Z.to_nat GUARD_PAGE_SIZE) None) ∪
  map_seqZ (sp - Z.of_N ssz) (Some <$> replicate (N.to_nat $ ssz) 0).

Lemma r2a_mem_stack_init ssz sp:
  r2a_mem_map (r2a_mem_stack_mem sp ssz) -∗
  r2a_mem_stack sp ssz.
Proof.
  iIntros "Hm". rewrite /r2a_mem_map/r2a_mem_stack_mem big_sepM_union.
  2: { apply map_disjoint_spec => ???. rewrite !lookup_map_seqZ_Some.
       rewrite list_lookup_fmap fmap_Some. setoid_rewrite lookup_replicate. unlock. lia. }
  iDestruct "Hm" as "[$ ?]".
  have {3} ->: (Z.of_N ssz) = length $ replicate (N.to_nat ssz) 0.
  { rewrite replicate_length. lia. }
  by iApply r2a_mem_uninit_alt2.
Qed.

Lemma r2a_args_nil o rs:
  r2a_args o [] rs ⊣⊢ True.
Proof. done. Qed.

Lemma r2a_args_cons1 o v vs rs:
  r2a_args o (v::vs) rs ⊣⊢ (∃ r, ⌜args_registers !! o = Some r⌝ ∗ r2a_val_rel v (rs !!! r)) ∗ r2a_args (S o) vs rs.
Proof.
  rewrite /r2a_args. setoid_rewrite Nat.add_succ_l. setoid_rewrite <-Nat.add_succ_r => /=.
  f_equiv. setoid_rewrite Nat.add_0_r. iSplit; iIntros!; iSplit!.
Qed.

Lemma r2a_args_cons o v vs rs r:
  args_registers !! o = Some r →
  r2a_args o (v::vs) rs ⊣⊢ r2a_val_rel v (rs !!! r) ∗ r2a_args (S o) vs rs.
Proof. move => ?. rewrite r2a_args_cons1. iSplit; iIntros!; iSplit!. Qed.

Lemma r2a_args_pure_mono o avs rs rs':
  map_preserved args_registers rs rs' →
  r2a_args_pure o avs rs →
  r2a_args_pure o avs rs'.
Proof.
  move => Hrs Ha ???. have [?[??]]:= Ha _ _ ltac:(done). split!.
  etrans; [|done].
  symmetry. apply: Hrs. by apply: elem_of_list_lookup_2.
Qed.

Lemma r2a_args_mono o vs rs rs':
  map_preserved (drop o args_registers) rs rs' →
  r2a_args o vs rs -∗
  r2a_args o vs rs'.
Proof.
  iIntros (Hpre) "Hargs". iApply (big_sepL_impl with "Hargs").
  iIntros "!>" (???) "[% [% ?]]". iExists _. iFrame. iSplit; [done|].
  rewrite ->Hpre; [done|].
  apply elem_of_list_lookup. setoid_rewrite lookup_drop. naive_solver.
Qed.

Lemma r2a_args_intro o vs avs rs:
  r2a_args_pure o avs rs →
  ([∗ list] v;av∈vs;avs, r2a_val_rel v av) -∗
  r2a_args o vs rs.
Proof.
  iIntros (Hpure) "Hvs".
  iInduction vs as [|v vs] "IH" forall (avs o Hpure). { by rewrite r2a_args_nil. }
  iDestruct (big_sepL2_cons_inv_l with "Hvs") as (???) "[??]". simplify_eq.
  have [?[]]:= Hpure 0%nat _ ltac:(done). rewrite Nat.add_0_r => ??. simplify_eq.
  rewrite r2a_args_cons; [|done].
  iDestruct ("IH" with "[%] [$]") as "$". 2: by iSplit!.
  move => ???. rewrite Nat.add_succ_l -Nat.add_succ_r. by apply Hpure.
Qed.

Lemma r2a_args_elim o vs rs:
  r2a_args o vs rs -∗
  ∃ avs, ⌜r2a_args_pure o avs rs⌝ ∗ ([∗ list] v;av∈vs;avs, r2a_val_rel v av).
Proof.
  iIntros "Hvs".
  iInduction vs as [|v vs] "IH" forall (o). { iExists []. by iSplit!. }
  iDestruct (r2a_args_cons1 with "Hvs") as "[??]". iDestruct!.
  iDestruct ("IH" with "[$]") as (? Hpure) "?".
  iExists (_::_). iSplit!; [|done..].
  move => i ? /lookup_cons_Some[[??]|[??]]; simplify_eq.
  - rewrite Nat.add_0_r. split!.
  - destruct i; [lia|]. rewrite Nat.add_succ_r -Nat.add_succ_l . apply Hpure.
    simplify_eq/=. rewrite ->Nat.sub_0_r in *. done.
Qed.

(** * Definition of [rec_to_asm] *)
Record rec_to_asm_stack_item := R2AI {
  r2as_extern : bool;
  r2as_ret : Z;
  r2as_regs : gmap string Z;
}.
Add Printing Constructor rec_to_asm_stack_item.

Record rec_to_asm_state := R2A {
  r2a_calls : list rec_to_asm_stack_item;
  r2a_last_regs : gmap string Z;
}.
Add Printing Constructor rec_to_asm_state.

Definition rec_to_asm_pre (ins : gset Z)
 (e : asm_event) (s : rec_to_asm_state) :
 prepost (rec_event * rec_to_asm_state) rec_to_asmUR :=
  match e with
  | (i, EAJump rs mem) =>
    (* env chooses if this is a function call or return *)
    pp_quant $ λ b : bool,
    pp_prop (i = Incoming) $
    pp_quant $ λ h,
    pp_quant $ λ ssz,
    pp_quant $ λ vs,
    pp_quant $ λ avs,
    pp_star (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv h ∗ [∗ list] v;av∈vs;avs, r2a_val_rel v av) $
    if b then
      (* env chooses function name *)
      pp_quant $ λ f,
      (* env chooses arguments *)
      pp_prop (r2a_args_pure 0 avs rs) $
      (* env proves that pc is in ins *)
      pp_prop  (rs !!! "PC" ∈ ins) $
      (* env proves it calls the right address *)
      pp_star (r2a_f2i_incl {[ f := rs !!! "PC" ]} ∅) $
      (* env proves that ret is not in ins *)
      pp_prop (rs !!! "R30" ∉ ins) $
      (* track the registers and return address (false means ret belongs to env) *)
      pp_end ((i, ERCall f vs h), R2A ((R2AI false (rs !!! "R30") rs)::s.(r2a_calls)) rs)
    else
      (* env chooses return value *)
      pp_quant $ λ v,
      pp_quant $ λ av,
      pp_prop (vs = [v] ∧ avs = [av]) $
      (* env chooses old registers *)
      pp_quant $ λ rsold,
      (* env chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (true means pc belongs to the program) *)
      pp_prop (s.(r2a_calls) = (R2AI true (rs !!! "PC") rsold)::cs') $
      (* env proves that rs is updated correctly *)
      pp_prop (r2a_regs_ret rs rsold av) $
      pp_end ((i, ERReturn v h), R2A cs' rs)
  | _ => pp_prop False $ pp_quant $ λ e, pp_end e
  end.

Definition rec_to_asm_post (ins : gset Z)
           (e : rec_event) (s : rec_to_asm_state) : prepost (asm_event * rec_to_asm_state) rec_to_asmUR :=
  pp_prop (e.1 = Outgoing) $
  pp_quant $ λ rs,
  pp_quant $ λ mem,
  pp_quant $ λ ssz,
  pp_quant $ λ avs,
  pp_star (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv (heap_of_event e.2)  ∗
             [∗ list] v;av∈(vals_of_event e.2);avs, r2a_val_rel v av) $
  match e with
  | (i, ERCall f vs h) =>
      (* program chooses new physical blocks *)
      pp_prop (r2a_args_pure 0 avs rs) $
      (* program proves that this instruction is external *)
      pp_prop (rs !!! "PC" ∉ ins) $
      (* program proves that the address is correct *)
      pp_star (r2a_f2i_incl {[ f := rs !!! "PC" ]} ∅) $
      (* program proves that ret is in ins *)
      pp_prop (rs !!! "R30" ∈ ins) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(r2a_last_regs) rs) $
      (* track the registers and return address (true means ret belongs to program) *)
      pp_end ((Outgoing, EAJump rs mem), (R2A ((R2AI true (rs !!! "R30") rs)::s.(r2a_calls)) s.(r2a_last_regs)))
  | (i, ERReturn v h) =>
      (* program chooses old registers *)
      pp_quant $ λ rsold,
      (* program chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (false means pc belongs to the env) *)
      pp_prop (s.(r2a_calls) = (R2AI false (rs !!! "PC") rsold)::cs') $
      (* prog proves that rs is updated correctly *)
      pp_prop (r2a_regs_ret rs rsold (avs !!! 0%nat)) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(r2a_last_regs) rs) $
      pp_end ((Outgoing, EAJump rs mem), (R2A cs' s.(r2a_last_regs)))
  end.

Definition rec_to_asm_trans (ins : gset Z) (f2i : gmap string Z)
           (m : mod_trans rec_event) : mod_trans asm_event :=
  prepost_trans (rec_to_asm_pre ins) (rec_to_asm_post ins) m.

Definition rec_to_asm (ins : gset Z) (f2i : gmap string Z) (mo : gmap Z (option Z))
           (m : module rec_event) : module asm_event :=
  Mod (rec_to_asm_trans ins f2i m.(m_trans))
      (SMFilter, m.(m_init), (PPOutside, R2A [] ∅, uPred_shrink (r2a_mem_map mo ∗ r2a_f2i_incl f2i ins )%I)).

Lemma rec_to_asm_trefines mo m m' ins f2i `{!VisNoAng m.(m_trans)}:
  trefines m m' →
  trefines (rec_to_asm ins f2i mo m) (rec_to_asm ins f2i mo m').
Proof. move => ?. by apply: prepost_mod_trefines. Qed.

(** * Horizontal compositionality of [rec_to_asm] *)
Inductive rec_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  seq_product_case → list seq_product_case →
  list rec_to_asm_stack_item → list rec_to_asm_stack_item → list rec_to_asm_stack_item →
 Prop :=
| RAC_nil :
  rec_to_asm_combine_stacks ins1 ins2 None [] [] [] []
| RAC_cons s s' ret rs ics cs cs1 cs2 cs' cs1' cs2':
  rec_to_asm_combine_stacks ins1 ins2 s ics cs cs1 cs2 →
  s ≠ s' →
  cs' = (if s is None then (R2AI false ret rs) :: cs else if s' is None then (R2AI true ret rs) :: cs else cs) →
  cs1' = (if s is Some SPLeft then (R2AI true ret rs) :: cs1 else if s' is Some SPLeft then (R2AI false ret rs) :: cs1 else cs1) →
  cs2' = (if s is Some SPRight then (R2AI true ret rs) :: cs2 else if s' is Some SPRight then (R2AI false ret rs) :: cs2 else cs2) →
  match s with
  | None => ret ∉ ins1 ∧ ret ∉ ins2
  | Some SPLeft => ret ∈ ins1
  | Some SPRight => ret ∈ ins2
  end →
  rec_to_asm_combine_stacks ins1 ins2 s' (s :: ics) cs' cs1' cs2'.

Local Ltac go := repeat match goal with | x : asm_ev |- _ => destruct x end;
                 destruct!/=; destruct!/=.
Local Ltac go_i := tstep_i; intros; go.
Local Ltac go_s := tstep_s; go.

Local Ltac r2a_split_go :=
  idtac; (* this idtac is important as otherwise the match is evaluated eagerly *)
  match goal with
  | |- r2a_regs_ret _ _ _ => eassumption
  | |- r2a_args_pure _ _ _ => eassumption
  | |- map_scramble ?r ?a ?b =>
      assert_fails (has_evar r); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  end.
Local Tactic Notation "r2a_split!" := split_tac ltac:(r2a_split_go).

Lemma rec_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 mo1 mo2 m1 m2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  mo1 ##ₘ mo2 →
  f2i_fns_ins_wf f2i1 fns1 ins1 →
  f2i_fns_ins_wf f2i2 fns2 ins2 →
  map_agree f2i1 f2i2 →
  map_Forall (λ f i, i ∉ ins2 ∨ f2i2 !! f = Some i) f2i1 →
  map_Forall (λ f i, i ∉ ins1 ∨ f2i1 !! f = Some i) f2i2 →
  trefines (asm_link ins1 ins2 (rec_to_asm ins1 f2i1 mo1 m1) (rec_to_asm ins2 f2i2 mo2 m2))
           (rec_to_asm (ins1 ∪ ins2) (f2i1 ∪ f2i2) (mo1 ∪ mo2) (rec_link fns1 fns2 m1 m2)).
Proof.
  move => Hdisji Hdisjf Hdisjm Hwf1 Hwf2 /map_agree_spec Hagree Hincl1 Hincl2.
  unshelve apply: prepost_link. { exact (λ ips '(R2A cs1 lr1) '(R2A cs2 lr2) '(R2A cs lr) x1 x2 x s ics,
  rec_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧ s = None ∧
  ((ips = None ∧ (x ⊣⊢ x1 ∗ x2 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)) ∨
  ((ips = Some SPLeft ∧ x1 = (x ∗ x2 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)%I
      ∧ map_scramble touched_registers lr lr1) ∨
  (ips = Some SPRight ∧ x2 = (x ∗ x1 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)%I
      ∧ map_scramble touched_registers lr lr2)))). }
  { move => ?? [] /=*; naive_solver. }
  { split!. econs. rewrite /r2a_mem_map big_sepM_union //.
    rewrite r2a_f2i_incl_union. 2: by apply map_agree_spec.
    2: { move => *. unfold map_Forall in *. naive_solver. }
    2: { move => *. unfold map_Forall in *. naive_solver. }
    iSplit; iIntros!.
    all: iDestruct select (r2a_f2i_incl f2i1 ins1) as "#?".
    all: iDestruct select (r2a_f2i_incl f2i2 ins2) as "#?".
    all: iFrame "#∗". }
  all: move => [cs1 lr1] [cs2 lr2] [cs lr] x1 x2 x ? ics.
  - move => e ? e' /= ? ??.
    destruct!.
    destruct e as [rs mem| |]; destruct!/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. split; [done|]. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => f Hargs Hin /not_elem_of_union[??] ? ?.
      repeat case_bool_decide => //.
      have ? : (f ∈ fns1). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        by iSatStop.
      }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *. destruct!.
      repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; simplify_eq/= => //. 2: { exfalso. set_solver. }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => e ? e' /= ? ??.
    destruct!.
    destruct e as [rs mem| |]; destruct!/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. split; [done|]. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => f Hargs Hin /not_elem_of_union[??] ??.
      repeat case_bool_decide => //.
      have ? : (f ∈ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *. destruct!. repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; simplify_eq/= => //.
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct!/=; split; [done|].
    + do 2 case_bool_decide => //. eexists true => /=.
      have ? : (f ∈ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: naive_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + repeat case_bool_decide => //. eexists false => /=.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". simplify_eq/=. iFrame. }
  - move => [? [f vs h|v h]] ? ? ? /= *.
    all: destruct!/=.
    + do 2 case_bool_decide => //.
      have ? : (f ∉ fns1 ∪ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        iSatStop. set_solver. }
      r2a_split!.
      1: repeat case_bool_decide => //; set_solver.
      1: set_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct!/=; split; [done|].
    + case_bool_decide; [|by case_bool_decide]. eexists true.
      have ? : (f ∈ fns1). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: naive_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //. eexists false.
      r2a_split!.
      1: { iSatMono. iIntros!. iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". simplify_eq/=. iFrame. }
  - move => [? [f vs h|v h]] ? /= ? *.
    all: destruct!/=.
    + do 2 case_bool_decide => //.
      have ? : (f ∉ fns1 ∪ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        iSatStop. set_solver. }
      r2a_split!.
      1: repeat case_bool_decide => //; set_solver.
      1: set_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iFrame. }
Qed.

(** * Proof technique for [rec_to_asm] *)
Lemma rec_to_asm_proof ins fns ins_dom f2i :
  ins_dom = dom ins →
  f2i_fns_ins_wf f2i (dom fns) ins_dom →
  (∀ n i rs mem K f fn vs h cs pc ssz rf rc lr,
      rs !!! "PC" = pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      satisfiable (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv h ∗ r2a_f2i_incl f2i ins_dom ∗ r2a_args 0 vs rs ∗ rf ∗ rc) →
      length vs = length (fd_args fn) →
      map_scramble touched_registers lr rs →
      (* Call *)
      (∀ K' rs' mem' f' es vs pc' ssz' h' lr' rf' r',
          Forall2 (λ e v, e = Val v) es vs →
          rs' !!! "PC" = pc' →
          (* We sadly don't have a good way to frame the r2a_f2i_incl
          f2i ins_dom. (We could put it in rc, but this would require
          the client to thread around rc). *)
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                      r2a_args 0 vs rs' ∗ r2a_f2i_incl {[f' := pc']} ∅ ∗
                      r2a_f2i_incl f2i ins_dom ∗ rf' ∗ r') →
          is_Some (ins !! (rs' !!! "R30")) →
          map_scramble touched_registers lr' rs' →
          (∀ rs'' ssz'' mem'' av v h'' rf'' lr'',
              rs'' !!! "PC" = rs' !!! "R30" →
              satisfiable (r2a_mem_inv (rs'' !!! "SP") ssz'' mem'' ∗ r2a_heap_inv h'' ∗
                           r2a_val_rel v av ∗ rf'' ∗ r') →
              r2a_regs_ret rs'' rs' av →
              map_scramble touched_registers lr'' rs'' →
              AsmState (ARunning []) rs'' mem'' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (expr_fill K' (Val v))) h'' fns, (PPInside, R2A cs lr'', uPred_shrink rf''))) →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (expr_fill K' (rec.Call (Val (ValFn f')) es))) h' fns, (PPInside, R2A cs lr', uPred_shrink rf'))) →
      (* Return *)
      (∀ rs' mem' ssz' av v h' lr' rf',
          rs' !!! "PC" = rs !!! "R30" →
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                      r2a_val_rel v av ∗ rf' ∗ rc) →
          r2a_regs_ret rs' rs av →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (Val v)) h' fns, (PPInside, R2A cs lr', uPred_shrink rf'))) →
      AsmState (ARunning []) rs mem ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, false}
               (SMProg, Rec (expr_fill K (AllocA fn.(fd_vars) $ subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (PPInside, R2A cs lr, uPred_shrink rf))
) →
  trefines (asm_mod ins) (rec_to_asm ins_dom f2i ∅ (rec_mod fns)).
Proof.
  move => ? Hwf Hf. subst.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((AsmState i1 rs1 mem1 ins'1), (σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1)))
                        '((AsmState i2 rs2 mem2 ins'2), (σfs2, Rec e2 h2 fns'2, (t2, R2A cs2 lr2, r2))),
      ∃ K rr1 rr2,
        i2 = AWaiting ∧ ins'2 = ins ∧ e2 = expr_fill K (Waiting (bool_decide (d ≠ 0%nat))) ∧ fns'2 = fns ∧
        t2 = PPOutside ∧ σfs2 = SMFilter ∧ (d = 0%nat ↔ cs2 = []) ∧
        r1 = uPred_shrink rr1 ∧ r2 = uPred_shrink rr2 ∧
        (rr2 ⊢ r2a_f2i_incl f2i (dom ins)) ∧
      if b then
        e2 = e1 ∧
        cs2 = cs1 ∧
        rr1 = rr2
      else
        True
  ). }
  { simpl. exact (λ  '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1))
                     '(AsmState i2 rs2 mem2 ins'2) '(σfs2, Rec e2 h2 fns'2, (t2, R2A cs2 lr2, r2)),
    ∃ i K av v pc lr' ssz rr1 rr2,
      r1 = uPred_shrink rr1 ∧ r2 = uPred_shrink rr2 ∧
      rs2 !!! "PC" = pc ∧
      ins !! pc = Some i ∧
      satisfiable (r2a_mem_inv (rs2 !!! "SP") ssz mem2 ∗ r2a_heap_inv h2 ∗ r2a_val_rel v av ∗ rr1 ∗ rr2) ∧
      r2a_regs_ret rs2 lr' av ∧
      i2 = ARunning [] ∧
      ins'1 = ins'2 ∧
      σfs2 = SMProg ∧
      e1 = expr_fill K (Waiting true) ∧
      e2 = expr_fill K (Val v) ∧
      fns'1 = fns'2 ∧
      t2 = PPInside ∧
      cs1 = R2AI true pc lr' :: cs2 ∧
      lr2 = rs2
). }
  { move => ??? *. destruct!. repeat case_match; naive_solver. }
  { move => /= *. destruct!. repeat case_match. naive_solver. }
  { move => /=. eexists []. split!. iIntros "[_ $]". }
  move => /= n [i rs mem ins'] [[?[???]][[?[cs ?]]r]] d ? ? Hstay Hcall Hret. destruct!/=.
  tstep_i => ??????.
  go_s. split!.
  go_s => -[] ? /=.
  - move => ?????? /elem_of_dom[??] /not_elem_of_dom ? ??.
    go_s.
    iSatStart. iIntros!.
    rename select (_ ⊢ _) into Hrr2. iDestruct (Hrr2 with "[$]") as "#Hincl".
    iDestruct (f2i_fns_ins_wf_in_ins f2i with "[$] [$]") as %Hfi; [done|by apply elem_of_dom|].
    move: Hfi => /elem_of_dom[??]. iSatStop.
    split!. tstep_s. left. split! => ?.
    (* This inner loop deals with calls inside of the module. We use
    Hf both for calls triggered from inside and outside the module. *)
    unshelve eapply tsim_remember. { exact (λ n '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1)),
       ∃ K' pc i f fn vs r' ssz rr1,
         r1 = uPred_shrink rr1 ∧
         rs1 !!! "PC" = pc ∧
         ins !! pc = Some i ∧
         fns !! f = Some fn ∧
         ins'1 = ins ∧
         fns'1 = fns ∧
         satisfiable (r2a_mem_inv (rs1 !!! "SP") ssz mem1 ∗ r2a_heap_inv h1 ∗
                      r2a_f2i_incl f2i (dom ins) ∗ r2a_f2i_incl {[f := pc]} ∅ ∗
                      r2a_args 0 vs rs1 ∗ r' ∗ rr1) ∧
         i1 = ARunning [] ∧
         e1 = expr_fill K' (AllocA fn.(fd_vars) $ subst_l fn.(fd_args) vs fn.(fd_body)) ∧
         map_scramble touched_registers lr1 rs1 ∧
         length vs = length (fd_args fn) ∧
         t1 = PPInside ∧
         σfs1 = SMProg ∧
         (∀ rs' mem' ssz' av v h' lr' rf',
          rs' !!! "PC" = rs1 !!! "R30" →
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                       r2a_f2i_incl f2i (dom ins) ∗
                       r2a_val_rel v av ∗ r' ∗ rf') →
          r2a_regs_ret rs' rs1 av  →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans (dom ins) f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K' (Val v)) h' fns, (PPInside, R2A cs1 lr', uPred_shrink rf'))) ). }
    { eexists (ReturnExtCtx _:: _). split! => //. {
        iSatMono. iIntros!. iFrame "∗#".
        iDestruct (r2a_args_intro with "[$]") as "$"; [done|].
        iRename select (rr2) into "Hrr2". iExact "Hrr2". }
      iSatClear. move => *.
      tstep_s.
      tstep_i => ??. simplify_map_eq'.
      tstep_s. split!. { instantiate (1:=[_]). done. } {
        iSatMono. iIntros!. iFrame. iRename select (rr2) into "Hrr2". iExact "Hrr2". }
      apply Hstay; [done|]. by split!.
    }
    { move => ?? [????] [[?[???]][[?[??]]?]] ??. destruct!. split!; [done..|].
      move => *. apply: tsim_mono; [naive_solver|]. etrans; [|done]. apply o_le_S. }
    iSatClear.
    move => n' /= Hn' IH [i' rs' mem' ins'] [[?[???]][[?[??]]?]] ?. destruct!.
    apply: Hf; [try done..| |]. {
      iSatStart. iIntros!.
      iDestruct (r2a_f2i_incl_in_ins _ _ f2i with "[$] [$]") as %?. { by apply elem_of_dom. }
      by iSatStop.
    }
    { iSatMono. iIntros!.
      iDestruct select (r2a_f2i_incl f2i _) as "#Hf2i".
      iFrame "∗#". iDestruct "Hf2i" as "-#Hf2i". iAccu. }
    + iSatClear.
      move => K'' rs'' mem'' f'' es vs'' pc'' ssz'' h'' lr rf'' r'' Hall ???? Hret'.
      have ?: es = Val <$> vs''. { clear -Hall. elim: Hall; naive_solver. } subst.
      destruct (ins !! (rs'' !!! "PC")) eqn:Hi.
      * iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins with "[$] [$]") as %Hf''; [done|by apply elem_of_dom|].
        move: Hf'' => /elem_of_dom[??]. iSatStop.
        tstep_s. left. split! => ?/=.
        apply IH; [done|]. split! => //.
        { iSatMono. iIntros!. iFrame. iAccu. }
        iSatClear. move => *.
        rewrite expr_fill_app.
        apply: Hret' => //.
        iSatMono. iIntros!. iFrame.
      * have ?: fns !! f'' = None. {
          iSatStart. iIntros!.
          iDestruct (f2i_fns_ins_wf_not_in_ins with "[$] [$]") as %?; [done|by apply not_elem_of_dom|].
          iSatStop. by apply not_elem_of_dom.
        }
        tstep_i => ??. simplify_map_eq.
        tstep_s. right. split!.
        tstep_s.
        iSatStart. iIntros!.
        iDestruct (r2a_args_elim with "[$]") as (??) "?". iSatStop.
        r2a_split!. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
        { iSatMono. iIntros!. iFrame. iAccu. }
        apply Hcall. { etrans; [|done]. apply o_le_S. } { split!; [done|]. iIntros!. done. }
        iSatClear.
        move => [i2 rs2 mem2 ins'2] [[?[???]][[?[??]]?]].
        move => [i3 rs3 mem3 ins'3] [[?[???]][[?[??]]?]] ??. destruct!.
        repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
        destruct!.
        rewrite !expr_fill_app /=.
        eapply Hret' => //.
        iSatMono. iIntros!. iFrame.
    + iSatClear. move => *.
      apply: H14 => //.
      iSatMono. iIntros!. iFrame.
  - move => *.
    tstep_s. simplify_eq. destruct d; [exfalso; naive_solver|]. split!.
    apply Hret; [done..| |].
    + by split!.
    + split!; [|done..]. destruct!/=.
      iSatMono. iIntros!. iFrame.
Qed.
