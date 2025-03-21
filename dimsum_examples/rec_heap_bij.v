From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core Require Export proof_techniques prepost.
From dimsum.core Require Import link.
From dimsum.core Require Import axioms.
From dimsum.examples Require Import rec.

Set Default Proof Using "Type".

(** * rec_heap_bij *)
(** [rec_heap_bij] allows transformations of memory when proving a
refinement between two Rec modules. *)

(** * Camera definition *)
Inductive heap_bij_elem :=
| HBShared (p : prov) | HBConstant (h : gmap Z val).
Canonical Structure heap_bij_elemO := leibnizO heap_bij_elem.
Inductive heap_bij_priv_elem := HBIConstant (h : gmap Z val).
Canonical Structure heap_bij_priv_elemO := leibnizO heap_bij_priv_elem.

Definition heap_bijUR : ucmra :=
  prodUR (optionO (agree (gset prov)))
         (prodUR (gmap_viewUR prov (agreeR heap_bij_elemO))
            (gmap_viewUR prov (agreeR heap_bij_priv_elemO))).

Global Instance heap_bijUR_shrink : Shrink heap_bijUR.
Proof. solve_shrink. Qed.

Definition heap_bijUR_s_inj (r : (gmap_viewUR prov (agreeR heap_bij_elemO))) : heap_bijUR := (None, (r, ε)).
Definition heap_bijUR_i_inj (r : (gmap_viewUR prov (agreeR heap_bij_priv_elemO))) : heap_bijUR := (None, (ε, r)).
Definition heap_bijUR_statics_inj (r : agree (gset prov)) : heap_bijUR := ((Some r), (ε, ε)).

Definition same_prov_kind (p1 p2 : prov) :=
  match p1, p2 with
  | ProvBlock _, ProvBlock _ => True
  | ProvStatic _ _, ProvStatic _ _ => p1 = p2
  | _, _ => False
  end.

Global Instance same_prov_kind_equiv : Equivalence same_prov_kind.
Proof.
  constructor.
  - by move => [|].
  - by move => [?|??] [?|??].
  - move => [?|??] [?|??] [?|??] //=. naive_solver.
Qed.

Lemma same_prov_kind_static_l p1 p2:
  same_prov_kind p1 p2 →
  is_ProvStatic p1 →
  p1 = p2.
Proof. by destruct p1, p2. Qed.

Lemma same_prov_kind_static_r p1 p2:
  same_prov_kind p1 p2 →
  is_ProvStatic p2 →
  p1 = p2.
Proof. by destruct p1, p2. Qed.

Lemma same_prov_kind_is_ProvBlock_iff p1 p2 :
  same_prov_kind p1 p2 →
  is_ProvBlock p1 ↔ is_ProvBlock p2.
Proof.
  by destruct p1, p2.
Qed.

(** * heap_bij *)
Record heap_bij := HeapBij {
  hb_bij : gmap prov heap_bij_elem;
  hb_priv_i : gmap prov (gmap Z val);
  hb_disj ps pi:
   hb_bij !! ps = Some (HBShared pi) →
   hb_priv_i !! pi = None;
  hb_iff pi ps ps' :
   hb_bij !! ps = Some (HBShared pi) →
   hb_bij !! ps' = Some (HBShared pi) →
   ps = ps';
  hb_shared_prov ps pi:
    hb_bij !! ps = Some (HBShared pi) →
    same_prov_kind pi ps
}.
Add Printing Constructor heap_bij.

Ltac simplify_bij :=
  repeat (simplify_eq; match goal with
         | H1 : hb_bij ?bij !! ?ps1 = Some (HBShared ?pi),
             H2 : hb_bij ?bij !! ?ps2 = Some (HBShared ?pi) |- _ =>
             pose proof (hb_iff bij pi ps1 ps2 H1 H2); clear H2
         end); simplify_eq.

Lemma heap_bij_eq bij1 bij2 :
  bij1 = bij2 ↔ hb_bij bij1 = hb_bij bij2 ∧ hb_priv_i bij1 = hb_priv_i bij2.
Proof.
  split; [naive_solver|]. move => [??]. destruct bij1, bij2 => /=. simplify_eq/=. f_equal.
  all: apply AxProofIrrelevance.
Qed.

Global Program Instance heap_bij_empty : Empty heap_bij := HeapBij ∅ ∅ _ _ _.
Next Obligation. set_solver. Qed.
Next Obligation. set_solver. Qed.
Next Obligation. set_solver. Qed.

Lemma hb_shared_static_eq_s bij ps pi :
  hb_bij bij !! ps = Some (HBShared pi) →
  is_ProvStatic ps →
  pi = ps.
Proof. move => /hb_shared_prov. by destruct pi, ps. Qed.

Lemma hb_shared_static_eq_i bij ps pi :
  hb_bij bij !! ps = Some (HBShared pi) →
  is_ProvStatic pi →
  pi = ps.
Proof. move => /hb_shared_prov. by destruct pi, ps. Qed.

(** ** hb_shared *)
Definition hb_shared (bij : heap_bij) : gmap prov prov :=
  (omap (λ v, if v is HBShared p then Some p else None) (hb_bij bij)).

Lemma hb_shared_lookup bij ps :
  hb_shared bij !! ps = hb_bij bij !! ps ≫= λ v, if v is HBShared p then Some p else None.
Proof. apply lookup_omap. Qed.

Lemma hb_shared_lookup_Some bij ps pi :
  hb_shared bij !! ps = Some pi ↔ hb_bij bij !! ps = Some (HBShared pi).
Proof. rewrite hb_shared_lookup. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

Lemma hb_shared_lookup_None bij ps :
  hb_shared bij !! ps = None ↔ ∀ pi, hb_bij bij !! ps = Some (HBShared pi) → False.
Proof. rewrite hb_shared_lookup. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

(** ** hb_shared_rev *)
Definition hb_shared_rev (bij : heap_bij) : gmap prov prov :=
  list_to_map $ (λ x, (x.2, x.1)) <$> map_to_list (hb_shared bij).

Lemma hb_shared_rev_lookup_Some bij ps pi :
  hb_shared_rev bij !! pi = Some ps ↔ hb_bij bij !! ps = Some (HBShared pi).
Proof.
  rewrite /hb_shared_rev -elem_of_list_to_map. 2: {
    rewrite -list_fmap_compose. apply NoDup_fmap_2_strong; [|apply NoDup_map_to_list].
    move => [??][??] /elem_of_map_to_list/hb_shared_lookup_Some? /elem_of_map_to_list /hb_shared_lookup_Some?/= ?.
    by simplify_bij.
  }
  rewrite elem_of_list_fmap -hb_shared_lookup_Some.
  split.
  - move => [[??] /=[? /elem_of_map_to_list ?]]. naive_solver.
  - move => ?. eexists (_, _). rewrite elem_of_map_to_list. naive_solver.
Qed.

(** ** hb_shared_s *)
Definition hb_shared_s (bij : heap_bij) : gset prov := dom (hb_shared bij).

Lemma elem_of_hb_shared_s bij ps :
  ps ∈ hb_shared_s bij ↔ ∃ pi, hb_bij bij !! ps = Some (HBShared pi).
Proof. rewrite /hb_shared_s; unlock. rewrite elem_of_dom /is_Some. f_equiv => ?. apply hb_shared_lookup_Some. Qed.

Lemma hb_shared_s_empty :
  hb_shared_s ∅ = ∅.
Proof. apply set_eq => ?. by rewrite elem_of_hb_shared_s. Qed.

(** ** hb_shared_i *)
Definition hb_shared_i (bij : heap_bij) : gset prov :=
  list_to_set (omap (λ x, if x.2 is HBShared p then Some p else None) (map_to_list (hb_bij bij))).
Global Typeclasses Opaque hb_shared_i.

Lemma elem_of_hb_shared_i bij p1:
  p1 ∈ hb_shared_i bij ↔ ∃ p2, hb_bij bij !! p2 = Some (HBShared p1).
Proof.
  rewrite /hb_shared_i elem_of_list_to_set elem_of_list_omap.
  setoid_rewrite elem_of_map_to_list'.
  split.
  - move => [[??] /= [??]]. case_match; simplify_eq/=. naive_solver.
  - move => [??]. by eexists (_, _).
Qed.

Lemma hb_shared_i_static p bij :
  is_ProvStatic p →
  p ∈ hb_shared_i bij ↔ p ∈ hb_shared_s bij.
Proof.
  move => ?. rewrite elem_of_hb_shared_i elem_of_hb_shared_s.
  split => -[p2 ?]; (exploit hb_shared_prov; [done|]).
  - move => /same_prov_kind_static_l. naive_solver.
  - move => /same_prov_kind_static_r. naive_solver.
Qed.

Lemma hb_shared_i_empty :
  hb_shared_i ∅ = ∅.
Proof. apply set_eq => ?. by rewrite elem_of_hb_shared_i. Qed.

(** ** hb_priv_s *)
Definition hb_priv_s (bij : heap_bij) : gmap prov (gmap Z val) :=
  omap (λ v, if v is HBConstant h then Some h else None) (hb_bij bij).

Lemma hb_priv_s_lookup_None bij ps :
  hb_priv_s bij !! ps = None ↔ ∀ h, hb_bij bij !! ps = Some (HBConstant h) → False.
Proof. rewrite lookup_omap. destruct (hb_bij bij !! ps) => //=. case_match; naive_solver. Qed.

Lemma hb_priv_s_lookup_Some bij ps h :
  hb_priv_s bij !! ps = Some h ↔ hb_bij bij !! ps = Some (HBConstant h).
Proof.
  rewrite lookup_omap_Some.
  split.
  - move => [?[??]]. case_match => //; naive_solver.
  - move => ?. eexists _. split; [|done]. done.
Qed.

(** ** hb_provs_i *)
(* hb_provs_s is directly written as [dom (hb_bij bij)] *)
Definition hb_provs_i (bij : heap_bij) : gset prov :=
  dom (hb_priv_i bij) ∪ hb_shared_i bij.

Lemma elem_of_hb_provs_i bij pi :
  pi ∈ hb_provs_i bij ↔ (∃ h, hb_priv_i bij !! pi = Some h) ∨ ∃ ps, hb_bij bij !! ps = Some (HBShared pi).
Proof. unfold hb_provs_i. rewrite elem_of_union elem_of_dom elem_of_hb_shared_i. naive_solver. Qed.

Lemma hb_provs_i_empty :
  hb_provs_i ∅ = ∅.
Proof. apply set_eq => ?. by rewrite elem_of_hb_provs_i. Qed.

(** ** heap_bij constructors *)
Program Definition hb_share (p1 p2 : prov) (bij : heap_bij)
        (H : p1 ∉ hb_provs_i bij) (Hkind : same_prov_kind p1 p2) :=
  HeapBij (<[p2 := HBShared p1]> (hb_bij bij)) (hb_priv_i bij) _ _ _.
Next Obligation.
  move => ??? Hnotin ???. move: Hnotin. rewrite elem_of_hb_provs_i => ?.
  rewrite !lookup_insert_Some => ?. destruct!/= => //; try naive_solver.
  - apply eq_None_ne_Some => ??. naive_solver.
  - by apply: hb_disj.
Qed.
Next Obligation.
  move => ??? Hnotin ????. move: Hnotin. rewrite elem_of_hb_provs_i => ?.
  rewrite !lookup_insert_Some => ??. destruct!/= => //; try naive_solver.
  by apply: hb_iff.
Qed.
Next Obligation.
  move => ??? Hnotin ??? /lookup_insert_Some [[<- [<-]]//| [??]].
  by apply: hb_shared_prov.
Qed.

Program Definition hb_share_big (s : gmap prov prov) (bij : heap_bij)
        (H1 : ∀ p1 p2, s !! p2 = Some p1 → p1 ∉ hb_provs_i bij)
        (H2 : ∀ p1 p2 p2', s !! p2 = Some p1 → s !! p2' = Some p1 → p2 = p2')
        (H1 : ∀ p1 p2, s !! p2 = Some p1 → same_prov_kind p1 p2) :=
  HeapBij ((HBShared <$> s) ∪ (hb_bij bij)) (hb_priv_i bij) _ _ _.
Next Obligation.
  move => ?? Hnotin ????.
  rewrite lookup_union_Some_raw lookup_fmap fmap_Some fmap_None => ?.
  destruct!/= => //; try naive_solver.
  - setoid_rewrite elem_of_hb_provs_i in Hnotin. apply eq_None_not_Some. naive_solver.
  - by apply: hb_disj.
Qed.
Next Obligation.
  move => ?? Hnotin Hag ????.
  rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None => ??.
  destruct!/= => //; try naive_solver.
  - setoid_rewrite elem_of_hb_provs_i in Hnotin. naive_solver.
  - setoid_rewrite elem_of_hb_provs_i in Hnotin. naive_solver.
  - by apply: hb_iff.
Qed.
Next Obligation.
  move => ???? Hkind ??.
  rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None => [[[?[?[->]]]|[_]]].
  - naive_solver.
  - eapply hb_shared_prov.
Qed.

Lemma hb_share_big_empty bij H1 H2 H3:
  hb_share_big ∅ bij H1 H2 H3 = bij.
Proof. apply heap_bij_eq => /=. split; [|done]. by rewrite fmap_empty left_id_L. Qed.

Program Definition hb_update_const_s (p : prov) (h : gmap Z val) (bij : heap_bij) :=
  HeapBij (<[p := HBConstant h]> (hb_bij bij)) (hb_priv_i bij) _ _ _.
Next Obligation.
  move => ?????.
  rewrite !lookup_insert_Some => ?. destruct!/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ??????.
  rewrite !lookup_insert_Some => ??. destruct!/= => //. by apply: hb_iff.
Qed.
Next Obligation.
  move => ????? /lookup_insert_Some [[??]|[??]]; first done.
  by eapply hb_shared_prov.
Qed.

Program Definition hb_update_const_s_big (s : gmap prov (gmap Z val)) (bij : heap_bij) :=
  HeapBij ((HBConstant <$> s) ∪ (hb_bij bij)) (hb_priv_i bij) _ _ _.
Next Obligation.
  move => ????.
  rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some fmap_None => ?.
  destruct!/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ?????.
  rewrite !lookup_union_Some_raw !lookup_fmap !fmap_Some !fmap_None => ??.
  destruct!/= => //. by apply: hb_iff.
Qed.
Next Obligation.
  move => ???? /lookup_union_Some_raw [/lookup_fmap_Some [? []]|[_ ?]]; first done.
  by eapply hb_shared_prov.
Qed.

Lemma hb_update_const_s_big_empty bij:
  hb_update_const_s_big ∅ bij = bij.
Proof. apply heap_bij_eq => /=. split; [|done]. by rewrite fmap_empty left_id_L. Qed.

Lemma hb_update_const_s_big_insert bij p2 h s:
  hb_update_const_s_big (<[p2:=h]> s) bij = hb_update_const_s p2 h $ hb_update_const_s_big s bij.
Proof. apply heap_bij_eq => /=. split; [|done]. by rewrite fmap_insert insert_union_l. Qed.

Lemma hb_shared_i_hb_update_const_s_big s bij :
  dom s ## hb_shared_s bij →
  hb_shared_i (hb_update_const_s_big s bij) = hb_shared_i bij.
Proof.
  move => Hdisj.
  apply set_eq => ?.
  rewrite !elem_of_hb_shared_i /=.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_fmap.
  setoid_rewrite fmap_None.
  setoid_rewrite fmap_Some.
  split; [naive_solver|].
  move => [??]. split!; [|done].
  apply not_elem_of_dom. apply: not_elem_of_disjoint; [|by symmetry].
  apply elem_of_hb_shared_s.
  naive_solver.
Qed.

Lemma hb_shared_s_hb_update_const_s_big s bij :
  dom s ## hb_shared_s bij →
  hb_shared_s (hb_update_const_s_big s bij) = hb_shared_s bij.
Proof.
  move => Hdisj.
  apply set_eq => ?.
  rewrite !elem_of_hb_shared_s /=.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_fmap.
  setoid_rewrite fmap_None.
  setoid_rewrite fmap_Some.
  split; [naive_solver|].
  move => [??]. split!.
  apply not_elem_of_dom. apply: not_elem_of_disjoint; [|by symmetry].
  apply elem_of_hb_shared_s.
  naive_solver.
Qed.

Lemma hb_provs_i_hb_update_const_s_big s bij :
  dom s ## hb_shared_s bij →
  hb_provs_i (hb_update_const_s_big s bij) = hb_provs_i bij.
Proof. move => Hdisj. by rewrite /hb_provs_i/= hb_shared_i_hb_update_const_s_big. Qed.


Program Definition hb_update_const_i (p : prov) (h : gmap Z val) (bij : heap_bij)
  (H : p ∉ hb_shared_i bij) :=
  HeapBij (hb_bij bij) (<[p := h]> $ hb_priv_i bij) _ _ _.
Next Obligation.
  move => ??? /elem_of_hb_shared_i ????.
  rewrite !lookup_insert_None.
  split; [by apply: hb_disj|naive_solver].
Qed.
Next Obligation.
  move => ???????. by apply: hb_iff.
Qed.
Next Obligation.
  move => ???????. by apply: hb_shared_prov.
Qed.

Program Definition hb_update_const_i_big (s : gmap prov (gmap Z val)) (bij : heap_bij) (H : dom s ## hb_shared_i bij) :=
  HeapBij (hb_bij bij) (s ∪ hb_priv_i bij) _ _ _.
Next Obligation.
  move => ?? Hdisj ???.
  rewrite !lookup_union_None.
  split; [|by apply: hb_disj].
  apply not_elem_of_dom_1. apply: not_elem_of_disjoint. 2: by symmetry.
  apply elem_of_hb_shared_i. naive_solver.
Qed.
Next Obligation.
  move => ???????. by apply: hb_iff.
Qed.
Next Obligation.
  move => ??????. by apply: hb_shared_prov.
Qed.

Lemma hb_shared_i_hb_update_const_i_big s bij H:
  hb_shared_i (hb_update_const_i_big s bij H) = hb_shared_i bij.
Proof. apply set_eq => ?. rewrite !elem_of_hb_shared_i /=. done. Qed.

Lemma hb_shared_s_hb_update_const_i_big s bij H:
  hb_shared_s (hb_update_const_i_big s bij H) = hb_shared_s bij.
Proof. apply set_eq => ?. rewrite !elem_of_hb_shared_s /=. done. Qed.

Lemma hb_provs_i_hb_update_const_i_big s bij H :
  hb_provs_i (hb_update_const_i_big s bij H) = dom s ∪ hb_provs_i bij.
Proof. rewrite /hb_provs_i/= hb_shared_i_hb_update_const_i_big dom_union_L. set_solver. Qed.

(* Alternative version of hb_update_const_i_big such that we can do
induction on s without worrying about the proof term in the argument. *)
Definition hb_update_const_i_big_alt (s : gmap prov (gmap Z val)) (bij : heap_bij) :=
  if decide (dom s ## hb_shared_i bij) is left H then
    hb_update_const_i_big s bij H
  else ∅.

Lemma hb_update_const_i_big_alt_eq s bij H :
  hb_update_const_i_big s bij H = hb_update_const_i_big_alt s bij.
Proof. rewrite /hb_update_const_i_big_alt. case_decide => //. by apply heap_bij_eq. Qed.

Lemma hb_update_const_i_big_alt_empty bij:
  hb_update_const_i_big_alt ∅ bij = bij.
Proof.
  rewrite /hb_update_const_i_big_alt. case_decide as Hd.
  - apply heap_bij_eq => /=. by rewrite left_id_L.
  - contradict Hd. rewrite dom_empty. apply disjoint_empty_l.
Qed.

Lemma hb_update_const_i_big_alt_insert bij p2 h s Hni:
  dom s ## hb_shared_i bij →
  hb_update_const_i_big_alt (<[p2:=h]> s) bij =
    hb_update_const_i p2 h (hb_update_const_i_big_alt s bij) Hni.
Proof.
  move => Hdisj.
  rewrite /hb_update_const_i_big_alt. case_decide as Hd1. 2: {
    contradict Hd1. rewrite dom_insert_L. move: Hni.
    rewrite -hb_update_const_i_big_alt_eq hb_shared_i_hb_update_const_i_big.
    set_solver. }
  apply heap_bij_eq => /=. case_decide as Hd2; [|done].
  split; [done|]. by rewrite /= insert_union_l.
Qed.

Program Definition hb_delete_s (p : prov) (bij : heap_bij) :=
  HeapBij (delete p (hb_bij bij)) (hb_priv_i bij) _ _ _.
Next Obligation.
  move => ????.
  rewrite !lookup_delete_Some => ?. destruct!/= => //. by apply: hb_disj.
Qed.
Next Obligation.
  move => ?????.
  rewrite !lookup_delete_Some => ??. destruct!/= => //. by apply: hb_iff.
Qed.
Next Obligation.
  move => ????.
  rewrite !lookup_delete_Some => [[??]]. by apply: hb_shared_prov.
Qed.

Lemma hb_provs_i_delete_s p bij:
  p ∉ hb_shared_s bij →
  hb_provs_i (hb_delete_s p bij) = hb_provs_i bij.
Proof.
  move => /elem_of_hb_shared_s ?.
  apply set_eq => ?.
  rewrite !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_delete_Some.
  set_solver.
Qed.

Lemma hb_shared_delete_s p bij :
  hb_shared (hb_delete_s p bij) = delete p (hb_shared bij).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  by rewrite hb_shared_lookup_Some /= !lookup_delete_Some hb_shared_lookup_Some.
Qed.

Lemma hb_priv_s_delete_s p bij:
  hb_priv_s (hb_delete_s p bij) = delete p (hb_priv_s bij).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  by rewrite hb_priv_s_lookup_Some /= !lookup_delete_Some hb_priv_s_lookup_Some.
Qed.

Program Definition hb_delete_s_big (s : gmap prov (gmap Z val)) (bij : heap_bij) :=
  HeapBij (hb_bij bij ∖ (HBConstant <$> s)) (hb_priv_i bij) _ _ _.
Next Obligation. move => ????. rewrite !lookup_difference_Some => -[??]. by apply: hb_disj. Qed.
Next Obligation. move => ?????. rewrite !lookup_difference_Some => -[??] -[??]. by apply: hb_iff. Qed.
Next Obligation. move => ????. rewrite !lookup_difference_Some => -[??]. by apply: hb_shared_prov. Qed.

Lemma hb_delete_s_big_empty bij:
  hb_delete_s_big ∅ bij = bij.
Proof. apply heap_bij_eq => /=. split; [|done]. by rewrite fmap_empty map_difference_empty. Qed.

Lemma hb_delete_s_big_insert bij p2 h s:
  hb_delete_s_big (<[p2:=h]> s) bij = hb_delete_s p2 $ hb_delete_s_big s bij.
Proof. apply heap_bij_eq => /=. split; [|done]. by rewrite fmap_insert -delete_difference. Qed.


Program Definition hb_delete_i (p : prov) (bij : heap_bij) :=
  HeapBij (hb_bij bij) (delete p (hb_priv_i bij)) _ _ _.
Next Obligation.
  move => ????.
  rewrite !lookup_delete_None => ?. right. by apply: hb_disj.
Qed.
Next Obligation.
  move => ?????. by apply: hb_iff.
Qed.
Next Obligation.
  move => ????. by apply: hb_shared_prov.
Qed.

Lemma hb_provs_i_delete_i p bij :
  p ∉ hb_shared_i bij →
  hb_provs_i (hb_delete_i p bij) = hb_provs_i bij ∖ {[ p ]}.
Proof.
  move => /elem_of_hb_shared_i ?.
  apply set_eq => ?. rewrite elem_of_difference !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_delete_Some.
  set_solver.
Qed.

Lemma hb_shared_delete_i p bij :
  hb_shared (hb_delete_i p bij) = hb_shared bij.
Proof. apply map_eq => ?. apply option_eq => ?. by rewrite !hb_shared_lookup_Some. Qed.

Lemma hb_shared_s_delete_i p bij :
  hb_shared_s (hb_delete_i p bij) = hb_shared_s bij.
Proof. apply set_eq => ?. by rewrite !elem_of_hb_shared_s /=. Qed.

Lemma hb_priv_s_delete_i p bij:
  hb_priv_s (hb_delete_i p bij) = hb_priv_s bij.
Proof. apply map_eq => ?. apply option_eq => ?. by rewrite hb_priv_s_lookup_Some. Qed.

Program Definition hb_delete_i_big (s : gmap prov (gmap Z val)) (bij : heap_bij) :=
  HeapBij (hb_bij bij) (hb_priv_i bij ∖ s) _ _ _.
Next Obligation. move => ????. rewrite !lookup_difference_None. left. by apply: hb_disj. Qed.
Next Obligation. move => *. by apply: hb_iff. Qed.
Next Obligation. move => ????. by apply: hb_shared_prov. Qed.

Lemma hb_delete_i_big_empty bij:
  hb_delete_i_big ∅ bij = bij.
Proof. apply heap_bij_eq => /=. split; [done|]. by rewrite map_difference_empty. Qed.

Lemma hb_delete_i_big_insert bij p2 h s:
  hb_delete_i_big (<[p2:=h]> s) bij = hb_delete_i p2 $ hb_delete_i_big s bij.
Proof. apply heap_bij_eq => /=. split; [done|]. by rewrite -delete_difference. Qed.


Lemma hb_priv_s_share pi ps bij H H2:
  hb_priv_s (hb_share pi ps bij H H2) = delete ps (hb_priv_s bij).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !hb_priv_s_lookup_Some/=.
  rewrite lookup_delete_Some hb_priv_s_lookup_Some lookup_insert_Some.
  naive_solver.
Qed.

Lemma hb_priv_s_update_const_s bij ps h :
  hb_priv_s (hb_update_const_s ps h bij) = <[ps := h]> (hb_priv_s bij).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !hb_priv_s_lookup_Some/=.
  rewrite !lookup_insert_Some hb_priv_s_lookup_Some/=. naive_solver.
Qed.

Lemma hb_provs_i_share p1 p2 bij H H2:
  hb_provs_i (hb_share p1 p2 bij H H2) ⊆ {[p1]} ∪ hb_provs_i bij.
Proof.
  move => ?. rewrite elem_of_union !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_insert_Some at 1. set_solver.
Qed.

Lemma hb_provs_i_update_const_s p h bij:
  hb_provs_i (hb_update_const_s p h bij) ⊆ hb_provs_i bij.
Proof.
  move => ?. rewrite !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma hb_provs_i_update_const_i p h bij H:
  hb_provs_i (hb_update_const_i p h bij H) ⊆ {[p]} ∪ hb_provs_i bij.
Proof.
  move => ?. rewrite !elem_of_hb_provs_i /=.
  setoid_rewrite lookup_insert_Some => Hp.
  apply elem_of_union. rewrite elem_of_hb_provs_i. set_solver.
Qed.

Lemma hb_shared_share pi ps bij H Hkind:
  hb_shared (hb_share pi ps bij H Hkind) = <[ps := pi]> (hb_shared bij).
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite !hb_shared_lookup_Some /=.
  rewrite !lookup_insert_Some !hb_shared_lookup_Some. naive_solver.
Qed.

Lemma hb_shared_update_const_s p2 h bij:
  (∀ p1, hb_bij bij !! p2 ≠ Some (HBShared p1)) →
  hb_shared (hb_update_const_s p2 h bij) = hb_shared bij.
Proof.
  move => ?.
  apply map_eq => ?. apply option_eq => ?. rewrite !hb_shared_lookup_Some /=.
  rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma hb_shared_update_const_i p h bij H:
  hb_shared (hb_update_const_i p h bij H) = hb_shared bij.
Proof. done. Qed.

(** * ghost theory *)
(** ** Ghost state definitions *)
Definition heap_bij_auth_bij (m : gmap prov heap_bij_elem) : uPred heap_bijUR :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> m)).
Definition heap_bij_auth_priv_i (m : gmap prov (gmap Z val)) : uPred heap_bijUR :=
  uPred_ownM (heap_bijUR_i_inj $ gmap_view_auth (DfracOwn 1) (to_agree ∘ HBIConstant <$> m)).

Definition heap_bij_auth (bij : heap_bij) : uPred heap_bijUR :=
  heap_bij_auth_bij (hb_bij bij) ∗ heap_bij_auth_priv_i (hb_priv_i bij).

Definition heap_bij_shared (p1 p2 : prov) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_frag p2 DfracDiscarded (to_agree $ HBShared p1)).

Definition heap_bij_const_s (p : prov) (h : gmap Z val) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_s_inj $ gmap_view_frag p (DfracOwn 1) (to_agree $ HBConstant h)).

Definition heap_bij_const_i (p : prov) (h : gmap Z val) : uPred (heap_bijUR) :=
  uPred_ownM (heap_bijUR_i_inj $ gmap_view_frag p (DfracOwn 1) (to_agree $ HBIConstant h)).

Definition heap_bij_statics (provs : gset prov) :=
  uPred_ownM (heap_bijUR_statics_inj (to_agree provs)).

(** ** Ghost state lemmas *)

Lemma heap_bij_statics_eq h1 h2 :
  heap_bij_statics h1 -∗
  heap_bij_statics h2 -∗
  ⌜h1 = h2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [/=]. rewrite -Some_op Some_valid to_agree_op_valid => ??.
  by fold_leibniz.
Qed.

Lemma heap_bij_alloc_shared1 m p1 p2:
  p2 ∉ dom m →
  heap_bij_auth_bij m ==∗ heap_bij_auth_bij (<[p2:=HBShared p1]> m) ∗ heap_bij_shared p1 p2.
Proof.
  iIntros (?) "?". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2 -pair_op_1. apply prod_update; [done|]. apply prod_update; [|done].
  rewrite fmap_insert. apply gmap_view_alloc; [|done..].
  rewrite lookup_fmap fmap_None. by apply not_elem_of_dom.
Qed.

Lemma heap_bij_alloc_shared bij p1 p2 H Hkind:
  p2 ∉ dom (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (hb_share p1 p2 bij H Hkind) ∗ heap_bij_shared p1 p2.
Proof. iIntros (?) "[? $]". by iApply heap_bij_alloc_shared1. Qed.

Lemma heap_bij_alloc_shared_big s bij H1 H2 Hkind :
  dom s ## dom (hb_bij bij) →
  heap_bij_auth bij ==∗
  heap_bij_auth (hb_share_big s bij H1 H2 Hkind) ∗ [∗ map] p2↦p1∈s, heap_bij_shared p1 p2.
Proof.
  iIntros (Hdisj) "[Ha $]" => /=. move: (hb_bij bij) Hdisj => m Hdisj. clear H1 H2.
  iInduction s as [|p2 p1 s ?] "IH" using map_ind forall (m Hdisj Hkind).
  { iModIntro. rewrite fmap_empty left_id_L big_sepM_empty. iFrame. }
  rewrite big_sepM_insert //.
  iMod ("IH" with "[%] [%] Ha") as "[Ha $]". {
    move => p /elem_of_dom[??]. apply: Hdisj. apply elem_of_dom.
    eexists _. rewrite lookup_insert_Some. naive_solver.
  } {
    move => ???. eapply Hkind, lookup_insert_Some. right.
    split!. move => ?. simplify_eq.
  }
  iMod (heap_bij_alloc_shared1 with "Ha") as "[Ha $]".
  { move => /elem_of_dom. move => [? /lookup_union_Some_raw[|[??]]].
    - rewrite lookup_fmap fmap_Some. naive_solver.
    - apply: Hdisj; apply elem_of_dom; [|done]. by rewrite lookup_insert. }
  by rewrite insert_union_l fmap_insert.
Qed.

Lemma heap_bij_shared_lookup p1 p2 bij :
  heap_bij_auth bij -∗
  heap_bij_shared p1 p2 -∗
  ⌜hb_bij bij !! p2 = Some (HBShared p1)⌝.
Proof.
  iIntros "[? _]". iStopProof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op -pair_op_2 -pair_op_1.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [? [/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _]].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma heap_bij_shared_lookup_big m bij :
  heap_bij_auth bij -∗
  ([∗ map] p2↦p1 ∈ m, heap_bij_shared p1 p2) -∗
  ⌜m ⊆ hb_shared bij⌝.
Proof.
  iIntros "Hauth Hsh".
  iInduction m as [|p h m ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hsh" as "[??]".
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?heap_is_fresh. iPureIntro.
  apply insert_subseteq_l; [|done]. by apply hb_shared_lookup_Some.
Qed.

Lemma heap_bij_alloc_const_s bij p h:
  p ∉ dom (hb_bij bij) →
  heap_bij_auth bij ==∗ heap_bij_auth (hb_update_const_s p h bij) ∗ heap_bij_const_s p h.
Proof.
  iIntros (?) "[? $]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2 -pair_op_1. apply prod_update; [done|].
  apply prod_update; [|done]. rewrite fmap_insert.
  apply gmap_view_alloc; [|done..]. rewrite lookup_fmap fmap_None. by apply not_elem_of_dom.
Qed.

Lemma heap_bij_alloc_const_s_big s bij :
  dom s ## dom (hb_bij bij) →
  heap_bij_auth bij ==∗
  heap_bij_auth (hb_update_const_s_big s bij) ∗ ([∗ map] p↦h∈s, heap_bij_const_s p h).
Proof.
  iIntros (Hdisj) "Ha" => /=.
  iInduction s as [|p2 p1 s ?] "IH" using map_ind forall (bij Hdisj).
  { iModIntro. rewrite hb_update_const_s_big_empty big_sepM_empty. iFrame. }
  rewrite big_sepM_insert //.
  iMod ("IH" with "[%] Ha") as "[Ha $]". {
    move => p /elem_of_dom[??]. apply: Hdisj. apply elem_of_dom.
    eexists _. rewrite lookup_insert_Some. naive_solver.
  }
  iMod (heap_bij_alloc_const_s with "Ha") as "[Ha $]".
  { move => /= /elem_of_dom. move => [? /lookup_union_Some_raw[|[??]]].
    - rewrite lookup_fmap fmap_Some. naive_solver.
    - apply: Hdisj; apply elem_of_dom; [|done]. by rewrite lookup_insert. }
  by rewrite hb_update_const_s_big_insert.
Qed.

Lemma heap_bij_alloc_const_i_disj p bij :
  p ∉ hb_provs_i bij → p ∉ hb_shared_i bij.
Proof. set_solver. Qed.

Lemma heap_bij_alloc_const_i bij p h
  (Hin : p ∉ hb_provs_i bij):
  heap_bij_auth bij ==∗ heap_bij_auth (hb_update_const_i p h bij
                                         (heap_bij_alloc_const_i_disj p bij Hin)) ∗ heap_bij_const_i p h.
Proof.
  iIntros "[$ ?]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite /= fmap_insert.
  rewrite -!pair_op_2. do 2 (apply prod_update; [done|]).
  apply gmap_view_alloc; [|done..].
  move: Hin => /elem_of_hb_provs_i Hin. rewrite lookup_fmap fmap_None. apply eq_None_not_Some => -[??].
  naive_solver.
Qed.

Lemma heap_bij_alloc_const_i_big s bij Hd :
  dom s ## hb_provs_i bij →
  heap_bij_auth bij ==∗
  heap_bij_auth (hb_update_const_i_big s bij Hd) ∗ ([∗ map] p↦h∈s, heap_bij_const_i p h).
Proof.
  iIntros (Hdisj) "Ha" => /=. rewrite hb_update_const_i_big_alt_eq. clear Hd.
  iInduction s as [|p2 p1 s ?] "IH" using map_ind forall (bij Hdisj).
  { iModIntro. rewrite hb_update_const_i_big_alt_empty big_sepM_empty. iFrame. }
  rewrite big_sepM_insert //.
  iMod ("IH" with "[%] Ha") as "[Ha $]". {
    move => p /elem_of_dom[??]. apply: Hdisj. apply elem_of_dom.
    eexists _. rewrite lookup_insert_Some. naive_solver.
  }
  unshelve iMod (heap_bij_alloc_const_i with "Ha") as "[Ha $]".
  { rewrite -hb_update_const_i_big_alt_eq.
    { apply: disjoint_mono; [done|rewrite dom_insert; set_solver|set_solver]. }
    move => ?. rewrite hb_provs_i_hb_update_const_i_big. apply not_elem_of_union.
    rewrite not_elem_of_dom. split; [done|]. set_solver. }
  rewrite -hb_update_const_i_big_alt_insert; [by iFrame|set_solver].
Qed.

Lemma heap_bij_free_const_s bij p h:
  heap_bij_auth bij ∗ heap_bij_const_s p h ==∗ heap_bij_auth (hb_delete_s p bij).
Proof.
  iIntros "[[? $] ?]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2 -pair_op_1. apply prod_update; [done|].
  apply prod_update; [|done]. rewrite fmap_delete.
  by apply gmap_view_delete.
Qed.

Lemma heap_bij_free_const_s_big s bij :
  heap_bij_auth bij -∗
  ([∗ map] p↦h∈s, heap_bij_const_s p h) ==∗
  heap_bij_auth (hb_delete_s_big s bij).
Proof.
  iIntros "Ha Hm" => /=.
  iInduction s as [|p2 h s ?] "IH" using map_ind forall (bij).
  { iModIntro. by rewrite hb_delete_s_big_empty. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hp Hm]".
  iMod ("IH" with "Ha Hm") as "Ha".
  iMod (heap_bij_free_const_s with "[$Ha $Hp]") as "?".
  iModIntro. by rewrite hb_delete_s_big_insert.
Qed.

Lemma heap_bij_free_const_i bij p h:
  heap_bij_auth bij ∗ heap_bij_const_i p h ==∗ heap_bij_auth (hb_delete_i p bij).
Proof.
  iIntros "[[$ ?] ?]". iStopProof. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -!pair_op_2. apply prod_update; [done|]. apply prod_update; [done|].
  rewrite /= fmap_delete. by apply gmap_view_delete.
Qed.

Lemma heap_bij_free_const_i_big s bij :
  heap_bij_auth bij -∗
  ([∗ map] p↦h∈s, heap_bij_const_i p h) ==∗
  heap_bij_auth (hb_delete_i_big s bij).
Proof.
  iIntros "Ha Hm" => /=.
  iInduction s as [|p2 h s ?] "IH" using map_ind forall (bij).
  { iModIntro. by rewrite hb_delete_i_big_empty. }
  rewrite big_sepM_insert //. iDestruct "Hm" as "[Hp Hm]".
  iMod ("IH" with "Ha Hm") as "Ha".
  iMod (heap_bij_free_const_i with "[$Ha $Hp]") as "?".
  iModIntro. by rewrite hb_delete_i_big_insert.
Qed.

Lemma heap_bij_const_s_lookup p f bij :
  heap_bij_auth bij -∗
  heap_bij_const_s p f -∗
  ⌜hb_bij bij !! p = Some (HBConstant f)⌝.
Proof.
  iIntros "[? _]". iStopProof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [? [/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _]].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma heap_bij_const_s_lookup_big m bij :
  heap_bij_auth bij -∗
  ([∗ map] p↦h ∈ m, heap_bij_const_s p h) -∗
  ⌜m ⊆ hb_priv_s bij⌝.
Proof.
  iIntros "Hauth Hconst".
  iInduction m as [|p h m ?] "IH" using map_ind. { iPureIntro. apply map_empty_subseteq. }
  rewrite big_sepM_insert //. iDestruct "Hconst" as "[??]".
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %?. iPureIntro.
  apply insert_subseteq_l; [|done]. by apply hb_priv_s_lookup_Some.
Qed.

Lemma heap_bij_const_i_lookup p f bij :
  heap_bij_auth bij -∗
  heap_bij_const_i p f -∗
  ⌜hb_priv_i bij !! p = Some f⌝.
Proof.
  iIntros "[_ ?]". iStopProof.
  apply bi.wand_intro_r. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [? [? /(gmap_view_both_dfrac_valid_discrete_total _ _ _)+]].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.


Lemma heap_bij_update_const_s bij p f h:
  heap_bij_auth bij ∗ heap_bij_const_s p f ==∗
  heap_bij_auth (hb_update_const_s p h bij) ∗ heap_bij_const_s p h.
Proof.
  iIntros "[[? $] ?]". iStopProof.
  rewrite -!uPred.ownM_op. apply uPred.bupd_ownM_update.
  rewrite -pair_op_2 -!pair_op_1. apply prod_update; [done|].
  apply prod_update; [|done]. rewrite fmap_insert.
  by apply gmap_view_replace.
Qed.

Lemma heap_bij_update_all bij' bij ho hs :
  ho ⊆ hb_priv_s bij →
  ho ⊆ hb_priv_s bij' →
  hb_shared bij ⊆ hb_shared bij' →
  hb_priv_i bij ∖ hs = hb_priv_i bij' →
  heap_bij_auth bij -∗
  ([∗ map] p2↦p1∈ hb_shared bij, heap_bij_shared p1 p2) -∗
  ([∗ map] p↦h∈ hb_priv_s bij ∖ ho, heap_bij_const_s p h) -∗
  ([∗ map] p↦h∈ hs, heap_bij_const_i p h) ==∗
  heap_bij_auth bij' ∗
  ([∗ map] p2↦p1∈ hb_shared bij', heap_bij_shared p1 p2) ∗
  ([∗ map] p↦h∈ hb_priv_s bij' ∖ ho, heap_bij_const_s p h)
.
Proof.
  iIntros (Hho1 Hho2 Hsub Hpi) "Ha #Hsh Hconst Hs".
  have Hsub' : ∀ p1 p2, hb_bij bij !! p2 = Some (HBShared p1) → hb_bij bij' !! p2 = Some (HBShared p1). {
    move => ??. rewrite -!hb_shared_lookup_Some => ?. by eapply lookup_weaken. }
  have Hho1' : ∀ p h, ho !! p = Some h → hb_bij bij !! p = Some (HBConstant h). {
    move => ??. rewrite -!hb_priv_s_lookup_Some => ?. by eapply lookup_weaken. }
  have Hho2' : ∀ p h, ho !! p = Some h → hb_bij bij' !! p = Some (HBConstant h). {
    move => ??. rewrite -!hb_priv_s_lookup_Some => ?. by eapply lookup_weaken. }
  iMod (heap_bij_free_const_s_big with "Ha Hconst") as "Ha".
  iMod (heap_bij_free_const_i_big with "Ha Hs") as "Ha".
  have Hash1 : ∀ p1 p2, (hb_shared bij' ∖ hb_shared bij) !! p2 = Some p1 → p1 ∉ hb_provs_i (hb_delete_i_big hs (hb_delete_s_big (hb_priv_s bij ∖ ho) bij)). {
    move => /= p1 p2 /lookup_difference_Some[/hb_shared_lookup_Some? /hb_shared_lookup_None?].
    rewrite elem_of_hb_provs_i /=. move => [[?]|[?]].
    - rewrite Hpi. by eapply eq_None_ne_Some_1, hb_disj.
    - move => /lookup_difference_Some[Hb]. move: (Hb) => /Hsub' ?. simplify_bij. naive_solver.
  }
  have Hash2 : ∀ p1 p2 p2', (hb_shared bij' ∖ hb_shared bij) !! p2 = Some p1 →
                            (hb_shared bij' ∖ hb_shared bij) !! p2' = Some p1 → p2 = p2'. {
    move => ???. rewrite !lookup_difference_Some !hb_shared_lookup_Some => -[??] [??].
    by simplify_bij.
  }
  unshelve iMod (heap_bij_alloc_shared_big (hb_shared bij' ∖ hb_shared bij) with "Ha") as "[Ha #Hsh2]"; [exact: Hash1| exact: Hash2|..]. {
     move => ??. rewrite lookup_difference_Some => [[??]]. by eapply hb_shared_prov, hb_shared_lookup_Some.
  } {
    apply elem_of_disjoint => ?.
    rewrite !elem_of_dom /is_Some /=.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite lookup_fmap. setoid_rewrite fmap_None.
    setoid_rewrite lookup_difference_None. rewrite /is_Some.
    setoid_rewrite hb_shared_lookup_Some. setoid_rewrite hb_shared_lookup_None.
    setoid_rewrite hb_priv_s_lookup_None.
    move => ??. destruct!.
    - destruct x; naive_solver.
    - naive_solver.
  }
  iMod (heap_bij_alloc_const_s_big with "Ha") as "[Ha $]". {
    apply elem_of_disjoint => ?.
    rewrite !elem_of_dom /is_Some /=.
    setoid_rewrite lookup_union_Some_raw.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite lookup_fmap. setoid_rewrite fmap_Some. setoid_rewrite fmap_None.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite lookup_difference_None. rewrite /is_Some.
    setoid_rewrite hb_shared_lookup_Some. setoid_rewrite hb_shared_lookup_None.
    setoid_rewrite hb_priv_s_lookup_Some. setoid_rewrite hb_priv_s_lookup_None.
    move => ??. destruct!.
    - destruct x; naive_solver.
    - naive_solver.
  }
  iModIntro. iSplit.
  - enough (hb_update_const_s_big (hb_priv_s bij' ∖ ho) (hb_share_big (hb_shared bij' ∖ hb_shared bij)
              (hb_delete_i_big hs (hb_delete_s_big (hb_priv_s bij ∖ ho) bij)) Hash1 Hash2 _) = bij') as -> by done.
    apply heap_bij_eq => /=. split; [|done].
    apply map_eq => p. apply option_eq => e.
    rewrite !lookup_union_Some_raw !lookup_difference_Some !lookup_fmap !fmap_Some !fmap_None.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite lookup_difference_None. rewrite /is_Some.
    setoid_rewrite hb_priv_s_lookup_Some.
    setoid_rewrite hb_priv_s_lookup_None.
    setoid_rewrite hb_shared_lookup_Some.
    setoid_rewrite hb_shared_lookup_None.
    split => ?.
    + destruct!/= => //; try destruct e; naive_solver.
    + destruct e.
      * split!; [naive_solver|].
        destruct (hb_shared bij !! p) eqn: Heq;
          rewrite ?hb_shared_lookup_Some ?hb_shared_lookup_None in Heq; naive_solver.
      * destruct (ho !! p) eqn: ?; [|naive_solver]. split!; naive_solver.
  - iApply big_sepM_subseteq.
    { by rewrite - (map_difference_union (hb_shared bij) (hb_shared bij')). }
    iApply big_sepM_union; [by apply map_disjoint_difference_r|by iFrame "#"].
Qed.

(** * val_in_bij *)

Definition loc_in_bij (l1 l2 : loc) : uPred heap_bijUR :=
  ⌜same_prov_kind l1.1 l2.1⌝ ∗ ⌜l1.2 = l2.2⌝ ∗ heap_bij_shared l1.1 l2.1.

Global Instance loc_in_bij_Persistent l1 l2 : Persistent (loc_in_bij l1 l2).
Proof. apply _. Qed.

Lemma loc_in_bij_same_prov_kind l1 l2 :
  loc_in_bij l1 l2 ⊢ ⌜same_prov_kind l1.1 l2.1⌝.
Proof. by iIntros "[% ?]". Qed.

Definition val_in_bij (v1 v2 : val) : uPred heap_bijUR :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => ⌜n1 = n2⌝
  | ValBool b1, ValBool b2 => ⌜b1 = b2⌝
  | ValFn f1, ValFn f2 => ⌜f1 = f2⌝
  | ValLoc l1, ValLoc l2 => loc_in_bij l1 l2
  | _, _ => False
  end.

Global Instance val_in_bij_Persistent v1 v2 : Persistent (val_in_bij v1 v2).
Proof. destruct v1, v2 => /=; apply _. Qed.

Lemma big_sepL2_ValNum_inv_r vl zl :
  ([∗ list] y1;y2 ∈ vl;(ValNum <$> zl), val_in_bij y1 y2) -∗
  ⌜vl = (ValNum <$> zl)⌝.
Proof.
  iIntros "Hvl".
  iInduction vl as [|v] "IH" forall (zl); csimpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. done. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[Hv ?]"; subst.
  destruct zl; simplify_eq/=. destruct v => //=. iDestruct "Hv" as %?.
  iDestruct ("IH" with "[$]") as %?.
  naive_solver.
Qed.

Lemma eval_binop_bij o v1 v2 v1' v2' v:
  eval_binop o v1 v2 = Some v →
  val_in_bij v1' v1 -∗
  val_in_bij v2' v2 -∗
  ∃ v', ⌜eval_binop o v1' v2' = Some v'⌝ ∗ val_in_bij v' v.
Proof.
  iIntros (?) "??".
  destruct o, v1, v2, v1', v2' => //= *; unfold loc_in_bij; iDestruct!; iSplit!; unfold loc_in_bij; iSplit!.
  lia.
Qed.

(** * heap_in_bij *)
Definition heap_in_bij (bij : heap_bij) (h h' : heap_state) : uPred heap_bijUR :=
  ∀ p1 p2 o,
  ⌜hb_bij bij !! p2 = Some (HBShared p1)⌝ -∗

  ⌜(is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))⌝
  ∗
  ∀ v1 v2,
  ⌜h.(h_heap)  !! (p1, o) = Some v1⌝ -∗
  ⌜h'.(h_heap) !! (p2, o) = Some v2⌝ -∗
  val_in_bij v1 v2.

Global Instance heap_in_bij_Persistent bij h h': Persistent (heap_in_bij bij h h').
Proof. apply _. Qed.

Lemma heap_in_bij_mono_bij bij bij' h h':
  (∀ p1 p2, hb_bij bij' !! p2 = Some (HBShared p1) → hb_bij bij !! p2 = Some (HBShared p1)) →
  heap_in_bij bij  h h' -∗
  heap_in_bij bij' h h'.
Proof. iIntros (?) "Hh". iIntros (????). iApply "Hh". iPureIntro. naive_solver. Qed.

Lemma heap_in_bij_alive bij h1 h2 l1 l2:
  heap_alive h2 l2 →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  ⌜heap_alive h1 l1⌝.
Proof.
  iIntros (???) "Hh". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  unfold heap_in_bij, heap_alive in *. iDestruct ("Hh" with "[//]") as "[% ?]".
  iPureIntro. naive_solver.
Qed.

Lemma heap_in_bij_lookup bij h1 h2 l1 l2 v:
  h_heap h2 !! l2 = Some v →
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  ∃ v', ⌜h_heap h1 !! l1 = Some v'⌝ ∗ val_in_bij v' v.
Proof.
  iIntros (???) "Hh". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  iDestruct ("Hh" with "[//]") as "[%Hx Hv]". move: Hx => [_ Hx].
  have [??]:= Hx ltac:(done). iSplit!. by iApply "Hv".
Qed.

Lemma heap_in_bij_update bij h1 h2 l1 l2 v1 v2:
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  l1.2 = l2.2 →
  heap_in_bij bij h1 h2 -∗
  val_in_bij v1 v2 -∗
  heap_in_bij bij (heap_update h1 l1 v1) (heap_update h2 l2 v2).
Proof.
  iIntros (??) "Hh Hv". destruct l1 as [p1 ?], l2 as [p2 o]; simplify_eq/=.
  iIntros (p1' p2' o' ?) => /=. iDestruct ("Hh" with "[//]") as "[%Hh1 Hh2]". iSplit.
  - iPureIntro. by rewrite !lookup_alter_is_Some.
  - iIntros (???%lookup_alter_Some?%lookup_alter_Some); destruct!; simplify_bij => //.
    by iApply "Hh2".
Qed.

Lemma heap_in_bij_update_r bij h1 h2 l2 v2:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij h1 h2 -∗
  heap_in_bij bij h1 (heap_update h2 l2 v2).
Proof.
  iIntros (?) "Hh". iIntros (????).
  rewrite !lookup_alter_ne. 1: by iApply "Hh".
  naive_solver.
Qed.

Lemma heap_in_bij_share h pi ps hi hs bij H Hkind:
  (∀ o, h_heap hi !! (pi, o) = h !! o) →
  (∀ o, h_heap hs !! (ps, o) = h !! o) →
  heap_in_bij bij hi hs -∗
  ([∗ map] v∈h, val_in_bij v v) -∗
  heap_in_bij (hb_share pi ps bij H Hkind) hi hs.
Proof.
  iIntros (Hi Hs) "Hh Hv". iIntros (p1 p2 o) => /=. iIntros ([[??]|[??]]%lookup_insert_Some); simplify_eq.
  - rewrite Hi Hs. iSplit; [done|]. iIntros (????). simplify_eq.
    by iDestruct (big_sepM_lookup with "Hv") as "?".
  - have ? : p1 ≠ pi. { contradict H. apply elem_of_hb_provs_i. naive_solver. }
    by iApply "Hh".
Qed.

Lemma heap_in_bij_alloc l1 l2 hi hs n bij H Hkind:
  heap_is_fresh hi l1 →
  heap_is_fresh hs l2 →
  heap_in_bij bij hi hs -∗
  heap_in_bij (hb_share l1.1 l2.1 bij H Hkind) (heap_alloc hi l1 n) (heap_alloc hs l2 n).
Proof.
  iIntros ([Hi1 ?] [Hi2 ?]) "Hh". iIntros (p1 p2 o) => /=. iIntros ([[??]|[??]]%lookup_insert_Some); simplify_eq.
  - destruct l1 as [p1 ?], l2 as [p2 ?]; simplify_eq/=.
    rewrite !lookup_union_l.
    2: { apply eq_None_ne_Some => ??. apply Hi2. by eapply (lookup_heap_Some_elem_of_h_provs (_,_)). }
    2: { apply eq_None_ne_Some => ??. apply Hi1. by eapply (lookup_heap_Some_elem_of_h_provs (_,_)). }
    iSplit.
    + iPureIntro. by rewrite !lookup_kmap.
    + iIntros (??). rewrite !lookup_kmap. iIntros ([??]%zero_block_lookup_Some [??]%zero_block_lookup_Some). naive_solver.
  - have ? : p1 ≠ l1.1. { contradict H. apply elem_of_hb_provs_i. naive_solver. }
    iDestruct ("Hh" with "[//]") as "[Hh1 Hh2]".
    rewrite !lookup_union_r ?lookup_kmap_None. 1: by iSplit.
    all: move => ??; naive_solver.
Qed.

Lemma heap_in_bij_alloc_r l2 hi hs n bij:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij hi (heap_alloc hs l2 n).
Proof.
  iIntros (?) "Hh". iIntros (????). rewrite lookup_union_r. 1: by iApply "Hh".
  apply lookup_kmap_None; [apply _|]. naive_solver.
Qed.

Lemma heap_in_bij_free hi hs l1 l2 bij:
  hb_bij bij !! l2.1 = Some (HBShared l1.1) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij (heap_free hi l1) (heap_free hs l2).
Proof.
  iIntros (?) "Hh". iIntros (p1 p2 o ?).
  iDestruct ("Hh" $! p1 p2 o with "[//]") as "[%Hh1 Hh2]".
  iSplit => /=.
  - iPureIntro. rewrite !map_lookup_filter /=. destruct (h_heap hi !! (p1, o)), (h_heap hs !! (p2, o)) => //=.
    all: repeat case_guard => //; simplify_bij; naive_solver.
  - iIntros (??). rewrite !map_lookup_filter. iIntros ([?[??]]%bind_Some [?[??]]%bind_Some).
    repeat case_guard => //; simplify_eq/=. by iApply "Hh2".
Qed.

Lemma heap_in_bij_free_r l2 hi hs bij:
  (∀ p, hb_bij bij !! l2.1 = Some (HBShared p) → False) →
  heap_in_bij bij hi hs -∗
  heap_in_bij bij hi (heap_free hs l2).
Proof.
  iIntros (?) "Hh". iIntros (????) => /=. rewrite map_lookup_filter_true. 1: by iApply "Hh".
  naive_solver.
Qed.

(** * heap_bij_inv *)
Definition heap_bij_inv (hi hs : heap_state) : uPred heap_bijUR :=
  ∃ bij, ⌜dom (hb_bij bij) ⊆  h_provs hs⌝ ∗
         ⌜hb_provs_i bij ⊆ h_provs hi⌝ ∗
         ⌜heap_preserved (hb_priv_s bij) hs⌝ ∗
         ⌜heap_preserved (hb_priv_i bij) hi⌝ ∗
         ([∗ map] p2↦p1∈ hb_shared bij, heap_bij_shared p1 p2) ∗
         heap_bij_auth bij ∗
         heap_in_bij bij hi hs ∗
         heap_bij_statics (h_static_provs hi) ∗
         heap_bij_statics (h_static_provs hs).

Lemma heap_bij_inv_lookup hi hs li ls v:
  h_heap hs !! ls = Some v →
  heap_bij_inv hi hs -∗
  loc_in_bij li ls -∗
  ∃ v', ⌜h_heap hi !! li = Some v'⌝ ∗ val_in_bij v' v.
Proof.
  iIntros (?) "[% [% [% [% [% [? [Ha [Hbij ?]]]]]]]] [% [% ?]]".
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
  by iApply (heap_in_bij_lookup with "[$]").
Qed.

Lemma heap_bij_inv_alive hi hs li ls:
  heap_alive hs ls →
  heap_bij_inv hi hs -∗
  loc_in_bij li ls -∗
  ⌜heap_alive hi li⌝.
Proof.
  iIntros (?) "[% [% [% [% [% [? [Ha [Hbij ?]]]]]]]] [% [% ?]]".
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
  by iApply (heap_in_bij_alive with "[$]").
Qed.

Lemma heap_bij_inv_lookup_s l hi hs hs':
  heap_bij_inv hi hs -∗
  heap_bij_const_s l.1 hs' -∗
  ⌜h_heap hs !! l = hs' !! l.2⌝.
Proof.
  iIntros "[% [% [% [%Hs [% [? [Ha [Hbij ?]]]]]]]] Hl".
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %?.
  iPureIntro. apply Hs. by apply hb_priv_s_lookup_Some.
Qed.

Lemma heap_bij_inv_update hi hs li ls vi vs:
  heap_bij_inv hi hs -∗
  loc_in_bij li ls -∗
  val_in_bij vi vs -∗
  heap_bij_inv (heap_update hi li vi) (heap_update hs ls vs).
Proof.
  iIntros  "[% [% [% [% [% [? [Ha [Hbij [??]]]]]]]]] [% [% ?]] ?".
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
  iExists _. iSplit!; [done|done| | |done|done|..].
  - apply heap_preserved_update; [done|]. rewrite hb_priv_s_lookup_None. naive_solver.
  - apply heap_preserved_update; [done|]. by apply: hb_disj.
  - by iApply (heap_in_bij_update with "[$]").
Qed.

Lemma heap_bij_inv_update_s l v hi hs hs' :
  heap_bij_inv hi hs -∗
  heap_bij_const_s l.1 hs' ==∗
  heap_bij_inv hi (heap_update hs l v) ∗ heap_bij_const_s l.1 (h_block (heap_update hs l v) l.1).
Proof.
  iIntros "[% [% [% [% [% [? [Ha [Hbij [??]]]]]]]]] Hcont".
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %Hl1.
  iMod (heap_bij_update_const_s with "[$]") as "[? $]". iModIntro.
  iExists _. iFrame. repeat iSplit; try iPureIntro.
  - rewrite dom_insert_L /=. move: Hl1 => /(elem_of_dom_2 _ _ _). set_solver.
  - intros b Hb. apply hb_provs_i_update_const_s in Hb. naive_solver.
  - rewrite hb_priv_s_update_const_s. apply: heap_preserved_insert_const.
    apply heap_preserved_update; [|by simplify_map_eq].
    apply: heap_preserved_mono; [done|]. apply delete_subseteq.
  - done.
  - rewrite hb_shared_update_const_s; [done|naive_solver].
  - iApply heap_in_bij_update_r; [move => /=??; simplify_map_eq|].
    iApply heap_in_bij_mono_bij; [|done]. move => /= ?? /lookup_insert_Some?. naive_solver.
  - by rewrite h_static_provs_heap_update.
Qed.

Lemma heap_bij_inv_alloc_s hi hs ls n:
  heap_is_fresh hs ls →
  heap_bij_inv hi hs ==∗
  heap_bij_inv hi (heap_alloc hs ls n) ∗ heap_bij_const_s ls.1 (h_block (heap_alloc hs ls n) ls.1).
Proof.
  iIntros ([Hnotin [??]])  "[% [%Hsub [% [% [% [? [Ha [Hbij [??]]]]]]]]]".
  iMod (heap_bij_alloc_const_s with "[$]") as "[? $]". { by move => /Hsub. } iModIntro.
  iExists _. iFrame. repeat iSplit; try iPureIntro.
  - rewrite h_provs_heap_alloc //= dom_insert_L.
    set_solver.
  - move => b' /hb_provs_i_update_const_s Hb'. eauto.
  - rewrite hb_priv_s_update_const_s. apply: heap_preserved_insert_const.
    apply heap_preserved_alloc.
    + apply: heap_preserved_mono; [done|]. apply delete_subseteq.
    + rewrite lookup_delete_None. naive_solver.
  - done.
  - rewrite hb_shared_update_const_s; [done|]. by intros ? ?%elem_of_dom_2%Hsub.
  - iApply heap_in_bij_alloc_r; [move => /=??; simplify_map_eq|].
    iApply heap_in_bij_mono_bij; [|done]. move => /= ?? /lookup_insert_Some?. naive_solver.
  - by rewrite h_static_provs_heap_alloc.
Qed.

Lemma heap_bij_inv_alloc hi hs li ls n:
  heap_is_fresh hi li →
  heap_is_fresh hs ls →
  heap_bij_inv hi hs ==∗
  heap_bij_inv (heap_alloc hi li n) (heap_alloc hs ls n) ∗ loc_in_bij li ls.
Proof.
  iIntros ([?[??]] [?[??]])  "[% [% [%Hsub [% [% [? [Ha [Hbij [??]]]]]]]]]".
  have Hni2 : li.1 ∉ hb_provs_i bij.
  { by move => /Hsub. }
  unshelve iMod (heap_bij_alloc_shared with "[$]") as "[Ha #$]"; [done| | |].
  { abstract (by destruct ls.1, li.1). }
  { abstract set_solver. }
  iModIntro. iSplit; [|iSplit; iPureIntro; [by destruct ls.1, li.1|congruence]].
  iExists _. iFrame "Ha". iSplit!.
  - set_solver.
  - move => b' /hb_provs_i_share. set_solver.
  - rewrite hb_priv_s_share. apply heap_preserved_alloc; [|by simplify_map_eq].
    apply: heap_preserved_mono; [done|]. apply delete_subseteq.
  - apply heap_preserved_alloc; [done|]. apply eq_None_ne_Some_2 => ??.
    apply Hni2. apply elem_of_hb_provs_i. naive_solver.
  - rewrite hb_shared_share. by iApply big_sepM_insert_2.
  - iApply heap_in_bij_alloc; [eexists; by split!..| done].
  - by rewrite h_static_provs_heap_alloc.
  - by rewrite h_static_provs_heap_alloc.
Qed.

Lemma heap_bij_inv_alloc_list hi hi' hs hs' lsi lss xs:
  heap_alloc_list xs lsi hi hi' →
  heap_alloc_list xs lss hs hs' →
  heap_bij_inv hi hs ==∗
  heap_bij_inv hi' hs' ∗ [∗ list] li;ls∈lsi;lss, loc_in_bij li ls.
Proof.
  iIntros (Hi Hs) "Hinv".
  iInduction xs as [] "IH" forall (lsi lss hi hi' hs hs' Hi Hs); simplify_eq/=; destruct!/=.
  { by iFrame. }
  iMod (heap_bij_inv_alloc with "Hinv") as "[Hinv $]"; [done..|].
  by iApply "IH".
Qed.

Lemma heap_bij_inv_range hi hs li ls n:
  heap_range hs ls n →
  heap_bij_inv hi hs -∗
  loc_in_bij li ls -∗
  ⌜heap_range hi li n⌝.
Proof.
  iIntros (Hr)  "[% [% [% [% [% [? [Ha [Hbij ?]]]]]]]] [% [% ?]]".
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?.
  iIntros (a ?). iDestruct ("Hbij" $! _ _ a.2 with "[//]") as "[% _]".
  iPureIntro. destruct a, li, ls; simplify_eq/=. etrans; [done|]. by apply Hr.
Qed.

Lemma heap_bij_inv_free_s ls hi hs hs':
  is_ProvBlock ls.1 →
  heap_bij_inv hi hs -∗
  heap_bij_const_s ls.1 hs' ==∗
  heap_bij_inv hi (heap_free hs ls).
Proof.
  iIntros "%Hls [% [%Hsubs [% [% [% [? [Ha [Hbij [??]]]]]]]]] Hl".
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %?.
  iMod (heap_bij_update_const_s with "[$]") as "[Ha ?]". iModIntro.
  iExists _. iFrame "Ha". iSplit!.
  - rewrite dom_insert_L.
    have : ls.1 ∈ dom (hb_bij bij) by apply elem_of_dom.
    set_solver.
  - move => ? /hb_provs_i_update_const_s. eauto.
  - rewrite hb_priv_s_update_const_s. apply: heap_preserved_insert_const.
    apply heap_preserved_free; [|by simplify_map_eq].
    apply: heap_preserved_mono; [done|]. apply delete_subseteq.
  - rewrite hb_shared_update_const_s; [done|naive_solver].
  - iApply heap_in_bij_free_r.
    + move => ? /= /lookup_insert_Some. naive_solver.
    + iApply (heap_in_bij_mono_bij with "[$]"). move => /= ?? /lookup_insert_Some. naive_solver.
  - done.
  - by rewrite h_static_provs_heap_free.
Qed.

Lemma heap_bij_inv_free hi hs li ls :
  is_ProvBlock ls.1 →
  heap_bij_inv hi hs -∗
  loc_in_bij li ls -∗
  heap_bij_inv (heap_free hi li) (heap_free hs ls).
Proof.
  iIntros "%Hbs [% [% [% [% [% [? [Ha [Hbij [??]]]]]]]]] [%Hkind [% ?]]".
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %Hbij.
  iExists _. iFrame "Ha". iSplit!.
  - apply heap_preserved_free; [done|]. apply hb_priv_s_lookup_None. naive_solver.
  - apply heap_preserved_free; [done|]. by apply: hb_disj.
  - by iApply heap_in_bij_free.
Qed.

Lemma heap_bij_inv_free_list hi hs hs' lis lss lis' lss':
  heap_free_list lss hs hs' →
  lis.*2 = lss.*2 →
  lis' = lis.*1 →
  lss' = lss.*1 →
  heap_bij_inv hi hs -∗
  ([∗ list] li;ls∈lis';lss', loc_in_bij li ls) -∗
  ∃ hi', ⌜heap_free_list lis hi hi'⌝ ∗ heap_bij_inv hi' hs'.
Proof.
  iIntros (Hf Hl2 -> ->) "Hinv Hls".
  iInduction lss as [|ls lss] "IH" forall (hi hs hs' lis Hf Hl2);
      simplify_eq/=; destruct lis as [|li lis] => //; destruct!/=.
  { iSplit!. }
  iDestruct "Hls" as "[Hl Hls]".
  iDestruct (loc_in_bij_same_prov_kind with "Hl") as "%Hkind".
  iDestruct (heap_bij_inv_range with "[$] [$]") as %?; [done|].
  iDestruct ((heap_bij_inv_free _ _ li.1 ls.1) with "[$]") as "Hinv"; [done|].
  iDestruct ("IH" with "[//] [//] [Hl Hinv] [$]") as (??) "?"; first by iApply "Hinv".
  iExists _. iFrame. iPureIntro. replace li.2 with ls.2. split!.
  by erewrite same_prov_kind_is_ProvBlock_iff.
Qed.

(* specialized to the same provenance and heap on both sides for now
since this suffices for statics *)
Lemma heap_bij_inv_share hi hs p h:
  heap_bij_inv hi hs -∗
  heap_bij_const_i p h -∗
  heap_bij_const_s p h -∗
  ([∗ map] v∈h, val_in_bij v v) ==∗
  heap_bij_inv hi hs ∗ loc_in_bij (p, 0%Z) (p, 0%Z).
Proof.
  iIntros "[% [%Hsubs [% [%Hps [%Hpi [? [Ha [Hbij [??]]]]]]]]] Hi Hs Hv".
  iDestruct (heap_bij_const_i_lookup with "[$] [$]") as %?.
  iDestruct (heap_bij_const_s_lookup with "[$] [$]") as %?.
  iMod (heap_bij_free_const_i with "[$]") as "?".
  iMod (heap_bij_free_const_s with "[$]") as "?".
  have Hi : hb_provs_i (hb_delete_s p (hb_delete_i p bij)) = hb_provs_i bij ∖ {[p]}. {
    rewrite hb_provs_i_delete_s ?hb_provs_i_delete_i //=.
    - rewrite elem_of_hb_shared_i. move => [? /hb_disj?]. naive_solver.
    - rewrite hb_shared_s_delete_i elem_of_hb_shared_s => -[??]. simplify_bij.
  }
  unshelve iMod (heap_bij_alloc_shared with "[$]") as "[? #$]" => /=.
  { abstract (simpl; rewrite Hi; set_solver). }
  { done. }
  { set_solver. }
  iModIntro. iSplit!. iExists _. iFrame.
  iSplit!.
  - etrans; [|done]. rewrite dom_insert_L dom_delete_L.
    have : p ∈ dom (hb_bij bij) by apply elem_of_dom.
    set_solver.
  - etrans; [|done]. etrans; [apply hb_provs_i_share|].
    have : p ∈ hb_provs_i bij by apply elem_of_hb_provs_i; naive_solver.
    rewrite Hi. set_solver.
  - apply: heap_preserved_mono; [done|].
    rewrite hb_priv_s_share hb_priv_s_delete_s hb_priv_s_delete_i.
    etrans; [apply delete_subseteq|].
    by apply delete_subseteq.
  - apply: heap_preserved_mono; [done|]. by apply delete_subseteq.
  - rewrite hb_shared_share. iApply big_sepM_insert_2; [done|].
    rewrite hb_shared_delete_s hb_shared_delete_i.
    by iApply big_sepM_delete_2.
  - iApply (heap_in_bij_share with "[Hbij] Hv").
    + move => ?. by apply Hpi.
    + move => ?. by apply Hps, hb_priv_s_lookup_Some.
    + iApply (heap_in_bij_mono_bij with "[$]") => /=.
      move => ??. rewrite lookup_delete_Some. naive_solver.
Qed.

Lemma heap_bij_inv_share_big hi hs m:
  heap_bij_inv hi hs -∗
  ([∗ map] p↦h∈m, heap_bij_const_i p h) -∗
  ([∗ map] p↦h∈m, heap_bij_const_s p h) -∗
  ([∗ map] p↦h∈m, [∗ map] v∈h, val_in_bij v v) ==∗
  heap_bij_inv hi hs ∗ ([∗ map] p↦h∈m, loc_in_bij (p, 0%Z) (p, 0%Z)).
Proof.
  iIntros "Hinv Hi Hs Hv".
  iInduction m as [|???] "IH" using map_ind. { iModIntro. by iFrame. }
  rewrite !big_sepM_insert //.
  iDestruct!. iMod (heap_bij_inv_share with "[$] [$] [$] [$]") as "[? $]".
  by iApply ("IH" with "[$] [$] [$] [$]").
Qed.

Definition rec_heap_bij_init (h0 : gmap prov (gmap Z val)) : uPred heap_bijUR :=
  (([∗ map]p↦v∈h0, heap_bij_const_i p v) ∗ ([∗ map]p↦v∈h0, heap_bij_const_s p v)).

Lemma rec_heap_bij_init_union h1 h2:
  h1 ##ₘ h2 →
  rec_heap_bij_init (h1 ∪ h2) ⊣⊢ rec_heap_bij_init h1 ∗ rec_heap_bij_init h2.
Proof.
  move => Hdisj. rewrite /rec_heap_bij_init.
  rewrite !big_sepM_union //. iSplit; iIntros!; iFrame.
Qed.

Lemma heap_bij_inv_share_init hi hs f statics :
  heap_bij_inv hi hs -∗
  rec_heap_bij_init (fd_init_heap f statics) ==∗
  ([∗ list] l ∈ static_locs f statics, loc_in_bij l l) ∗ heap_bij_inv hi hs.
Proof.
  iIntros "Hinv [Hi Hs]".
  iMod (heap_bij_inv_share_big with "Hinv Hi Hs []") as "[$ ?]". {
    iApply big_sepM_intro. iIntros "!>" (??[?[?[?[??]]]]%fd_init_heap_lookup_Some).
    simplify_eq. iApply big_sepM_intro.
    iIntros "!>" (??[??]%zero_block_lookup_Some); by simplify_eq/=.
  }
  iModIntro. rewrite /fd_init_heap.
  rewrite big_sepM_list_to_map. 2: {
    apply NoDup_alt => ???. rewrite !list_lookup_fmap_Some.
    setoid_rewrite lookup_zip_with_Some.
    setoid_rewrite static_provs_lookup_Some.
    naive_solver. }
  rewrite big_sepL_zip_with /= /static_locs big_sepL_fmap.
  iApply (big_sepL_impl with "[$]"). iIntros "!>" (???%static_provs_lookup_Some) "?".
  case_match eqn: Heq => //. apply lookup_ge_None in Heq. lia.
Qed.

Lemma heap_bij_inv_share_inits hi hs fns :
  heap_bij_inv hi hs -∗
  rec_heap_bij_init (fds_init_heap fns) ==∗
  ([∗ map] f↦fn∈fns, [∗ list] l ∈ static_locs f fn, loc_in_bij l l) ∗ heap_bij_inv hi hs.
Proof.
  iIntros "Hinv Hinit".
  iInduction fns as [|f fn fns Hf] "IH" using map_ind forall (hi hs).
  { iModIntro. iFrame. done. }
  rewrite fds_init_heap_insert // rec_heap_bij_init_union.
  2: by apply fds_init_heap_map_disjoint.
  iDestruct "Hinit" as "[? Hinit2]".
  iMod ("IH" with "Hinv Hinit2") as "[? Hinv]".
  iMod (heap_bij_inv_share_init with "[$] [$]") as "[??]".
  iModIntro. rewrite big_sepM_insert //. iFrame.
Qed.

Program Definition heap_bij_init_bij (h0 : gmap prov (gmap Z val)) : heap_bij :=
  hb_update_const_s_big h0 (hb_update_const_i_big h0 ∅ _).
Next Obligation. move => ? ?? /elem_of_hb_shared_i. naive_solver. Qed.

Lemma heap_bij_init ps :
 satisfiable (heap_bij_auth ∅ ∗ heap_bij_statics ps).
Proof.
  apply: (satisfiable_init (Some (to_agree ps), (_, _))). { split; first done. split; by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1)). }
  rewrite pair_split.
  setoid_rewrite pair_split.
  rewrite (pair_split (Some _)).
  rewrite !uPred.ownM_op.
  rewrite pair_op_2 !uPred.ownM_op.
  iIntros!. by iFrame.
Qed.

Lemma heap_bij_inv_init bs :
  satisfiable (heap_bij_inv (heap_from_blocks bs) (heap_from_blocks bs) ∗ rec_heap_bij_init bs).
Proof.
  apply: satisfiable_bmono; [apply heap_bij_init|].
  iIntros "[? #?]".
  unshelve iMod (heap_bij_alloc_const_i_big bs with "[$]") as "[? $]".
  { abstract (rewrite hb_shared_i_empty; set_solver). } { rewrite hb_provs_i_empty. set_solver. }
  iMod (heap_bij_alloc_const_s_big bs with "[$]") as "[? $]". { set_solver. }
  iModIntro. iExists _. iFrame "∗#". iSplit!.
  - rewrite right_id_L dom_fmap_L //.
  - rewrite hb_provs_i_hb_update_const_s_big ?hb_provs_i_hb_update_const_i_big
      ?hb_shared_s_hb_update_const_i_big ?hb_shared_s_empty ?hb_provs_i_empty ?right_id_L //.
  - move => [??]/=? /hb_priv_s_lookup_Some/=. rewrite right_id_L. move => /lookup_fmap_Some[?[??]].
    rewrite lookup_gmap_uncurry. by simplify_option_eq.
  - rewrite right_id_L. move => [??]/=??. rewrite lookup_gmap_uncurry. by simplify_option_eq.
  - iApply big_sepM_intro. iIntros "!>" (?? Hs). exfalso.
    move: Hs => /hb_shared_lookup_Some/=. rewrite right_id_L. move => /lookup_fmap_Some[?[??]]. done.
  - iIntros (??? Hl). exfalso. move: Hl => /=. rewrite right_id_L. move => /lookup_fmap_Some[?[??]]. done.
Qed.

(** * Definition of [rec_heap_bij] *)
Definition rec_heap_bij_pre (e : rec_event) (s : unit) : prepost (rec_event * unit) heap_bijUR :=
  let vsi := vals_of_event e.2 in
  let hi := heap_of_event e.2 in
  pp_quant $ λ vss,
  pp_quant $ λ hs,
  pp_star (heap_bij_inv hi hs ∗ [∗ list] v1;v2∈vsi;vss, val_in_bij v1 v2) $
  pp_end ((e.1, event_set_vals_heap e.2 vss hs), tt).

Definition rec_heap_bij_post (e : rec_event) (s : unit) : prepost (rec_event * unit) heap_bijUR :=
  let vss := vals_of_event e.2 in
  let hs := heap_of_event e.2 in
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_star (heap_bij_inv hi hs ∗ [∗ list] v1;v2∈vsi;vss, val_in_bij v1 v2) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), tt).

Definition rec_heap_bij_trans (m : mod_trans rec_event) : mod_trans rec_event :=
  prepost_trans rec_heap_bij_pre rec_heap_bij_post m.

Definition rec_heap_bij (h0 : gmap prov (gmap Z val)) (m : module rec_event) : module rec_event :=
  Mod (rec_heap_bij_trans m.(m_trans)) (SMFilter, m.(m_init), (PPOutside, tt,
   uPred_shrink (rec_heap_bij_init h0))).

Lemma rec_heap_bij_trefines m m' h0 `{!VisNoAng m.(m_trans)}:
  trefines m m' →
  trefines (rec_heap_bij h0 m) (rec_heap_bij h0 m').
Proof. move => ?. by apply: prepost_mod_trefines. Qed.

(** ** rec_heap_bij_N *)
Definition rec_heap_bij_N n h0 (m: module rec_event) : module rec_event :=
  Nat.iter n (rec_heap_bij h0) m.

Global Instance rec_heap_bij_N_vis_no_all n m h0 `{!VisNoAng m.(m_trans)} :
  VisNoAng (rec_heap_bij_N n h0 m).(m_trans).
Proof. elim: n => //= ??. apply _. Qed.

(** * Proof techniques for [rec_heap_bij] *)
Definition rec_heap_bij_call (n : ordinal) (fns1 fns2 : gmap string fndef) INV :=
  (∀ n' f es1' es2' K1' K2' es1 es2 vs1' vs2' h1' h2' b r rf',
      RecExprFill es1' K1' (Call (Val (ValFn f)) es1) →
      RecExprFill es2' K2' (Call (Val (ValFn f)) es2) →
      n' ⊆ n →
      Forall2 (λ e v, e = Val v) es1 vs1' →
      Forall2 (λ e v, e = Val v) es2 vs2' →
      satisfiable (heap_bij_inv h1' h2' ∗ ([∗ list] v1;v2∈vs1';vs2', val_in_bij v1 v2) ∗ INV ∗ r ∗ rf') →
      (∀ v1'' v2'' h1'' h2'' rf'',
        satisfiable (heap_bij_inv h1'' h2'' ∗ val_in_bij v1'' v2'' ∗ INV ∗ r ∗ rf'') →
        Rec (expr_fill K1' (Val v1'')) h1'' fns1
            ⪯{rec_trans, rec_heap_bij_trans rec_trans, n', true}
        (SMProg, Rec (expr_fill K2' (Val v2'')) h2'' fns2, (PPInside, tt, uPred_shrink rf''))) →
      Rec es1' h1' fns1
          ⪯{rec_trans, rec_heap_bij_trans rec_trans, n', b}
      (SMProg, Rec es2' h2' fns2, (PPInside, tt, uPred_shrink rf'))).

Definition rec_heap_bij_return n fns1 fns2 Ki Ks r INV :=
  (∀ n' v1 v2 h1' h2' rf' b,
      n' ⊆ n →
      satisfiable (heap_bij_inv h1' h2' ∗ val_in_bij v1 v2 ∗ INV ∗ r ∗ rf') →
      Rec (expr_fill Ki (Val v1)) h1' fns1
        ⪯{rec_trans, rec_heap_bij_trans rec_trans, n', b}
      (SMProg, Rec (expr_fill Ks (Val v2)) h2' fns2, (PPInside, (), uPred_shrink rf'))).

Lemma rec_heap_bij_call_mono n n' fns1 fns2 INV :
  rec_heap_bij_call n fns1 fns2 INV →
  n' ⊆ n →
  rec_heap_bij_call n' fns1 fns2 INV .
Proof.
  intros Hprf ???????????????????????.
  eapply Hprf; eauto. by etrans.
Qed.

Lemma rec_heap_bij_return_mono n n' fns1 fns2 K1 K2 r INV:
  rec_heap_bij_return n fns1 fns2 K1 K2 r INV →
  n' ⊆ n →
  rec_heap_bij_return n' fns1 fns2 K1 K2 r INV.
Proof.
  intros Hprf ??????????.
  eapply Hprf; eauto. by etrans.
Qed.

Lemma rec_heap_bij_proof INV fns1 fns2 h0 :
  dom fns1 = dom fns2 →
  (∀ f fn1, fns1 !! f = Some fn1 → ∃ fn2, fns2 !! f = Some fn2
                                          ∧ length (fd_args fn1) = length (fd_args fn2)
                                          ∧ fd_static_vars fn1 = fd_static_vars fn2) →
  (∀ hi hs, rec_heap_bij_init h0 -∗ heap_bij_inv hi hs ==∗ INV ∗ heap_bij_inv hi hs) →
  (∀ n K1 K2 f fn1 fn2 vs1 vs2 h1 h2 r rf,
      fns1 !! f = Some fn1 →
      fns2 !! f = Some fn2 →
      length vs1 = length (fd_args fn1) →
      length vs2 = length (fd_args fn2) →
      satisfiable (heap_bij_inv h1 h2 ∗ ([∗ list] v1;v2∈vs1;vs2, val_in_bij v1 v2) ∗ INV ∗ r ∗ rf) →

      rec_heap_bij_call n fns1 fns2 INV →
      rec_heap_bij_return n fns1 fns2 K1 K2 r INV →

      Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f (fd_static_vars fn1) $ subst_l fn1.(fd_args) vs1 (fd_body fn1))) h1 fns1
          ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, false}
      (SMProg, Rec (expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f (fd_static_vars fn2) $ subst_l fn2.(fd_args) vs2 (fd_body fn2))) h2 fns2, (PPInside, tt, uPred_shrink rf))) →
  trefines (rec_mod fns1) (rec_heap_bij h0 (rec_mod fns2)).
Proof.
  move => Hdom Hlen Hinit Hf.
  rewrite (lock (dom _)) in Hdom. unfold rec_heap_bij.
  etrans. 2: {
    apply (mod_prepost_impl_prop _ _ _ _ INV); [apply _| ] => /=.
    iIntros (???) "? [[? ?] $]".
    iMod (Hinit with "[$] [$]") as "[$ $]". by iFrame. }
  pose (R := λ (b : bool) (s1 s2 : (unit * uPred heap_bijUR)), (if b then s1.2 ≡ s2.2 else True) ∧ (s2.2 ⊢ INV ∗ (INV -∗ s2.2))).
  apply: (rec_prepost_proof R); unfold R; [| | naive_solver.. |].
  { destruct b.
    - move => ??? [-> ?] //.
    - move => //. }
  { split!. iIntros "$". iIntros "$". }
  move => n K1 K2 f fn1 vs1 h1 [] r1 /= [_ Hstat] Hfn1 /= vs2 h2 rf Hsat.
  iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
  have [?[??]]:= (Hlen _ _ ltac:(done)).
  split!. move => ?. split; [lia|].
  move => Hcall Hret.
  unshelve eapply tsim_remember'. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(σfs, Rec e2 h2 fns2', (t1, _, rf')),
     ∃ K1 K2 f vs1 vs2 fn1 fn2 r rrf',
       rf' = uPred_shrink rrf' ∧
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       fns1 !! f = Some fn1 ∧
       fns2 !! f = Some fn2 ∧
       e1 = expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f (fd_static_vars fn1) $ subst_l (fd_args fn1) vs1 (fd_body fn1)) ∧
       e2 = expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f (fd_static_vars fn2) $ subst_l (fd_args fn2) vs2 (fd_body fn2)) ∧
       length vs1 = length (fd_args fn1) ∧
       σfs = SMProg ∧
       t1 = PPInside ∧
       satisfiable (heap_bij_inv h1 h2
            ∗ ([∗ list] v1;v2∈vs1;vs2, val_in_bij v1 v2)
            ∗ INV
            ∗ r ∗ rrf') ∧
       rec_heap_bij_return n' fns1 fns2 K1 K2 r INV). }
  { move => /= ??. split! => //; [lia|..]. {
      iSatMono. iFrame. iStopProof.
      etrans; [apply Hstat|]. iIntros!. iFrame. iAccu. } iSatClear.
    move => ?????????. apply: tsim_mono; [|done]. apply: Hret; [done|]. eexists [_]. split!.
    iSatMono. iIntros!. iFrame. iDestruct select (INV -∗ _)%I as "H". by iApply "H". }
  iSatClear. move => n' /= ? IH [e1 {}h1 ?] [[σfs [e2 {}h2 ?]] [[?[]]?]] ?. destruct!. simplify_eq/=.
  have [?[??]]:= (Hlen _ _ ltac:(done)).
  iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
  apply: Hf => //; [lia|..]. { iSatMono. iFrame. }
  - iSatClear. move => ? f1 es1 es2 ?? es1' es2' vs1' vs2' ????? [?] [?] ? Hall1 Hall2 ? Hret'.
    have ?: es1' = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
    have ?: es2' = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
    destruct (fns1 !! f1) eqn: ?.
    + tstep_both. split; [|naive_solver].
      move => ??. have [?[??]]:= (Hlen _ _ ltac:(done)). tstep_s. left. split! => ?. tend.
      iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
      split; [lia|].
      apply: IH; [done|]. move => ??.
      split! => //; [lia|..]. { iSatMono. iFrame. iAccu. }
      move => *. apply: tsim_mono_to_true; [naive_solver|]. etrans; [|done]. by econs.
    + apply: Hcall; [by etrans|done|..].
      { apply not_elem_of_dom. unlock in Hdom. rewrite -Hdom. by apply not_elem_of_dom. }
      1,2: by apply Forall2_fmap_l, Forall_Forall2_diag, Forall_true.
      split!. 2: { iSatMono. iIntros!. iFrame. iAccu. }
      { by iIntros "[$ $] $". }
      iSatClear. move => ????[??]????. setoid_subst. split!.
      apply: tsim_mono_b. apply: Hret'. iSatMono. iIntros!. iFrame.
      iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". by simplify_eq.
Qed.

(** * Properties of [rec_heap_bij] *)
(** ** Horizontal compositionality *)
Lemma rec_heap_bij_combine fns1 fns2 m1 m2 h01 h02 h0 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  h01 ##ₘ h02 →
  h0 = h01 ∪ h02 →
  trefines (rec_link fns1 fns2 (rec_heap_bij h01 m1) (rec_heap_bij h02 m2))
           (rec_heap_bij h0 (rec_link fns1 fns2 m1 m2)).
Proof.
  move => Hdisj ->.
  unshelve apply: prepost_link. { exact
      (λ ips s1 s2 s x1 x2 x ics1 ics2,
        ics1 = ics2 ∧
        match ips with
        | None => x ⊣⊢ x1 ∗ x2
        | Some SPLeft => x1 = (x ∗ x2)%I
        | Some SPRight => x2 = (x ∗ x1)%I
        end
      ). }
  { move => ?? [] /=*; naive_solver. }
  { split!. rewrite /rec_heap_bij_init !big_sepM_union //. iSplit; iIntros!; iFrame. }
  all: move => [] [] [] P1 P2 P ics1 ics2.
  - move => e ics' e' /= ? ? *; destruct!/=.
    setoid_subst.
    split!.
    { iSatMono. iIntros!. iFrame. }
    { by destruct e. }
  - move => e ics' e' /= ? ? *; destruct!/=.
    setoid_subst.
    split!.
    { iSatMono; iIntros!; iFrame. }
    { by destruct e. }
  - move => [? e] /= ? Hr *. destruct!/=.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    split!.
    { iSatMono; iIntros!. iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    { by destruct e. }
    { by destruct e. }
  - move => [? e] /= *; destruct!/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
  - move => [? e] /= ? *; destruct!/=.
    split!.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    { iSatMono; iIntros!; iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= ? *; destruct!/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
Qed.

(** ** Reflexivity *)
Lemma rec_heap_bij_sim_call_bind args vs' ws' es ei Ks Ki vss vsi vfi vfs n b hi hs fns1 fns2 rf r INV
  `{Hfill2: !RecExprFill ei Ki (Call (Val vfi) ((Val <$> vs') ++ (subst_map vsi <$> args)))}
  `{Hfill1: !RecExprFill es Ks (Call (Val vfs) ((Val <$> ws') ++ (subst_map vss <$> args)))}:
    satisfiable (heap_bij_inv hi hs ∗ ([∗ map] vi;vs ∈ vsi; vss, val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs'; ws', val_in_bij v w) ∗ val_in_bij vfi vfs ∗ INV ∗ r ∗ rf) →
    dom vss ⊆ dom vsi →
    rec_heap_bij_call n fns1 fns2 INV →
    (∀ vs ws hi' hs' b' n' rf' f,
      n' ⊆ n →
      satisfiable (heap_bij_inv hi' hs' ∗ ([∗ map] vi;vs ∈ vsi; vss, val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs' ++ vs; ws' ++ ws, val_in_bij v w) ∗ INV ∗ r ∗ rf') →
      Rec (expr_fill Ki (Call (Val (ValFn f)) (Val <$> (vs' ++ vs)))) hi' fns1
        ⪯{rec_trans, rec_heap_bij_trans rec_trans, n', b'}
      (SMProg, Rec (expr_fill Ks (Call (Val (ValFn f)) (Val <$> (ws' ++ ws)))) hs' fns2, (PPInside, (), uPred_shrink rf'))
    ) →
    Forall
    (λ e : expr,
       ∀ es ei hi hs n b Ki Ks r rf,
         RecExprFill es Ks (subst_map vss e)
         → RecExprFill ei Ki (subst_map vsi e)
             → rec_heap_bij_call n fns1 fns2 INV
                  → satisfiable
                      (heap_bij_inv hi hs ∗
                      ([∗ map] v1;v2 ∈ vsi;vss, val_in_bij v1 v2) ∗ INV ∗ r ∗
                      rf)
                      → rec_heap_bij_return n fns1 fns2 Ki Ks r INV
                     → Rec ei hi fns1 ⪯{rec_trans,
                     rec_heap_bij_trans rec_trans, n, b}
                     (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf))) args →
    Rec ei hi fns1
      ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, b}
    (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  intros Hsat Hdom Hfuns Hcont Hargs; destruct Hfill1 as [->], Hfill2 as [->].
  induction args as [|e args IH] in n, b, vs', ws', hs, hi, Hsat, Hcont, Hargs, Hfuns, rf |-*; simpl.
 - specialize (Hcont [] []). rewrite !app_nil_r in Hcont.
   rewrite !app_nil_r. tstep_s => ??. simplify_eq/=.
   iSatStart. iIntros!. destruct vfi => //=. iDestruct!. iSatStop.
   eapply Hcont; [done|]. iSatMono. iFrame.
 - eapply Forall_cons_1 in Hargs as [Harg Hall].
   apply: Harg.
  + eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end.
  + eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end.
  + done.
  + iSatMono. iIntros "(Hbij & #Hvals & #Hvals' & Hf & Hs & r & rf)". iFrame.
    iFrame "Hvals". iCombine "Hvals Hvals' Hf r" as "r". iExact "r".
  + simpl. iSatClear. intros n' v w h1' h2' rf' b' Hsub Hsat'. simpl.
    rewrite !cons_middle !app_assoc. change ([Val v]) with (Val <$> [v]).
    change ([Val w]) with (Val <$> [w]). rewrite -!fmap_app.
    specialize (IH (vs' ++ [v]) (ws' ++ [w]) n' b' h1' h2' rf').
    eapply IH; eauto.
    * iSatMono. iIntros!. by iFrame.
    * by apply: rec_heap_bij_call_mono.
    * intros vs ws hi' hs' b'' n'' rf'' Hsub' Hsat. rewrite -!app_assoc.
      clear IH Hall Hsat'. eapply Hcont; first by etrans.
Qed.

Lemma rec_heap_bij_sim_refl_static INV vss vsi e es ei hi hs n b Ki Ks fns1 fns2 r rf
  `{Hfill1: !RecExprFill es Ks (subst_map vss e)}
  `{Hfill2: !RecExprFill ei Ki (subst_map vsi e)}:
  dom vss ⊆ dom vsi →
  rec_heap_bij_call n fns1 fns2 INV →
  rec_heap_bij_return n fns1 fns2 Ki Ks r INV →
  is_static_expr false e →
  satisfiable (heap_bij_inv hi hs ∗ ([∗ map] v1;v2 ∈ vsi; vss, val_in_bij v1 v2) ∗ INV ∗ r ∗ rf) →
  Rec ei hi fns1 ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, b} (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  induction e as [x|v|e1 op e2 IH1 IH2|e IH|e1 e2 IH1 IH2|e e1 e2 IH IH1 IH2| x e1 e2 IH1 IH2| f args IH| | | |] in vss, vsi, hi, hs, n, b, Ks, Ki, es, ei, Hfill1, Hfill2, r, rf |-*;
    intros Hsub Hcall Hcont Hstatic Hsat;
    destruct Hfill1 as [->], Hfill2 as [->].
  - simpl. destruct (vss !! x) as [v|] eqn: Hlook; last first.
    + tstep_s. done.
    + eapply elem_of_dom_2 in Hlook as Hel.
      eapply elem_of_weaken in Hel; last done.
      eapply elem_of_dom in Hel as [w Hlook'].
      rewrite Hlook'. eapply Hcont; simpl.
      { done. }
      { iSatMono. iIntros "($ & Hm & $ & $)". iApply (big_sepM2_lookup with "Hm"); done. }
  - simpl. eapply Hcont; first done.
    iSatMono. iIntros "($ & Hm & $ & $)". destruct v; done.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstat2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: IH2; simpl; eauto; last first.
    { iSatMono. iIntros "($ & #Hv & $ & [#Hm r] & $)". iFrame "Hm". iCombine "Hm Hv r " as "r". iExact "r". }
    2: { by apply: rec_heap_bij_call_mono. }
    iSatClear. intros n'' wi ws hi'' hs'' rf'' b'' Hn'' Hsat; simpl.
    tstep_s. intros w Heval. iSatStart.
    iIntros "(Hinv & Hw & HINV & (Hsub & Hv & r) & rf)".
    iDestruct (eval_binop_bij with "Hv Hw") as "[%u [% Hu]]"; first done.
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame.
  - simpl. simpl in Hstatic.
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. intros l v' -> Hlook. iSatStart.
    iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)".
    destruct vi; try done; simpl.
    iDestruct (heap_bij_inv_lookup with "Hinv Hv") as "[%w [% #Hw]]"; first done.
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame. iFrame "Hw".
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstat2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
      iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: IH2; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hv & $ & (#Hm & r) & $)". iFrame "Hm". iCombine "Hm Hv r " as "r". iExact "r". }
    2: { by apply: rec_heap_bij_call_mono. }
    iSatClear. intros n'' wi ws hi'' hs'' rf'' b'' Hn'' Hsat; simpl.
    tstep_s. intros w -> Halive. iSatStart.
    iIntros "(Hinv & #Hw & HINV & (Hsub & Hv & r) & rf)".
    destruct vi; try done.
    iDestruct (heap_bij_inv_alive with "Hinv Hv") as "%"; first done.
    iDestruct (heap_bij_inv_update with "Hinv Hv Hw") as "Hinv".
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame. iFrame "Hw".
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic Hstatic2].
    eapply andb_True in Hstatic as [Hstatic Hstatic1].
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. intros cond ->. iSatStart.
    iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)".
    destruct vi; try done; simpl. iDestruct "Hv" as "->". iSatStop.
    tstep_i. destruct cond.
    + apply: IH1; simpl; eauto.
      { by apply: rec_heap_bij_call_mono. }
      { by apply: rec_heap_bij_return_mono. }
      iSatMono. iFrame.
    + apply: IH2; simpl; eauto.
      { by apply: rec_heap_bij_call_mono. }
      { by apply: rec_heap_bij_return_mono. }
      iSatMono. iFrame.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstatic2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. tstep_i. rewrite -!subst_subst_map_delete.
    apply: IH2; simpl; eauto.
    { set_solver. }
    { by apply: rec_heap_bij_call_mono. }
    { by apply: rec_heap_bij_return_mono. }
    iSatMono. iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)". iFrame.
    iApply (big_sepM2_insert_2 with "[Hv]"); by iFrame.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstatic2].
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: (rec_heap_bij_sim_call_bind args nil nil); simpl; eauto.
    + iSatMono. iIntros!. iFrame. iAccu.
    + by apply: rec_heap_bij_call_mono.
    + clear Hsat vs hi' hs' b' rf'. intros vs ws hi' hs' b' n'' rf' f' Hn'' Hsat'.
      apply: Hcall; simpl; eauto.
      * by etrans.
      * by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall.
      * by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall.
      * iSatMono. iIntros "($ & ? & $ & $)".
      * move => *. apply Hcont; [by etrans|done].
    + eapply Forall_forall. intros x Hx.
      eapply Forall_forall in H; last done.
      intros ???????????????. eapply H; eauto.
      simpl in Hstatic2. by eapply forallb_True, Forall_forall in Hstatic2.
  - done.
  - done.
  - done.
  - done.
Qed.

Lemma rec_heap_bij_refl fns:
  trefines (rec_mod fns) (rec_heap_bij (fds_init_heap (fd_static_vars <$> fns)) (rec_mod fns)).
Proof.
  pose (INV := ([∗ map] f↦fn∈fns, [∗ list] l ∈ static_locs f (fd_static_vars fn), loc_in_bij l l)%I).
  apply: (rec_heap_bij_proof INV).
  { done. } { naive_solver. } {
    rewrite /INV. iIntros (??) "Hinit Hinv".
    iMod (heap_bij_inv_share_inits with "Hinv Hinit"). by rewrite big_sepM_fmap.
  }
  move => n K1 K2 f fn1 fn2 vs1 v2 h1 h2 r rf ????? Hcall Hret. simplify_eq.
  rewrite !subst_l_subst_map //.
  tstep_s. pose proof (heap_alloc_list_fresh (fd_vars fn1).*2 ∅ h2) as [??].
  split!; [done|]. move => ?.
  tstep_i => ???. split!.
  have Hlen1 := (heap_alloc_list_length _ (heap_fresh_list _ _ _) _ _ ltac:(done)).
  have Hlen2 := (heap_alloc_list_length _ _ _ _ ltac:(done)).
  rewrite length_fmap in Hlen1, Hlen2.
  rewrite /subst_static !subst_l_subst_map ?length_fmap ?length_imap ?length_fmap -?subst_map_subst_map //.
  apply: (rec_heap_bij_sim_refl_static INV); last first.
  - iSatMonoBupd. iIntros "(? & Hvs & #HINV & r & $)".
    iMod (heap_bij_inv_alloc_list with "[$]") as "[$ Hl]"; [done..|iCombine "Hl" as "#Hl"].
    iModIntro.
    rewrite -!list_to_map_app. iFrame "HINV".
    iCombine "Hl r" as "r". iSplitR "r"; [| iAccu].
    iApply big_sepM2_list_to_map_2;
      rewrite ?fmap_app ?fst_zip ?snd_zip ?length_fmap ?length_imap ?length_fmap //; try lia.
    iApply (big_sepL2_app with "[Hvs]"); [done|].
    iApply big_sepL2_app; [| by rewrite big_sepL2_fmap_l big_sepL2_fmap_r].
    iClear "Hl". iApply big_sepL_sepL2_diag.
    rewrite big_sepL_fmap /=.
    rewrite /INV. by iDestruct (big_sepM_lookup with "HINV") as "?".
  - apply fd_static.
  - iSatClear. move => /= ?????????.
    tstep_s => hs' Hfrees.
    tstep_i.
    iSatStart. iIntros!.
    iDestruct (heap_bij_inv_free_list with "[$] [$]") as (??) "?"; [done|..]; last (iSatStop; split!; [done|]).
    all: rewrite ?snd_zip ?fst_zip ?length_fmap //; try lia.
    apply: Hret; [done|].
    iSatMono. iFrame.
  - done.
  - rewrite !dom_union_L !dom_list_to_map_L !fst_zip ?length_fmap ?length_imap ?length_fmap //; lia.
Qed.

(** ** Adequacy *)

Lemma rec_heap_bij_rec_closed hinit bs m :
  hinit ⊆ bs →
  let h := (heap_from_blocks bs) in
  trefines (rec_closed h (rec_heap_bij hinit m)) (rec_closed h m).
Proof.
  move => Hh h.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σm1, (σf, σ1, (pp, _, r)), σc1)
          '(σm2, σ2, σc2),
           ∃ rr, r = uPred_shrink rr ∧ σ1 = σ2 ∧ σc1 = σc2 ∧
             ((σc1 = RCStart h ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ rr = rec_heap_bij_init hinit) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = RCRunning ∧ pp = PPInside))
                             ). }
  { split!. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp []] r]]] σc1] [[σm2 σ2] σc2] ?.
  destruct!/=.
  - tstep_i. apply steps_impl_step_end => ???. inv_all/= @m_step. split!.
    tstep_s. eexists (Some (SMEEmit _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
    tstep_s. eexists (Some (SMEReturn _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i => ??; simplify_eq/=.
    tstep_i. eexists (ValNum <$> vs), h. split!.
    { apply: satisfiable_mono; [by apply (heap_bij_inv_init bs)|]. iIntros "[$ [Hi Hs]]".
      iSplitL.
      - iSplitL "Hi"; by iApply big_sepM_subseteq.
      - iSplitL; [|iAccu]. rewrite big_sepL2_fmap_l big_sepL2_fmap_r. iApply big_sepL2_intro; [done|].
        iIntros "!>" (?????). by simplify_eq/=. }
    apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. case_match => *; simplify_eq.
    + tstep_s.  eexists (Some _). split; [done|]. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    destruct κ as [e|]; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i => ? vs *. tstep_both => *.
    apply steps_impl_step_end => ???. inv_all @m_step => ?; simplify_eq.
    + destruct e as [? [? vs' |]]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=. tend.
      split!.
      tstep_both. apply steps_impl_step_end => ???. inv_all @m_step.
      tstep_s. eexists (None). apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=. tend.
      iSatStart.
      iIntros!. iDestruct (big_sepL2_ValNum_inv_r with "[$]") as %?. subst.
      iSatStop.
      split!; [done|].
      tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEEmit _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEReturn _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i => ? <-.
      tstep_i. eexists [ValNum _]. split!.
      { iSatMono. iIntros!. iFrame. iSplitR; [by iPureIntro|]. instantiate (1:=True%I). done. }
      apply: Hloop; [done|]. split!.
    + destruct e as [? []]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=.
      tstep_s. eexists None. apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=.
      iSatStart. iIntros!.
      iDestruct (big_sepL2_cons_inv_r with "[$]") as ([]??) "[??]"; subst => //=; iDestruct!.
      iSatStop.
      tend. split!.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEEmit _)). split!.
      apply: steps_spec_step_end; [econs|]=> /=? ->.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step.
Qed.

(** ** [rec_heap_bij] is adequate wrt. contextual refinement *)
(** Follows from the lemmas above. *)
Lemma rec_heap_bij_trefines_implies_ctx_refines fnsi fnss :
  dom fnsi = dom fnss →
  fd_static_vars <$> fnsi = fd_static_vars <$> fnss →
  trefines (rec_mod fnsi) (rec_heap_bij (fds_init_heap (fd_static_vars <$> fnss)) (rec_mod fnss)) →
  rec_ctx_refines fnsi fnss.
Proof.
  move => Hdom Hs Href C HC. rewrite /rec_syn_link map_difference_union_r (map_difference_union_r fnss).
  etrans. 2: {
    by apply (rec_heap_bij_rec_closed (fds_init_heap (fd_static_vars <$> fnss ∪ C ∖ fnss))). }
  rewrite !map_fmap_union Hs. rewrite {1}(map_difference_eq_dom_L C fnsi fnss) //.
  apply seq_map_mod_trefines. { apply _. } { apply _. }
  etrans. { apply rec_syn_link_refines_link. apply map_disjoint_difference_r'. }
  etrans. { eapply rec_link_trefines. 1,2: apply _. 1: done. 1: apply rec_heap_bij_refl. }
  etrans. { apply rec_heap_bij_combine. 1,2: apply _. 2: done.
            apply fds_init_heap_disj. apply map_disjoint_fmap.
            rewrite (map_difference_eq_dom_L C fnsi fnss) //. apply map_disjoint_difference_r'. }
  rewrite fds_init_heap_union. 2: { apply map_disjoint_fmap. apply map_disjoint_difference_r'. }
  rewrite {1}(map_difference_eq_dom_L C fnsi fnss) //.
  apply rec_heap_bij_trefines. 1: apply _.
  etrans. 2: { apply rec_link_refines_syn_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  erewrite map_difference_eq_dom_L => //.
  apply _.
Qed.

(** * Exercising [rec_heap_bij] *)
Module rec_heap_bij_example.

Local Open Scope Z_scope.

Definition bij_alloc : fndef := {|
  fd_args := [];
  fd_vars := [("tmp", 1)];
  fd_static_vars := [];
  fd_body := (LetE "_" (Store (Var "tmp") (Val 1))
             (LetE "_" (Call (Val (ValFn "ext")) [])
             (Load (Var "tmp"))));
  fd_static := I;
|}.

Definition bij_alloc_opt : fndef := {|
  fd_args := [];
  fd_vars := [];
  fd_static_vars := [];
  fd_body := (LetE "_" (Call (Val (ValFn "ext")) [])
             (Val 1));
  fd_static := I;
|}.

Lemma bij_alloc_opt_refines :
  trefines (rec_mod (<["f" := bij_alloc_opt]> ∅))
           (rec_heap_bij ∅ (rec_mod (<["f" := bij_alloc]> ∅))).
Proof.
  apply: (rec_heap_bij_proof True). { compute_done. }
  { move => ??. setoid_rewrite lookup_insert_Some. setoid_rewrite lookup_empty. naive_solver. }
  { iIntros!. by iFrame. }
  move => n K1 K2 f fn1 fn2 vs1 vs2 h1 h2 r rf Hf1 ???? Hcall Hret.
  move: Hf1. rewrite !lookup_insert_Some => ?; destruct!; simplify_map_eq/=.
  destruct vs1, vs2 => //.
  tstep_s. split!; [apply (heap_fresh_is_fresh ∅)|]. move => _.
  tstep_i => ??[??]. simplify_eq. split!.
  tstep_s => ???. simplify_eq.
  tstep_s.
  apply: Hcall; [done|econs|econs|..].
  { iSatMonoBupd. iIntros!. iFrame.
    iMod (heap_bij_inv_alloc_s with "[$]") as "[? ?]"; [apply (heap_fresh_is_fresh ∅)|].
    iMod (heap_bij_inv_update_s with "[$] [$]") as "[$ ?]". iModIntro. iAccu. }
  iSatClear.
  move => v1'' v2'' h1'' h2'' rf'' ? /=.
  iSatStart. iIntros!.
  iDestruct (heap_bij_inv_lookup_s (heap_fresh ∅ h2) with "[$] [$]") as %Hl.
  iSatStop.
  tstep_i. tstep_i. split!.
  tstep_s.
  tstep_s => ???. simplify_eq. rewrite Hl h_block_lookup /=. simplify_map_eq.
  rewrite fmap_Some => -[?[??]]. simplify_eq.
  tstep_s => ?[? [? ?]]. simplify_eq.
  apply Hret; [done|].
  iSatMonoBupd.
  iMod (heap_bij_inv_free_s (heap_fresh ∅ h2) with "[$] [$]") as "$"; [done|].
  iModIntro. by iFrame.
Qed.


Lemma bij_alloc_ctx_refines :
  rec_ctx_refines (<["f" := bij_alloc_opt]> ∅) (<["f" := bij_alloc]> ∅).
Proof.
  apply: rec_heap_bij_trefines_implies_ctx_refines; [compute_done..|].
  have -> : (fds_init_heap (fd_static_vars <$> <["f":=bij_alloc]> ∅)) = ∅ by compute_done.
  apply bij_alloc_opt_refines.
Qed.
End rec_heap_bij_example.
