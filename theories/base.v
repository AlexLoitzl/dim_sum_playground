From Coq Require Export ssreflect.
Require Export stdpp.prelude.
Require Export stdpp.gmap.
Require Export stdpp.strings.

Global Unset Program Cases.

Definition LEM (P : Prop) := P ∨ ¬ P.

Lemma snoc_inv {A} (l : list A):
  l = [] ∨ ∃ x l', l = l' ++ [x].
Proof.
  destruct l as [|x l']. by left. right.
  elim: l' x => //. move => x. by eexists _, [].
  move => x ? IH x'. move: (IH x) => [x'' [l'' ->]].
  eexists x'', _. by apply: app_comm_cons.
Qed.

Record wrap A := Wrap { a : A }.

Ltac specialize_hyps :=
  repeat match goal with
  | H : ∀ x, @?P x → ?G |- _ =>
      let i := open_constr:(_) in
      let H' := fresh in
      assert (P i) as H' by done;
      assert_succeeds (clear; assert (∀ x, P x → x = i) by naive_solver);
      specialize (H i H');
      clear H'
         end.

Ltac destruct_hyps :=
  simplify_eq/=;
  repeat (
      lazymatch goal with
      | H : (_ * _) |- _ => destruct H as [??]
      | H : unit |- _ => destruct H
      | H : ∃ x, _ |- _ => destruct H as [??]
      | H : _ ∧ _ |- _ => destruct H as [??]
      end; simplify_eq/=
    ).

Tactic Notation "econs" := econstructor.
Tactic Notation "econs" integer(n) := econstructor n.

Tactic Notation "destruct_prod" "?" ident(H) :=
  repeat match type of H with
         | context [ match ?x with | (y, z) => _ end] =>
             let y := fresh y in
             let z := fresh z in
             destruct x as [y z]
         end.
Tactic Notation "destruct_prod" "!" ident(H) := progress (destruct_prod? H).
Tactic Notation "destruct_prod" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_prod? H) end.
Tactic Notation "destruct_prod" "!" :=
  progress destruct_prod?.
Tactic Notation "destruct_exist" "?" ident(H) :=
  repeat match type of H with
         | ∃ x, _ => let x := fresh x in destruct H as [x H]
         end.
Tactic Notation "destruct_exist" "!" ident(H) := progress (destruct_exist? H).
Tactic Notation "destruct_exist" "?" :=
  repeat match goal with H : _ |- _ => progress (destruct_exist? H) end.
Tactic Notation "destruct_exist" "!" :=
  progress destruct_exist?.
Tactic Notation "destruct_all" "?" :=
  repeat first [
      destruct_prod!
      | destruct_and!
      | destruct_or!
      | destruct_exist!
      ].
Tactic Notation "destruct_all" "!" :=
  progress destruct_all?.

Section theorems.
Context `{FinMap K M}.
Lemma map_disjoint_difference_l' {A} (m1 m2 : M A) : m2 ∖ m1 ##ₘ m1.
Proof.
  intros i.
  unfold difference, map_difference; rewrite lookup_difference_with.
  by destruct (m1 !! i), (m2 !! i).
Qed.
Lemma map_disjoint_difference_r' {A} (m1 m2 : M A) : m1 ##ₘ m2 ∖ m1.
Proof. intros. symmetry. by apply map_disjoint_difference_l'. Qed.

Lemma map_difference_union_r {A} (m1 m2 : M A) :
  m1 ∪ m2 = m1 ∪ (m2 ∖ m1).
Proof.
  apply map_eq. intros i.
  apply option_eq. intros v.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite !lookup_union_Some_raw (lookup_merge _).
  destruct (m1 !! i) as [x'|], (m2 !! i) => /=; intuition congruence.
Qed.
End theorems.

Section dom.
Context `{FinMapDom K M D}.
Lemma map_difference_eq_dom {A} (m m1 m2 : M A) :
  dom D m1 ≡ dom D m2 →
  m ∖ m1 = m ∖ m2.
Proof.
  move => Hdom.
  apply map_eq. intros i. move: (Hdom i). rewrite !elem_of_dom -!not_eq_None_Some => ?.
  apply option_eq. intros v.
  unfold difference, map_difference, difference_with, map_difference_with.
  rewrite !(lookup_merge _).
  destruct (m !! i), (m1 !! i) as [x'|] eqn: Heq1, (m2 !! i) eqn: Heq2 => /=; try intuition congruence.
Qed.
Lemma map_difference_eq_dom_L {A} (m m1 m2 : M A) `{!LeibnizEquiv D}:
  dom D m1 = dom D m2 →
  m ∖ m1 = m ∖ m2.
Proof. unfold_leibniz. apply: map_difference_eq_dom. Qed.
End dom.

Section semi_set.
  Context `{SemiSet A C}.
  Implicit Types x y : A.
  Implicit Types X Y : C.
  Implicit Types Xs Ys : list C.
Lemma elem_of_subseteq_1 X Y x: X ⊆ Y → x ∈ X → x ∈ Y.
Proof. set_solver. Qed.
End semi_set.

Section theorems.
Context `{FinMap K M}.

Lemma lookup_union_None_1 {A} (m1 m2 : M A) i :
  (m1 ∪ m2) !! i = None → m1 !! i = None ∧ m2 !! i = None.
Proof. apply lookup_union_None. Qed.
Lemma lookup_union_None_2 {A} (m1 m2 : M A) i :
  m1 !! i = None → m2 !! i = None → (m1 ∪ m2) !! i = None.
Proof. move => ??. by apply lookup_union_None. Qed.
End theorems.

Lemma omap_app {A B} l1 l2 (f : A → option B) :
  omap f (l1 ++ l2) = omap f l1 ++ omap f l2.
Proof. elim: l1 => //; csimpl => ?? ->. by case_match. Qed.

Lemma omap_option_list {A B} (f : A → option B) o :
  omap f (option_list o) = option_list (o ≫= f).
Proof. by destruct o. Qed.

Ltac invert_all_tac f :=
  let do_invert H := inversion H; clear H in
  repeat lazymatch goal with
         | H : f |- _ => do_invert H
         | H : f _ |- _ => do_invert H
         | H : f _ _|- _ => do_invert H
         | H : f _ _ _|- _ => do_invert H
         | H : f _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _|- _ => do_invert H
         | H : f _ _ _ _ _ _ _ _ _|- _ => do_invert H
         end.

Tactic Notation "invert_all" constr(f) := invert_all_tac f; simplify_eq/=; specialize_hyps.
Tactic Notation "invert_all'" constr(f) := invert_all_tac f.
