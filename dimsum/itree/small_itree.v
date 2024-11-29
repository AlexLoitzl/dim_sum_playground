From Paco Require Import paco.
From ITree.Eq Require Import Paco2.
From dimsum.core.itree Require Export upstream events.
From stdpp Require Import prelude.
From dimsum.core Require Import base universes.

Module SmallITree.
Local Set Implicit Arguments.
Local Set Contextual Implicit.
Local Set Primitive Projections.

Section itree.

  Context {E : Type -> Type} {R : TypeState} `{!ShrinkEvents E}.

  (** The type [itree] is defined as the final coalgebra ("greatest
      fixed point") of the functor [itreeF]. *)
  Variant itreeF (itree : TypeState) :=
  | RetF (r : R)
  | TauF (t : itree)
  | VisF {X : TypeBelowState} (e : small_events E X) (k : X -> itree)
  .

  CoInductive itree : TypeState := go
  { _observe : itreeF itree }.

End itree.

Arguments itreeF _ _ {_} _.
Arguments itree _ _ {_}.


Definition from_itree {E : Type -> Type} {R : Type} `{!ShrinkEvents E}
  : ITreeDefinition.itree E R -> itree E R :=
  cofix _from_itree (u : ITreeDefinition.itree E R) : itree E R :=
    match observe u with
    | ITreeDefinition.RetF r => go (RetF r)
    | ITreeDefinition.TauF t => go (TauF (_from_itree t))
    | ITreeDefinition.VisF e h => go (VisF (small_events_to_event _ e)
                                        (fun x => _from_itree (h (small_events_to_back _ e x))))
    end.

Definition to_itree {E : Type -> Type} {R : TypeState} `{!ShrinkEvents E}
  : itree E R → ITreeDefinition.itree E R :=
  cofix _to_itree (u : itree E R) : ITreeDefinition.itree E R :=
    match _observe u with
    | RetF r => (Ret r)
    | TauF t => (Tau (_to_itree t))
    | VisF e h => (Vis (small_events_from_event _ e) (fun x => _to_itree (h x)))
    end.

Section from_itree.
  Local Notation from_itree_ i :=
    match observe i with
    | ITreeDefinition.RetF r => go (RetF r)
    | ITreeDefinition.TauF t => go (TauF (from_itree t))
    | ITreeDefinition.VisF e h => go (VisF (small_events_to_event _ e)
                                        (fun x => from_itree (h (small_events_to_back _ e x))))
    end.

  Lemma unfold_from_itree_ {E R} (t : ITreeDefinition.itree E R) `{!ShrinkEvents E}
    : eq (_observe (from_itree t)) (_observe (from_itree_ t)).
  Proof. constructor; reflexivity. Qed.
End from_itree.

Section to_itree.
  Local Notation to_itree_ i :=
    match _observe i with
    | RetF r => (Ret r)
    | TauF t => (Tau (to_itree t))
    | VisF e h => (Vis (small_events_from_event _ e) (fun x => to_itree (h x)))
    end.

  Lemma unfold_to_itree_ {E R} `{!ShrinkEvents E} (t : itree E R)
    : observing eq (to_itree t) (to_itree_ t).
  Proof. constructor; reflexivity. Qed.
End to_itree.
Global Opaque to_itree.

Lemma from_to_itree E R `{!ShrinkEvents E} (i : ITreeDefinition.itree E R) :
  to_itree (from_itree i) ≅ i.
Proof.
  revert i. ginit. pcofix IH => i.
  rewrite ->unfold_to_itree_, unfold_from_itree_.
  rewrite ->(itree_eta i).
  destruct (observe i); simpl.
  - gstep. by constructor.
  - gstep. constructor. eauto with paco.
  - gstep. rewrite -(small_events_eq (λ T e k, Vis e k) _ k). constructor => ? /=. eauto with paco.
Qed.

Global Instance SmallITree_equiv {E R} `{!ShrinkEvents E} : Equiv (itree E R) :=
  λ t1 t2, SmallITree.to_itree t1 ≅ SmallITree.to_itree t2.

Lemma equiv_from_itree E R `{!ShrinkEvents E} (x y : ITreeDefinition.itree E R) :
  from_itree x ≡ from_itree y ↔ x ≅ y.
Proof.
  unfold equiv, SmallITree_equiv. by rewrite !from_to_itree.
Qed.

Lemma eqit_to_itree E R `{!ShrinkEvents E} (x y : itree E R) :
  to_itree x ≅ to_itree y ↔ x ≡ y.
Proof. done. Qed.

Global Instance SmallITree_equiv_proper E R `{!ShrinkEvents E} :
  Proper ((eq_itree eq) ==> (≡)) (@SmallITree.from_itree E R _).
Proof. intros ?? Heq. by apply equiv_from_itree. Qed.

Global Instance SmallITree_to_itree_proper E R `{!ShrinkEvents E} :
  Proper ((≡) ==> (eq_itree eq)) (@SmallITree.to_itree E R _).
Proof. intros ?? Heq. by apply eqit_to_itree. Qed.

Global Instance SmallITree_equiv_rewrite {E R} `{!ShrinkEvents E} : RewriteRelation (≡@{itree E R}) := { }.

Global Instance SmallITree_equiv_equiv {E R} `{!ShrinkEvents E} : Equivalence (≡@{itree E R}).
Proof.
  unfold equiv, SmallITree_equiv.
  constructor.
  - intros ?. done.
  - intros ??. done.
  - intros ??? ->. done.
Qed.

Global Instance SmallITree_supseteq {E R} `{!ShrinkEvents E} : SqSupsetEq (itree E R) :=
  λ t1 t2, SmallITree.to_itree t1 ≳ SmallITree.to_itree t2.

Lemma supseteq_from_itree E R `{!ShrinkEvents E} (x y : ITreeDefinition.itree E R) :
  from_itree x ⊒ from_itree y ↔ x ≳ y.
Proof.
  unfold sqsupseteq, SmallITree_supseteq. by rewrite !from_to_itree.
Qed.

Lemma euttge_to_itree E R `{!ShrinkEvents E} (x y : itree E R) :
  to_itree x ≳ to_itree y ↔ x ⊒ y.
Proof. done. Qed.

Global Instance SmallITree_supseteq_proper_equiv E R `{!ShrinkEvents E} :
  Proper ((≡) ==> (≡) ==> iff) (⊒@{SmallITree.itree E R}).
Proof.
  unfold equiv, SmallITree_equiv, sqsupseteq, SmallITree_supseteq.
  intros ?? Heq1 ?? Heq2. by rewrite Heq1 Heq2.
Qed.
Global Instance SmallITree_supseteq_proper E R `{!ShrinkEvents E} :
  Proper ((euttge eq) ==> (⊒)) (@SmallITree.from_itree E R _).
Proof. intros ?? Heq. by apply supseteq_from_itree. Qed.
Global Instance SmallITree_supseteq_proper_flip E R `{!ShrinkEvents E} :
  Proper (flip (euttge eq) ==> flip (⊒)) (@SmallITree.from_itree E R _).
Proof. intros ?? Heq. by apply supseteq_from_itree. Qed.

Global Instance SmallITree_supseteq_preorder {E R} `{!ShrinkEvents E} : PreOrder (⊒@{itree E R}).
Proof.
  unfold sqsupseteq, SmallITree_supseteq.
  constructor.
  - intros ?. done.
  - intros ??? ->. done.
Qed.
End SmallITree.

Notation "↓ᵢ" := SmallITree.from_itree : stdpp_scope.
Notation "↑ᵢ" := SmallITree.to_itree : stdpp_scope.

(* Should be able to solve ShrinkEvents *)
Check ∀ t : itree (stateE nat +' choiceE +' visibleE nat) unit, SmallITree.from_itree t = SmallITree.from_itree t.
(* Should not be able to solve ShrinkEvents *)
Check ∀ t : itree (choiceE +' visibleE (itree choiceE nat)) unit, SmallITree.from_itree t = SmallITree.from_itree t.
