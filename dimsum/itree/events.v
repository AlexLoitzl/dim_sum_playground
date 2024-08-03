From dimsum.core.itree Require Export upstream.
From stdpp Require Import prelude.
From dimsum.core Require Import universes.
Import ITreeStdppNotations.

(** * state events *)
Inductive stateE (S : Type) : Type → Type :=
| EGetState : stateE S S
| ESetState (x : S) : stateE S unit
| EYield : stateE S unit.
Arguments EGetState {_}.
Arguments ESetState {_} _.
Arguments EYield {_}.

Definition get_state {E S} `{!stateE S -< E} : itree E S :=
  (trigger EGetState)%itree.
Definition set_state {E S} `{!stateE S -< E} (s : S) : itree E unit :=
  (trigger (ESetState s))%itree.
Definition yield {E S} `{!stateE S -< E} : itree E unit :=
  (trigger EYield)%itree.

Global Instance ITreeToTranslate_get_state E1 E2 S
  {HE1 : stateE S -< E1} (Hin : E1 -< E2) {HE2 : stateE S -< E2} :
  TCEq (HE2 S) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) S) →
  ITreeToTranslate (get_state) Hin (get_state).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Instance ITreeToTranslate_set_state E1 E2 S x
  {HE1 : stateE S -< E1} (Hin : E1 -< E2) {HE2 : stateE S -< E2} :
  TCEq (HE2 unit) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) unit) →
  ITreeToTranslate (set_state x) Hin (set_state x).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Instance ITreeToTranslate_yield E1 E2 S
  {HE1 : stateE S -< E1} (Hin : E1 -< E2) {HE2 : stateE S -< E2} :
  (TCEq (HE2 unit) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) unit)) →
  ITreeToTranslate yield Hin yield.
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Typeclasses Opaque get_state set_state yield.

(** * choice events *)
Inductive choiceE : Type → Type :=
| EDemonic (X : TypeBelowState) : choiceE X
| EAngelic (X : TypeBelowState) : choiceE X.

Definition angelic {E} `{!choiceE -< E} (R : TypeBelowState) : itree E R :=
  (trigger (EAngelic R))%itree.
Definition demonic {E} `{!choiceE -< E} (R : TypeBelowState) : itree E R :=
  (trigger (EDemonic R))%itree.

Definition assume {E} `{!choiceE -< E} (P : Prop) : itree E unit :=
  (angelic P;; Ret tt)%itree.
Definition assert {E} `{!choiceE -< E} (P : Prop) : itree E unit :=
  (demonic P;; Ret tt)%itree.

Definition UB {E R} `{!choiceE -< E} : itree E R :=
  (x ← angelic void; match x : void with end)%itree.
Definition NB {E R} `{!choiceE -< E} : itree E R :=
  (x ← demonic void; match x : void with end)%itree.

Definition assume_option {E R} `{!choiceE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => UB end)%itree.
Definition assert_option {E R} `{!choiceE -< E} (o : option R) : itree E R :=
  (match o with | Some x => Ret x | None => NB end)%itree.

Notation "x ?" := (assume_option x) (at level 10, format "x ?") : itree_scope.
Notation "x !" := (assert_option x) (at level 10, format "x !") : itree_scope.

(* This corresponds to the choice operator offered by traditional
operational semantics. It corresponds to angelic choice, if [∀ x1 x2, P
x1 → P x2 → x1 = x2]. *)
Definition demonic_non_empty {E} {R : TypeBelowState} `{!choiceE -< E} (P : R → Prop) : itree E R :=
  (assume (∃ x, P x);; x ← demonic _; assert (P x);; Ret x)%itree.


Global Instance ITreeToTranslate_angelic E1 E2 (T : TypeBelowState)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T) →
  ITreeToTranslate (angelic T) Hin (angelic T).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Instance ITreeToTranslate_demonic E1 E2 (T : TypeBelowState)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T) →
  ITreeToTranslate (demonic T) Hin (demonic T).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Instance ITreeToTranslate_assume E1 E2 (P : Prop)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 P) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) P) →
  ITreeToTranslate (assume P) Hin (assume P).
Proof. intros Heq. unfold assume. apply _. Qed.

Global Instance ITreeToTranslate_assert E1 E2 (P : Prop)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 P) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) P) →
  ITreeToTranslate (assert P) Hin (assert P).
Proof. intros Heq. unfold assert. apply _. Qed.

Global Instance ITreeToTranslate_UB E1 E2 R
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 void) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) void) →
  ITreeToTranslate (R:=R) UB Hin UB.
Proof. intros Heq. unfold UB. apply ITreeToTranslate_bind; [apply _|done]. Qed.

Global Instance ITreeToTranslate_NB E1 E2 R
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 void) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) void) →
  ITreeToTranslate (R:=R) NB Hin NB.
Proof. intros Heq. unfold NB. apply ITreeToTranslate_bind; [apply _|done]. Qed.

Global Instance ITreeToTranslate_assume_option E1 E2 R (o : option R)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 void) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) void) →
  ITreeToTranslate (assume_option o) Hin (assume_option o).
Proof. intros ?. destruct o; simpl; apply _. Qed.

Global Instance ITreeToTranslate_assert_option E1 E2 R (o : option R)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  TCEq (HE2 void) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) void) →
  ITreeToTranslate (assert_option o) Hin (assert_option o).
Proof. intros ?. destruct o; simpl; apply _. Qed.

Global Instance ITreeToTranslate_demonic_non_empty E1 E2 R (P : R → _)
  {HE1 : choiceE -< E1} (Hin : E1 -< E2) {HE2 : choiceE -< E2} :
  (∀ T, TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T)) →
  ITreeToTranslate (demonic_non_empty P) Hin (demonic_non_empty P).
Proof. intros ?. apply _. Qed.

Global Typeclasses Opaque angelic demonic assume assert UB NB assume_option assert_option demonic_non_empty.

(** * big choice events *)
Inductive choiceE_big : Type → Type :=
| EDemonic_big (X : TypeOrdinal) : choiceE_big X
| EAngelic_big (X : TypeOrdinal) : choiceE_big X.

Definition angelic_big {E} `{!choiceE_big -< E} (R : TypeOrdinal) : itree E R :=
  (trigger (EAngelic_big R))%itree.
Definition demonic_big {E} `{!choiceE_big -< E} (R : TypeOrdinal) : itree E R :=
  (trigger (EDemonic_big R))%itree.

Global Instance ITreeToTranslate_angelic_big E1 E2 (T : TypeOrdinal)
  {HE1 : choiceE_big -< E1} (Hin : E1 -< E2) {HE2 : choiceE_big -< E2} :
  TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T) →
  ITreeToTranslate (angelic_big T) Hin (angelic_big T).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Instance ITreeToTranslate_demonic_big E1 E2 (T : TypeOrdinal)
  {HE1 : choiceE_big -< E1} (Hin : E1 -< E2) {HE2 : choiceE_big -< E2} :
  TCEq (HE2 T) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) T) →
  ITreeToTranslate (demonic_big T) Hin (demonic_big T).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

(** * visible events *)
Inductive visibleE (EV : Type) : Type → Type :=
| EVisible (e : EV) : visibleE EV unit.
Arguments EVisible {_} _.

Definition visible {E EV} `{!visibleE EV  -< E} (e : EV) : itree E unit :=
  (trigger (EVisible e))%itree.

Global Instance ITreeToTranslate_visible EV E1 E2 e
  {HE1 : visibleE EV -< E1} (Hin : E1 -< E2) {HE2 : visibleE EV -< E2} :
  TCEq (HE2 unit) (cat (@resum _ _ _ _ HE1) (@resum _ _ _ _ Hin) unit) →
  ITreeToTranslate (visible e) Hin (visible e).
Proof. intros Heq%TCEq_eq. apply ITreeToTranslate_trigger. by rewrite Heq. Qed.

Global Typeclasses Opaque visible.

(** * [moduleE] *)
Notation moduleE EV S := (choiceE +' visibleE EV +' stateE S).
Notation moduleE_big EV S := (choiceE_big +' moduleE EV S).

Section moduleE_eq_itree_inv.

  Context {EV S R : Type}.

  Notation moduleE_eq_itree_ t1_ t2_ :=
    match observe t1_, observe t2_ with
    | RetF r1, RetF r2 => r1 = r2
    | TauF t1, TauF t2 => t1 ≅ t2
    | VisF e1 t1, VisF e2 t2 =>
        match e1, e2 with
        | inl1 e1, inl1 e2 =>
            match e1 in choiceE X return (X → itree _ _) → _ with
            | EDemonic X1 => λ t1,
                  match e2 in choiceE X return (X → itree _ _) → _ with
                  | EDemonic X2 => λ t2,
                        ∃ p : @eq Type X1 X2, pweqeq (eq_itree eq) p t1 t2
                  | _ => λ _, False
                  end t2
            | EAngelic X1 => λ t1,
                  match e2 in choiceE X return (X → itree _ _) → _ with
                  | EAngelic X2 => λ t2,
                        ∃ p : @eq Type X1 X2, pweqeq (eq_itree eq) p t1 t2
                  | _ => λ _, False
                  end t2
            end t1
        | inr1 (inl1 e1), inr1 (inl1 e2) =>
            match e1 in visibleE _ X return (X → itree _ _) → _ with
            | EVisible e1 => λ t1,
                  match e2 in visibleE _ X return (X → itree _ _) → _ with
                  | EVisible e2 => λ t2,
                        e1 = e2 ∧ t1 () ≅ t2 ()
                  end t2
            end t1
        | inr1 (inr1 e1), inr1 (inr1 e2) =>
            match e1 in stateE _ X return (X → itree _ _) → _ with
            | EGetState => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | EGetState => λ t2,
                        ∀ s, t1 s ≅ t2 s
                  | _ => λ _, False
                  end t2
            | ESetState s1 => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | ESetState s2 => λ t2,
                        s1 = s2 ∧ t1 () ≅ t2 ()
                  | _ => λ _, False
                  end t2
            | EYield => λ t1,
                  match e2 in stateE _ X return (X → itree _ _) → _ with
                  | EYield => λ t2,
                        t1 () ≅ t2 ()
                  | _ => λ _, False
                  end t2
            end t1
        | _, _ => False
        end
    | _, _ => False
    end.

  Lemma moduleE_eq_itree_inv (t1 t2 : itree (moduleE EV S) R) :
    t1 ≅ t2 -> moduleE_eq_itree_ t1 t2.
  Proof using Type*.
    intros Heq%eqit_inv. unfold observe.
    destruct (_observe t1), (_observe t2); try done.
    destruct Heq as [? [Heq1 Heq2]]. simplify_eq/=.
    repeat case_match; simplify_eq/=.
    - exists eq_refl. done.
    - exists eq_refl. done.
    - naive_solver.
    - naive_solver.
    - naive_solver.
    - naive_solver.
  Qed.

End moduleE_eq_itree_inv.
(* This contraint is required, but not sure why and where
moduleE_eq_itree_inv.u0 comes from. *)
Constraint universes.BelowState < moduleE_eq_itree_inv.u0.

(** * Shrinking of events *)
Class ShrinkEvents (E : Type → Type) := MkShrinkEvents {
  small_events : TypeBelowState → TypeState;
  small_events_to_type T : E T → TypeBelowState;
  small_events_to_event T : ∀ (e : E T), small_events (small_events_to_type T e);
  small_events_to_back T : ∀ (e : E T), small_events_to_type T e → T;
  small_events_from_event T : small_events T → E T;
  small_events_eq {X Y Z} (f : ∀ (T : Type), E T → (T → Y) → Z) e (k : X → Y):
    f (small_events_to_type X e) (small_events_from_event (small_events_to_type X e) (small_events_to_event X e))
      (λ x, k (small_events_to_back X e x)) = f X e k;
}.
Arguments small_events _ {_}.

Inductive stateE_shrink (S : TypeBelowState) : TypeBelowState → TypeState :=
| EGetState_shrink : stateE_shrink S S
| ESetState_shrink (x : S) : stateE_shrink S unit
| EYield_shrink : stateE_shrink S unit.

Global Instance shrink_stateE (S : TypeBelowState) : ShrinkEvents (stateE S).
Proof.
  unshelve eapply (MkShrinkEvents _ (stateE_shrink S)).
  - intros ? e. destruct e. exact S. exact unit. exact unit.
  - intros ? e. destruct e. apply EGetState_shrink. apply (ESetState_shrink _ x).
    apply EYield_shrink.
  - intros ? e. destruct e. all: exact (λ x, x).
  - intros ? e. destruct e. apply EGetState. apply (ESetState x).
    apply EYield.
  - intros X Y Z f e k; simpl. by destruct e.
Qed.

Inductive choiceE_shrink : TypeBelowState → TypeState :=
| EDemonic_shrink (X : TypeBelowState) : choiceE_shrink X
| EAngelic_shrink (X : TypeBelowState) : choiceE_shrink X.

Global Instance shrink_choiceE : ShrinkEvents choiceE.
Proof.
  unshelve eapply (MkShrinkEvents _ choiceE_shrink).
  - intros ? e. destruct e as [X|X]; exact X.
  - intros ? e. destruct e. exact (EDemonic_shrink _). exact (EAngelic_shrink _).
  - intros ? e. destruct e; exact (λ x, x).
  - intros ? e. destruct e. exact (EDemonic _). exact (EAngelic _).
  - intros X Y Z f e k; simpl. by destruct e.
Qed.

Inductive visibleE_shrink (EV : TypeState) : TypeBelowState → TypeState :=
| EVisible_shrink (e : EV) : visibleE_shrink EV unit.

Global Instance shrink_visibleE (EV : TypeState) : ShrinkEvents (visibleE EV).
Proof.
  unshelve eapply (MkShrinkEvents _ (visibleE_shrink EV)).
  - intros ? e. destruct e. exact unit.
  - intros ? e. destruct e. by constructor.
  - intros ? e. destruct e. exact (λ x, x).
  - intros ? e. destruct e. by constructor.
  - intros X Y Z f e k; simpl. by destruct e.
Qed.

Variant sum1_shrink (E1 E2 : TypeBelowState -> TypeState) (X : TypeBelowState) : TypeState :=
| inl1_shrink (_ : E1 X)
| inr1_shrink (_ : E2 X).
Arguments inr1_shrink {E1 E2} [X].
Arguments inl1_shrink {E1 E2} [X].

Global Instance shrink_sumE E1 E2 `{!ShrinkEvents E1} `{!ShrinkEvents E2} : ShrinkEvents (E1 +' E2).
Proof.
  unshelve eapply (MkShrinkEvents _ (sum1_shrink (small_events E1) (small_events E2))).
  - intros ? e. destruct e as [e|e]; apply (small_events_to_type _ e).
  - intros ? e. destruct e as [e|e].
    + apply inl1_shrink. apply small_events_to_event.
    + apply inr1_shrink. apply small_events_to_event.
  - intros ? e. destruct e as [e|e]; apply small_events_to_back.
  - intros ? e. destruct e as [e|e].
    + apply inl1. apply (small_events_from_event _ e).
    + apply inr1. apply (small_events_from_event _ e).
  - intros ??? f e ?; simpl. destruct e as [e|e].
    + apply (small_events_eq (λ T e k, f T (inl1 e) k)).
    + apply (small_events_eq (λ T e k, f T (inr1 e) k)).
Qed.


(** * tests *)
Definition step : itree (moduleE nat nat) unit :=
  (demonic nat;;
   n ← angelic nat;
   set_state n;;
   n ← get_state;
   yield;;
   '(m, _) ← angelic (nat * nat);
   Some 10?;;
   (None : option nat)!;;
   x ← Some 10?;
   y ← (None : option nat)!;
   UB (R:=void);;
   NB (R:=void);;
   visible x;;
   ret ())%itree.
