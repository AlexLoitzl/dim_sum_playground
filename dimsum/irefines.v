From dimsum.core Require Import module trefines.
From dimsum.core.itree Require Import upstream events.
Import ITreeStdppNotations.

(* From ITree.Props Require Import Finite.  *)
(*
Inductive all_finite {E} {A: Type} : itree E A -> Type :=
 | all_finiteRet: forall a t,
    observe t = RetF a ->
   all_finite t
 | all_finiteTau: forall t u,
   observe t = TauF u ->
   all_finite u ->
   all_finite t
 | all_finiteVis: forall {X : TypeState} (e: E X) t k,
   observe t = VisF e k ->
   (forall x, all_finite (k x)) ->
   all_finite t
.

Fixpoint itree_to_state {E} (t : itree E void) (HP: all_finite t) : TypeState :=
  match HP with
  | all_finiteRet x _ _ => match x with end
  | all_finiteTau _ u _ F => itree_to_state u F
  | @all_finiteVis _ _ X e _ k _ F => () + { x : X & itree_to_state (k x) (F x) }
  end.
(* TODO: combine this with a function from states to itrees? *)
(* TODO: define itree_to_state as a coinductive type? Is there a way to express this?
E.g. something like the following? *)
Section itree_state.
  Context {E : Type -> Type}.
  Variant itree_stateF (t : itree E void) (itree_state : itree E void → TypeState) : TypeState :=
  | RetState (r : void) (_ : observe t = RetF r)
  | TauState (_ : ∃ t', observe t = TauF t')
      (c : itree_state (match observe t with | TauF t' => t' | _ => ITree.spin end))
  | VisState (_ : ∃ X (e : E X) k, observe t = VisF e k)
      (* TODO *)
      (c : itree_state (match observe t with | TauF t' => t' | _ => ITree.spin end)).

  CoInductive itree_state (t : itree E void) : TypeState := go
  { _observe : itree_stateF t itree_state }.

**)


(** * [irefines] *)
Inductive ihas_trace {EV S} : itree (moduleE_big EV S) void → S → trace EV → (itree (moduleE_big EV S) void → S → Prop) → Prop :=
| ITraceTau t t' σ κs Pσ:
  t ≅ Tau t' →
  ihas_trace t' σ κs Pσ →
  ihas_trace t σ κs Pσ
| ITraceAngelicBig T t t' σ κs Pσ:
  t ≅ (Vis (inl1 (EAngelic_big T)) t') →
  (∀ x, ihas_trace (t' x) σ κs Pσ) →
  ihas_trace t σ κs Pσ
| ITraceDemonicBig T t t' σ κs Pσ x:
  t ≅ (Vis (inl1 (EDemonic_big T)) t') →
  ihas_trace (t' x) σ κs Pσ →
  ihas_trace t σ κs Pσ
| ITraceAngelic T t t' σ κs Pσ:
  t ≅ (Vis (inr1 (inl1 (EAngelic T))) t') →
  (∀ x, ihas_trace (t' x) σ κs Pσ) →
  ihas_trace t σ κs Pσ
| ITraceDemonic T t t' σ κs Pσ x:
  t ≅ (Vis (inr1 (inl1 (EDemonic T))) t') →
  ihas_trace (t' x) σ κs Pσ →
  ihas_trace t σ κs Pσ
| ITraceVis e t t' σ κs κs' Pσ:
  t ≅ (Vis (inr1 (inr1 (inl1 (EVisible e)))) t') →
  tcons e κs' ⊆ κs →
  ihas_trace (t' ()) σ κs' Pσ →
  ihas_trace t σ κs Pσ
| ITraceGetState t t' σ κs Pσ:
  t ≅ (Vis (inr1 (inr1 (inr1 EGetState))) t') →
  ihas_trace (t' σ) σ κs Pσ →
  ihas_trace t σ κs Pσ
| ITraceSetState t t' σ σ' κs Pσ:
  t ≅ (Vis (inr1 (inr1 (inr1 (ESetState σ')))) t') →
  ihas_trace (t' ()) σ' κs Pσ →
  ihas_trace t σ κs Pσ
| ITraceAll t T f σ κs Pσ:
    (∀ x, ihas_trace t σ (f x) Pσ) →
    tall T f ⊆ κs →
    ihas_trace t σ κs Pσ
| ITraceEnd t t' σ (Pσ : _ → _ → Prop) κs:
  t ≅ t' →
  Pσ t' σ →
  tnil ⊆ κs →
  ihas_trace t σ κs Pσ
.

(* TODO: Better notation where σ is not in the braces? *)
Notation " t '~{' σ , κs '}~>ᵢ' P " := (ihas_trace t σ κs P) (at level 40).
Notation " t '~{' σ , κs '}~>ᵢ' - " := (ihas_trace t σ κs (λ _ _, True)) (at level 40).

Global Instance ihas_trace_proper {EV S} :
  Proper (eq_itree eq ==> (=) ==> (⊆) ==> (pointwise_relation _ (pointwise_relation S impl)) ==> impl) (@ihas_trace EV S).
Proof.
  move => t1 t2 Heq ?? -> κs1 κs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht t2 κs2 Pσ2 Heq Hκs HP.
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|..]. 1: by etrans; [|done]. naive_solver.
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. econstructor; [by etrans|naive_solver].
  - move => *. apply: ITraceAll; [|by etrans]. naive_solver.
  - move => ????????????? HP. apply: ITraceEnd; [ | by apply: HP | by etrans].
    by etrans.
Qed.

Global Instance ihas_trace_proper_flip {EV S} :
  Proper ((eq_itree eq) ==> (=) ==> (flip (⊆)) ==> (=) ==> flip impl) (@ihas_trace EV S).
Proof. move => ?? Ht ?? -> ?? Hsub ?? -> /=. by rewrite Hsub Ht. Qed.

Lemma ihas_trace_mono {EV S} (t : itree (moduleE_big EV S) void) κs' κs (Pσ2' Pσ2 : _ → _ → Prop)  σ :
  t ~{ σ, κs' }~>ᵢ Pσ2' →
  κs' ⊆ κs →
  (∀ t σ, Pσ2' t σ → Pσ2 t σ) →
  t ~{ σ, κs }~>ᵢ Pσ2.
Proof. move => ???. by apply: ihas_trace_proper. Qed.

Record irefines {EV Si Ss} (ti : itree (moduleE_big EV Si) void) (σi : Si)
  (ts : itree (moduleE_big EV Ss) void) (σs : Ss) : Prop := {
  iref_subset:
    ∀ κs, ti ~{ σi, κs }~>ᵢ - →
          ts ~{ σs, κs }~>ᵢ -
}.

(** * Relating irefines to trefines *)
Definition mod_to_itree {EV} (m : mod_trans EV) : itree (moduleE_big EV (m.(m_state))) void:=
  ITree.forever (
      σ ← get_state;
      Pσ' ← demonic_big _;
      κ ← demonic _;
      assert (m.(m_step) σ κ Pσ');;
      (if κ is Some e then visible e else Ret ());;
      σ' ← angelic_big _;
      assume (Pσ' σ');;
      set_state σ')%itree.

Lemma thas_trace_ihas_trace EV (m : mod_trans EV) σ κs :
  σ ~{m, κs}~>ₜ - ↔ mod_to_itree m ~{σ, κs}~>ᵢ -.
Proof.
Admitted.

Lemma irefines_trefines EV (mi ms : module EV) :
  trefines mi ms ↔ irefines (mod_to_itree mi.(m_trans)) mi.(m_init)
                            (mod_to_itree ms.(m_trans)) ms.(m_init).
Proof.
  split; move => [Hr]; constructor => κs; move: (Hr κs).
  all: by rewrite !thas_trace_ihas_trace.
Qed.

(* Import here to check that there are not universe inconsistencies *)
From dimsum.core.itree Require Import asm rec.
