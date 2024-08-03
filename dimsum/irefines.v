From dimsum.core Require Import module trefines.
From dimsum.core.itree Require Import upstream events.
Import ITreeStdppNotations.

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
