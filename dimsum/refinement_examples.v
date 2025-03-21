From dimsum.core Require Export module.
From dimsum.core Require Import srefines trefines lrefines filter.
From dimsum.core Require Import axioms.

(** * Examples of exercising the different notions of refinement  *)

(** * Definition of modules and their behaviors  *)
(*
    1
 0 --- 1
*)
Inductive mod1_step : nat → option nat → (nat → Prop) → Prop :=
| T1S0: mod1_step 0 (Some 1) (λ σ', σ' = 1).

Definition mod1_trans : mod_trans nat := ModTrans mod1_step.
Definition mod1 : module nat := Mod mod1_trans 0.

Lemma mod1_straces Pκs:
  0 ~{mod1_trans, Pκs}~>ₛ (λ _, True) ↔
  (Pκs [] ∧ Pκs [Nb]) ∨
  (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
  - move => [?|[??]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| | naive_solver ].
    move => ??. simplify_eq.
    by apply: STraceEnd.
Qed.

Lemma mod1_ttraces κs:
  0 ~{mod1_trans, κs}~>ₜ (λ _, True) ↔
    tall bool (λ b, if b then tnil else tcons 1 tnil) ⊆ κs.
Proof.
  split.
  - move => Ht.
    thas_trace_inv Ht. { by apply: (subtrace_all_l true). }
    inv_all @m_step => //. specialize_hyps. apply: (subtrace_all_l false).
    revert select (_ ⊆ _) => <-. constructor.
    thas_trace_inv => //.
    inv_all @m_step.
  - move => <-. apply thas_trace_all => -[]. 1: by tend.
    tstep_Some. { by econs. }
    move => ??. simplify_eq/=.
    by tend.
Qed.

(*
    1     2
 0 --- 1 --- 2
*)
Inductive mod2_step : nat → option nat → (nat → Prop) → Prop :=
| T2S0: mod2_step 0 (Some 1) (λ σ', σ' = 1)
| T2S1: mod2_step 1 (Some 2) (λ σ', σ' = 2)
.

Definition mod2_trans : mod_trans nat := ModTrans mod2_step.
Definition mod2 : module nat := Mod mod2_trans 0.

Lemma mod2_straces Pκs:
  0 ~{mod2_trans, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H3; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
  - move => [?|[[??]|[?[??]]]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |naive_solver].
      move => ??. simplify_eq.
      by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ??. simplify_eq/=.
      apply: STraceStep; [by constructor| |naive_solver].
      move => ??. simplify_eq/=.
      by apply: STraceEnd.
Qed.

(*         2
    1      /- 2
 0 --- 1 -∃
           \- 3
           3
*)
Inductive mod3_step : nat → option nat → (nat → Prop) → Prop :=
| T3S0: mod3_step 0 (Some 1) (λ σ', σ' = 1)
| T3S1: mod3_step 1 (Some 2) (λ σ', σ' = 2)
| T3S2: mod3_step 1 (Some 3) (λ σ', σ' = 3)
.

Definition mod3_trans : mod_trans nat := ModTrans mod3_step.
Definition mod3 : module nat := Mod mod3_trans 0.

(*
    3
 0 --- 1
*)
Inductive mod3'_step : nat → option nat → (nat → Prop) → Prop :=
| T3'S0: mod3'_step 0 (Some 3) (λ σ', σ' = 1)
.

Definition mod3'_trans : mod_trans nat := ModTrans mod3'_step.
Definition mod3' : module nat := Mod mod3'_trans 0.

Lemma mod3'_straces Pκs:
  0 ~{mod3'_trans, Pκs}~>ₛ (λ _, True) ↔
  (Pκs [] ∧ Pκs [Nb]) ∨
  (Pκs [] ∧ Pκs [Vis 3] ∧ Pκs [Vis 3; Nb]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
  - move => [?|[??]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| | naive_solver ].
    move => ??. simplify_eq.
    by apply: STraceEnd.
Qed.

(*
    1
 0 --- 1 -- UB
*)
Inductive mod1_ub_step : nat → option nat → (nat → Prop) → Prop :=
| T1US0: mod1_ub_step 0 (Some 1) (λ σ', σ' = 1)
| T1US1: mod1_ub_step 1 None (λ σ', False)
.

Definition mod1_ub_trans : mod_trans nat := ModTrans mod1_ub_step.
Definition mod1_ub : module nat := Mod mod1_ub_trans 0.

Lemma mod1ub_straces Pκs:
  0 ~{mod1_ub_trans, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1]).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
    naive_solver.
  - move => [?|[??]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ? ->.
      apply: STraceStep; [by constructor| |done].
      done.
Qed.

(*
 0 -- UB
*)
Inductive mod_ub_step {EV} : nat → option EV → (nat → Prop) → Prop :=
| TUS0: mod_ub_step 0 None (λ σ', False)
.

Definition mod_ub_trans EV : mod_trans EV := ModTrans mod_ub_step.
Definition mod_ub EV : module EV := Mod (mod_ub_trans EV) 0.

Lemma modub_straces EV Pκs:
  (* Note that without [event EV], for EV not inhabited, this would be
  equivalent to the program that does not do anything (but does not
  have UB). *)
  0 ~{mod_ub_trans EV, Pκs}~>ₛ (λ _, True) ↔ Pκs [].
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    naive_solver.
  - move => ?.
    apply: STraceStep; [by constructor| |done]. done.
Qed.

(*
 0 -- NB
*)
Inductive mod_nb_step {EV} : nat → option EV → (nat → Prop) → Prop :=
.

Definition mod_nb_trans EV : mod_trans EV := ModTrans mod_nb_step.
Definition mod_nb EV : module EV := Mod (mod_nb_trans EV) 0.

Lemma modnb_straces EV Pκs:
  0 ~{mod_nb_trans EV, Pκs}~>ₛ (λ _, True) ↔ Pκs [] ∧ Pκs [Nb].
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step.
  - move => ?. by apply: STraceEnd.
Qed.

(*        1
    /- 1 --- 3
0 -∀
    \- 2 --- 3
          2
*)

Inductive mod12_ang_step : nat → option nat → (nat → Prop) → Prop :=
| T12AS0: mod12_ang_step 0 None (λ σ', σ' = 1 ∨ σ' = 2)
| T12AS1: mod12_ang_step 1 (Some 1) (λ σ', σ' = 3)
| T12AS2: mod12_ang_step 2 (Some 2) (λ σ', σ' = 3)
.

Definition mod12_ang_trans : mod_trans nat := ModTrans mod12_ang_step.
Definition mod12_ang : module nat := Mod mod12_ang_trans 0.

Lemma mod12_ang_straces Pκs:
  0 ~{mod12_ang_trans, Pκs}~>ₛ (λ _, True) ↔
     (Pκs [] ∧ Pκs [Nb])
  ∨ (Pκs [] ∧ Pκs [Vis 1] ∧ Pκs [Vis 1; Nb] ∧ Pκs [Vis 2] ∧ Pκs [Vis 2; Nb] ).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
    have {}H := (H1 1 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H3; simplify_eq. 2: inv_all @m_step => //.
    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H7; simplify_eq. 2: inv_all @m_step => //.
    naive_solver.
  - move => [?|[?[??]]].
    + by apply: STraceEnd.
    + apply: STraceStep; [by constructor| |done].
      move => ? [?|?]; simplify_eq.
      * apply: STraceStep; [by constructor | | naive_solver].
        move => ? ->.  apply: STraceEnd; [done| naive_solver].
      * apply: STraceStep; [by constructor | |naive_solver].
        move => ? ->. apply: STraceEnd; [done| naive_solver].
Qed.

(** * Refinements *)
(** NB refines visible events *)
Lemma mod1_srefines_mod2 :
  srefines mod1 mod2.
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->.
  inversion H0; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //.
Qed.

(** NB refines visible events (for trefines) *)
Lemma mod1_trefines_mod2 :
  trefines mod1 mod2.
Proof.
  constructor => κs /= Hs.
  thas_trace_inv. { tend. }
  inv_all @m_step => //. specialize_hyps.
  revert select (_ ⊆ _) => <-.
  tstep_Some. { econs. } move => ? ->.
  thas_trace_inv. { tend. }
  inv_all @m_step.
Qed.

Lemma mod2_srefines_mod3 :
  srefines mod2 mod3.
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H0; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H2; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //.
Qed.

(** visible events refine UB *)
Lemma mod2_srefines_mod1_ub :
  srefines mod2 mod1_ub.
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H0; simplify_eq. 1: by apply: STraceEnd.
  apply: STraceStep. { constructor. } 2: naive_solver.
  done.
Qed.

(** visible events do not refine NB *)
Lemma mod2_srefines_mod1 :
  srefines mod2 mod1.
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  apply: STraceStep. { constructor. } 2: done.
  move => ? ->. simplify_eq.
  inversion H0; simplify_eq.
  { simplify_eq/=. apply: STraceEnd; [done|].
    done.
    (* split. 2: move => <-.  *)
  }
  inv_all @m_step => //.
  apply: STraceStep; [| | ]. Fail constructor.
  (* Undo. Undo. apply: STraceEnd; [done|]. *)
Abort. (* does not hold *)

(** angelic choice can be resolved on the left side *)
Lemma mod12_ang_srefines_mod1 :
  srefines mod12_ang mod1.
Proof.
  constructor => Pκs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //.
  have H := (H0 1 ltac:(naive_solver)).
  inversion H; simplify_eq. 1: by apply: STraceEnd.
  inv_all @m_step => //. specialize_hyps.
  inversion H3; simplify_eq.
  2: inv_all @m_step => //.
  apply: STraceStep; [by constructor| | naive_solver].
  move => ?->. by apply: STraceEnd.
Qed.

(** angelic choice does not allow coming up with arbitrary events (for srefines) *)
Lemma mod12_ang_not_srefines_mod3' :
  ¬ srefines mod12_ang mod3'.
Proof.
  move => -[]/= /(_ (λ κs, κs = [] ∨ κs = [Vis 1] ∨ κs = [Vis 1; Nb] ∨ κs = [Vis 2] ∨ κs = [Vis 2; Nb])).
  rewrite mod12_ang_straces mod3'_straces. naive_solver.
Qed.

(** But angelic choice leaking into events allows coming up with arbitrary events (for lrefines) *)
Lemma mod12_ang_lrefines_mod3' :
  lrefines mod12_ang mod3'.
Proof.
  constructor => κs /= Hs.
  inversion Hs; simplify_eq. 1: by apply: LTraceEnd.
  inv_all @m_step => //.
  have H := (H0 1 ltac:(naive_solver)).
  inversion H; simplify_eq. 1: by apply: LTraceEnd.
  inv_all @m_step => //. specialize_hyps.
  inversion H2; simplify_eq.
  2: inv_all @m_step => //.

  have H3 := (H0 2 ltac:(naive_solver)).
  inversion H3; simplify_eq.
  inv_all @m_step => //.
Qed.


(** * Commuting angelic choices and events  *)
(** Angelic choice commutes with events for srefines: *)

(*               B
    A      /- 3 --- 4
 1 --- 2 -∀
           \- 5 --- 6
                 C
 *)
Inductive mod_ang_comm1_step : nat → option nat → (nat → Prop) → Prop :=
| TAC1S1: mod_ang_comm1_step 0 (Some 1) (λ σ', σ' = 2)
| TAC1S2: mod_ang_comm1_step 2 None     (λ σ', σ' = 3 ∨ σ' = 5)
| TAC1S3: mod_ang_comm1_step 3 (Some 2) (λ σ', σ' = 4)
| TAC1S5: mod_ang_comm1_step 5 (Some 3) (λ σ', σ' = 6)
.

Definition mod_ang_comm1_trans : mod_trans nat := ModTrans mod_ang_comm1_step.
Definition mod_ang_comm1 : module nat := Mod mod_ang_comm1_trans 0.

(*         A     B
     /- 2 --- 3 --- 4
 1 -∀
     \- 5 --- 6 --- 7
           A     C
 *)
Inductive mod_ang_comm2_step : nat → option nat → (nat → Prop) → Prop :=
| TAC2S1: mod_ang_comm2_step 0 None     (λ σ', σ' = 2 ∨ σ' = 5)
| TAC2S2: mod_ang_comm2_step 2 (Some 1) (λ σ', σ' = 3)
| TAC2S3: mod_ang_comm2_step 3 (Some 2) (λ σ', σ' = 4)
| TAC2S5: mod_ang_comm2_step 5 (Some 1) (λ σ', σ' = 6)
| TAC2S6: mod_ang_comm2_step 6 (Some 3) (λ σ', σ' = 7)
.

Definition mod_ang_comm2_trans : mod_trans nat := ModTrans mod_ang_comm2_step.
Definition mod_ang_comm2 : module nat := Mod mod_ang_comm2_trans 0.

Lemma mod_ang_comm1_straces Pκs:
  0 ~{mod_ang_comm1_trans, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   (Pκs [Vis 1] ∧
    (Pκs [Vis 1; Nb] ∨
     (Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb] ∧
      Pκs [Vis 1; Vis 3] ∧ Pκs [Vis 1; Vis 3; Nb])))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    split; [naive_solver|].
    inversion H1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.

    have {}H := (H3 3 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H5; simplify_eq. 2: inv_all @m_step => //.

    have {}H := (H3 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H9; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
  - move => [?[?|[? HP]]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ??; simplify_eq.
    move: HP => [?|?]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
    + apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
Qed.

Lemma mod_ang_comm2_straces Pκs:
  0 ~{mod_ang_comm2_trans, Pκs}~>ₛ (λ _, True) ↔
    Pκs [] ∧
  (Pκs [Nb] ∨
   (Pκs [Vis 1] ∧
    (Pκs [Vis 1; Nb] ∨
     (Pκs [Vis 1; Vis 2] ∧ Pκs [Vis 1; Vis 2; Nb] ∧
      Pκs [Vis 1; Vis 3] ∧ Pκs [Vis 1; Vis 3; Nb])))).
Proof.
  split.
  - inversion 1; simplify_eq. 1: naive_solver.
    inv_all @m_step => //.
    split; [naive_solver|].

    have {}H := (H1 2 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H3; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H5; simplify_eq. 2: inv_all @m_step => //.

    have {}H := (H1 5 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H9; simplify_eq. 1: naive_solver.
    inv_all @m_step => //. specialize_hyps.
    inversion H11; simplify_eq. 2: inv_all @m_step => //.
    naive_solver.
  - move => [?[?|[? HP]]]. 1: by apply: STraceEnd.
    apply: STraceStep; [by constructor| |done].
    move => /= ?[?|?]; simplify_eq.
    + apply: STraceStep; [by constructor| |done].
      move => /= ? ->.
      move: HP => [?|?]. 1: by apply: STraceEnd.
      apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
    + apply: STraceStep; [by constructor| |done].
      move => /= ? ->.
      move: HP => [?|?]. 1: by apply: STraceEnd.
      apply: STraceStep; [by constructor | |naive_solver].
      move => /= ? ->. apply: STraceEnd; [done | naive_solver].
Qed.

Lemma mod_ang_comm_sequiv:
  srefines_equiv mod_ang_comm1 mod_ang_comm2.
Proof. apply: srefines_equiv_equiv => ?. rewrite mod_ang_comm1_straces mod_ang_comm2_straces. done. Qed.

(** but not for trefines *)
Lemma mod_ang_comm_not_trefines:
  ¬ trefines mod_ang_comm2 mod_ang_comm1.
Proof.
  move => [/=Hr]. opose proof* (Hr (tex bool (λ b, if b then tcons 1 $ tcons 2 tnil else tcons 1 $ tcons 3 tnil))) as Hr2.
  - tstep_None; [ constructor|]. move => ?[->|->].
    + apply: (thas_trace_ex true).
      tstep_Some; [constructor|] => ? ->.
      tstep_Some; [constructor|] => ? ->.
      by tend.
    + apply: (thas_trace_ex false).
      tstep_Some; [constructor|] => ? ->.
      tstep_Some; [constructor|] => ? ->.
      by tend.
  - move: Hr2 => /thas_trace_ex_inv/thas_trace_nil_inv Hr2.
    inversion Hr2; simplify_eq => //. 2: inv_all @m_step => //; easy.
    move: H => [[] {}Hr].
    all: move: Hr => /(thas_trace_cons_inv _ _ _)/thas_trace_nil_inv{}Hr.
    all: inversion Hr; simplify_K; [| inv_all @m_step => //; easy].
    all: move: H => [? [? {}Hr]].
    all: inv_all @m_step; specialize_hyps.

    all: move: Hr => /(thas_trace_cons_inv _ _ _)/thas_trace_nil_inv{}Hr.
    all: inversion Hr; simplify_K; [ move: H => [?[??]]; by inv_all @m_step|].
    all: inv_all @m_step.
    1: move: (H2 5 ltac:(naive_solver)) => {}Hr.
    2: move: (H2 3 ltac:(naive_solver)) => {}Hr.
    all: inversion Hr; simplify_K; [ move: H => [?[??]]; inv_all mod_ang_comm1_step|].
    all: inv_all @m_step.
    all: pose proof (transitivity H5 H3); easy.
Qed.
