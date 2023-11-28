From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import product seq_product state_transform.

Set Default Proof Using "Type".

(** * Linking *)

Section link.
  Context {EV : Type} {S : Type}.
  Implicit Types (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop).

(*
  Inductive link_case :=
  | MLFLeft | MLFRight | MLFNone
  | MLFEmit (e : io_event EV) (s : link_case)
  | MLFExpect (e : seq_product_event (io_event EV) (io_event EV)) (s : link_case)
  | MLFReturn (s : link_case)
  .
  Fixpoint mod_link_state_to_product_state (s : link_case) : seq_product_case :=
    match s with
    | MLFLeft => (Some SPLeft)
    | MLFRight => (Some SPRight)
    | MLFNone => None
    | MLFEmit e s => mod_link_state_to_product_state s
    | MLFExpect e s => mod_link_state_to_product_state s
    | MLFReturn s => mod_link_state_to_product_state s
    end.

  Definition mod_link_to_state (s : seq_product_case) (e : EV) : link_case :=
    match s with
    | None => MLFEmit (Outgoing, e) (MLFReturn MLFNone)
    | Some SPLeft => MLFReturn (MLFExpect (SPELeft (Incoming, e) (Some SPLeft)) (MLFReturn MLFLeft))
    | Some SPRight => MLFReturn (MLFExpect (SPERight (Incoming, e) (Some SPRight)) (MLFReturn MLFRight))
    end.

  Inductive mod_link_filter_step R :
    (link_case * S) → option (sm_event (seq_product_event (io_event EV) (io_event EV)) (io_event EV)) →
    ((link_case * S) → Prop) → Prop :=
  | MLFLeftS s e p' s' e':
    R (Some SPLeft) s e p' s' e' →
    mod_link_filter_step R (MLFLeft, s) (Some (SMERecv (SPELeft (Outgoing, e) p')))
      (λ σ, σ = (mod_link_to_state p' e', s'))
  | MLFRightS s e p' s' e':
    R (Some SPRight) s e p' s' e' →
    mod_link_filter_step R (MLFRight, s) (Some (SMERecv (SPERight (Outgoing, e) p')))
      (λ σ, σ = (mod_link_to_state p' e', s'))
  | MLFNoneS s e p' s' e':
    R None s e p' s' e' →
    mod_link_filter_step R (MLFNone, s) (Some (SMERecv (SPENone p')))
      (λ σ, σ = (MLFEmit (Incoming, e') (mod_link_to_state p' e'), s'))
  | MLFEmitS s' s e:
    mod_link_filter_step R (MLFEmit e s', s) (Some (SMEEmit e))
      (λ σ, σ = (s', s))
  | MLFExpectS s' s e:
    mod_link_filter_step R (MLFExpect e s', s) (Some (SMERecv e))
      (λ σ, σ = (s', s))
  | MLFReturnS s' s:
    mod_link_filter_step R (MLFReturn s', s) (Some (SMEReturn None))
      (λ σ, σ = (s', s))
  .
  Definition mod_link_filter R := Mod (mod_link_filter_step R).

  Definition mod_link_trans R m1 m2 (σ :
      seq_map_case (seq_product_event (io_event EV) (io_event EV)) *
      link_case * S * m1.(m_state) * m2.(m_state)) :
    seq_map_case (seq_product_event (io_event EV) (io_event EV)) *
           (seq_product_case * m_state m1 * m_state m2) * (link_case * S) :=
    (σ.1.1.1.1, (mod_link_state_to_product_state σ.1.1.1.2, σ.1.2, σ.2), (σ.1.1.1.2, σ.1.1.2)).
  Arguments mod_link_trans _ _ _ _ /.

  Definition mod_link R m1 m2 : module (io_event EV) :=
    mod_state_transform (mod_seq_map (mod_seq_product m1 m2) (mod_link_filter R))
                        (λ σ σ', σ' = mod_link_trans R m1 m2 σ).
*)
  Inductive link_case :=
  | MLFRun (sp : seq_product_case)
  | MLFRecv (sp : seq_product_side) (e : EV)
  | MLFUb (sp : seq_product_case).

  Definition link_to_case (ok : bool) (s : seq_product_case) (e : EV) : link_case :=
    if ok then if s is Some s' then MLFRecv s' e else MLFRun None else MLFUb s.

  Inductive link_filter R : map_mod_fn (seq_product_event (io_event EV) (io_event EV)) (io_event EV) (link_case * S) :=
  | MLFLeftS s e p' s' e' ok:
    R (Some SPLeft) s e p' s' e' ok →
    link_filter R (MLFRun (Some SPLeft), s) (SPELeft (Outgoing, e) p')
                    (if p' is None then Some (Outgoing, e') else None)
                    (link_to_case ok p' e', s') ok
  | MLFLeftRecvS s e:
    link_filter R (MLFRecv SPLeft e, s) (SPELeft (Incoming, e) (Some SPLeft)) None (MLFRun (Some SPLeft), s) true
  | MLFRightS s e p' s' e' ok:
    R (Some SPRight) s e p' s' e' ok →
    link_filter R (MLFRun (Some SPRight), s) (SPERight (Outgoing, e) p')
                    (if p' is None then Some (Outgoing, e') else None)
                    (link_to_case ok p' e', s') ok
  | MLFRightRecvS s e:
    link_filter R (MLFRecv SPRight e, s) (SPERight (Incoming, e) (Some SPRight)) None (MLFRun (Some SPRight), s) true
  | MLFNoneS s e p' s' e' ok:
    R None s e p' s' e' ok →
    link_filter R (MLFRun None, s) (SPENone p')
                    (Some (Incoming, e'))
                    (link_to_case ok p' e', s') ok
  .

  Definition link_state_trans R (m1 m2 : mod_trans (io_event EV)) (σ : link_case * S * m1.(m_state) * m2.(m_state)) :=
    (match σ.1.1.1 with
          | MLFRun sp => sp
          | MLFRecv sp _ => Some sp
          | MLFUb sp => sp
          end, σ.1.2, σ.2, (σ.1.1, if σ.1.1.1 is MLFUb _ then false else true)).
  Arguments link_state_trans _ _ _ _ /.

  Definition link_trans R (m1 m2 : mod_trans (io_event EV)) : mod_trans (io_event EV) :=
    state_transform_trans (map_trans (seq_product_trans m1 m2) (link_filter R))
      (λ σ σ', σ' = link_state_trans R m1 m2 σ).

  Global Instance link_trans_transform_wf R (m1 m2 : mod_trans (io_event EV)) :
    StateTransformWf (map_trans (seq_product_trans m1 m2) (link_filter R))
      (λ σ σ', σ' = link_state_trans R m1 m2 σ).
  Proof.
    constructor; [naive_solver|].
    move => [[??]?] [[[??]?][[??]?]] [[[??]?][[??]?]] ?????; simplify_eq.
    inv_all/= @m_step; inv_all @link_filter; destruct!.
    all: eexists (_, _, _); do 3 f_equal; repeat case_match => //; simplify_eq/= => //.
    all: unfold link_to_case in *; repeat case_match; simplify_eq => //.
  Qed.

  Global Instance link_vis_no_all R (m1 m2 : mod_trans _) `{!VisNoAng m1} `{!VisNoAng m2}:
    VisNoAng (link_trans R m1 m2).
  Proof.
    apply: mod_state_transform_vis_no_all.
    move => ??? [[[sp σ1]σ2][[σ s] ok]] ??.
    eexists (σ, s, σ1, σ2) => -[[[??]?]?]/=.
    split => ?; simplify_eq => //.
    inv_all/= @m_step; inv_all @link_filter; destruct!.
    all: unfold link_to_case in *; repeat case_match => //; simplify_eq => //.
  Qed.

  Definition link_mod R (m1 m2 : module (io_event EV)) (σ : S) : module (io_event EV) :=
    Mod (link_trans R m1.(m_trans) m2.(m_trans)) (MLFRun None, σ, m1.(m_init), m2.(m_init)).

  Lemma link_mod_trefines R m1 m2 m1' m2' σ `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
    trefines m1 m1' →
    trefines m2 m2' →
    trefines (link_mod R m1 m2 σ) (link_mod R m1' m2' σ).
  Proof.
    move => ??.
    apply: (state_transform_mod_trefines (Mod (map_trans _ _) _) (Mod (map_trans _ _) _)); [simpl; apply _| |done..].
    apply: (map_mod_trefines (Mod (seq_product_trans _ _) _) (Mod (seq_product_trans _ _) _)) => /=.
    by apply seq_product_mod_trefines.
  Qed.

  Lemma link_trans_step_left_i R m1 m2 s σ1 σ2 P `{!TStepI m1 σ1 P} :
    TStepI (link_trans R m1 m2) (MLFRun (Some SPLeft), s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRun (Some SPLeft), s, x, σ2)))
      | Some κ' => ∀ p' s' e' ok, R (Some SPLeft) s κ'.2 p' s' e' ok → κ'.1 = Outgoing →
                              G b (if p' is None then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (link_to_case ok p' e', s', x, σ2)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRun (Some SPLeft), s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter.
        split!; [done| |done] => /=?. destruct!.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [by destruct ok, s0|done|by destruct ok, s0|naive_solver].
  Qed.

  Lemma link_trans_step_right_i R m1 m2 s σ1 σ2 P `{!TStepI m2 σ2 P} :
    TStepI (link_trans R m1 m2) (MLFRun (Some SPRight), s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRun (Some SPRight), s, σ1, x)))
      | Some κ' => ∀ p' s' e' ok, R (Some SPRight) s κ'.2 p' s' e' ok → κ'.1 = Outgoing →
                              G b (if p' is None then Some (Outgoing, e') else None)
                               (λ G', P' (λ x, G' (link_to_case ok p' e', s', σ1, x)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRun (Some SPRight), s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter.
        split!; [done| |done] => /=?. destruct!.
        split!; [naive_solver..|]. move => /= ? HP. move: HP => /H2[?[??]]. eexists (_, _, _, _).
        split!; [by destruct s0, ok|done|by destruct s0, ok|naive_solver] => /=.
  Qed.

  Lemma link_trans_step_left_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m1 σ1 P} :
    TStepI (link_trans R m1 m2) (MLFRecv SPLeft e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecv SPLeft e, s, x, σ2)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFRun (Some SPLeft), s, x, σ2)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRecv SPLeft e, s, x, σ2))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter; naive_solver.
  Qed.

  Lemma link_trans_step_right_recv_i R m1 m2 s σ1 σ2 e P `{!TStepI m2 σ2 P} :
    TStepI (link_trans R m1 m2) (MLFRecv SPRight e, s, σ1, σ2) (λ G, P (λ b κ P',
      match κ with
      | None => G b None (λ G', P' (λ x, G' (MLFRecv SPRight e, s, σ1, x)))
      | Some κ' => κ' = (Incoming, e) → G b None (λ G', P' (λ x, G' (MLFRun (Some SPRight), s, σ1, x)))
      end)).
  Proof.
    constructor => G /(@tstepi_proof _ _ _ _ ltac:(done))?. clear TStepI0.
    apply: (steps_impl_submodule _ (link_trans _ _ _) (λ x, (MLFRecv SPRight e, s, σ1, x))); [done| |].
    - naive_solver.
    - move => /= ??? Hs. inv_all @state_transform_step. inv_all/= @m_step.
      + case_match; simplify_eq. naive_solver.
      + case_match; simplify_eq. inv_all @link_filter; naive_solver.
  Qed.

  Lemma link_trans_step_none_i R m1 m2 s σ1 σ2 :
    TStepI (link_trans R m1 m2) (MLFRun None, s, σ1, σ2) (λ G, ∀ e p' s' e' ok, R None s e p' s' e' ok →
      G true (Some (Incoming, e')) (λ G', G' (link_to_case ok p' e', s', σ1, σ2))).
  Proof.
    constructor => G HG. apply steps_impl_step_end => ???.
    inv_all/= @m_step; inv_all/= link_filter.
    split!; [naive_solver|done|] => /= ??. eexists (_, _, _, _). split!; by destruct s0, ok.
  Qed.

  Lemma link_trans_step_left_s R m1 m2 s σ1 σ2 P `{!TStepS m1 σ1 P} :
    TStepS (link_trans R m1 m2) (MLFRun (Some SPLeft), s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRun (Some SPLeft), s, x, σ2)))
      | Some (Outgoing, e) => ∃ p' s' e' ok, R (Some SPLeft) s e p' s' e' ok ∧
                              G (if p' is None then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (link_to_case ok p' e', s', σ', σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; repeat case_match; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_right_s R m1 m2 s σ1 σ2 P `{!TStepS m2 σ2 P} :
    TStepS (link_trans R m1 m2) (MLFRun (Some SPRight), s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRun (Some SPRight), s, σ1, x)))
      | Some (Outgoing, e) => ∃ p' s' e' ok, R (Some SPRight) s e p' s' e' ok ∧
                              G (if p' is None then Some (Outgoing, e') else None)
                               (λ G', P' (λ σ', G' (link_to_case ok p' e', s', σ1, σ')))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e]|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /= /HG'?; tstep_s.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; repeat case_match; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_left_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m1 σ1 P} :
    TStepS (link_trans R m1 m2) (MLFRecv SPLeft e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecv SPLeft e, s, x, σ2)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFRun (Some SPLeft), s, x, σ2)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_right_recv_s R m1 m2 s σ1 σ2 e P `{!TStepS m2 σ2 P} :
    TStepS (link_trans R m1 m2) (MLFRecv SPRight e, s, σ1, σ2) (λ G, P (λ κ P',
      match κ with
      | None => G None (λ G', P' (λ x, G' (MLFRecv SPRight e, s, σ1, x)))
      | Some (Incoming, e') => G None (λ G', e = e' ∧ P' (λ x, G' (MLFRun (Some SPRight), s, σ1, x)))
      | Some _ => False
      end)).
  Proof.
    constructor => G /(@tsteps_proof _ _ _ _ ltac:(done)) [κ [? [? HG']]]. clear TStepS0.
    destruct κ as [[[] e']|] => //; destruct!.
    all: eexists _, _; split; [done|] => G' /=; try move => [?]; move => /HG'?; tstep_s; simplify_eq.
    all: split!; [..|apply: steps_spec_mono; [done|]] => //=; try by econs.
    all: move => ?? [[[p?]?]?]//=?; destruct p => //; by simplify_eq/=.
  Qed.

  Lemma link_trans_step_none_s R m1 m2 s σ1 σ2 :
    TStepS (link_trans R m1 m2) (MLFRun None, s, σ1, σ2) (λ G, ∃ e p' s' e' ok, R None s e p' s' e' ok ∧
      G (Some (Incoming, e')) (λ G', G' (link_to_case ok p' e', s', σ1, σ2))).
  Proof.
    constructor => G [?[?[?[?[?[??]]]]]]. split!; [done|] => /=??.
    tstep_s. split!; [by econs|]. move => [[[??]?]?] /=. unfold link_to_case.
    repeat case_match; naive_solver.
  Qed.

  Lemma link_trans_step_ub_s R m1 m2 s σ1 σ2 sp :
    TStepS (link_trans R m1 m2) (MLFUb sp, s, σ1, σ2) (λ G, G None (λ G', True)).
  Proof. constructor => G ?. split!; [done|] => /=??. by tstep_s. Qed.

  Lemma link_trans_step_link_to_case_s R m1 m2 s σ1 σ2 sp P `{!Decision P} e :
    TStepS (link_trans R m1 m2) (link_to_case (bool_decide P) sp e, s, σ1, σ2) (λ G, G None
         (λ G', P → G' (link_to_case true sp e, s, σ1, σ2) )).
  Proof.
    constructor => G ?.
    split!; [done|] => /=??. case_bool_decide; [|by tstep_s].
    apply steps_spec_end. naive_solver.
 Qed.
End link.
Arguments link_state_trans _ _ _ _ _ /.
Arguments link_case : clear implicits.

Global Hint Resolve
       link_trans_step_left_i
       link_trans_step_right_i
       link_trans_step_left_recv_i
       link_trans_step_right_recv_i
       link_trans_step_none_i
       link_trans_step_left_s
       link_trans_step_right_s
       link_trans_step_left_recv_s
       link_trans_step_right_recv_s
       link_trans_step_none_s
       link_trans_step_ub_s
| 2 : typeclass_instances.
Global Hint Resolve
  link_trans_step_link_to_case_s
| 3 : typeclass_instances.


Lemma link_comm {EV S1 S2 : Type}
  (INV : seq_product_case → S1 → S2 → Prop)
  (R1 : seq_product_case → S1 → EV → seq_product_case → S1 → EV → bool → Prop)
  (R2 : seq_product_case → S2 → EV → seq_product_case → S2 → EV → bool → Prop)
  (m1 m2 : module (io_event EV))
  s1 s2:
  INV None s1 s2 →
  (∀ p s e p' s' e' ok s2,
      R1 p s e p' s' e' ok →
      INV p s s2 →
      ∃ s2', R2 (sp_opp <$> p) s2 e (sp_opp <$> p') s2' e' ok ∧ INV p' s' s2') →
  trefines (link_mod R1 m1 m2 s1) (link_mod R2 m2 m1 s2).
Proof.
  move => Hinv Hcomm. apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
    '(σl1, s1, σ1, σ2)
    '(σl2, s2, σ1', σ2'),
    ∃ sp, match σl1 with
          | MLFRun sp' => sp = sp' ∧ σl2 = MLFRun (sp_opp <$> sp)
          | MLFRecv sp' e => sp = Some sp' ∧ σl2 = MLFRecv (sp_opp sp') e
          | _ => False
          end ∧ σ2' = σ1 ∧ σ1' = σ2 ∧ INV sp s1 s2). }
  { split!. } { done. }
  move => {}n _ /= Hloop {Hinv}.
  move => [[[σl1 {}s1] σ1] σ2] [[[σl2 {}s2] σ1'] σ2'] [sp ?].
  destruct sp as [[]|] => //=; case_match; destruct!.
  - tsim_mirror (m1.(m_trans)) σ1. { tstep_s. by eexists None. }
    move => ???[??]?? p' ?? ok HR1 ?. simplify_eq/=.
    ogeneralize* Hcomm; [done|done|] => /= -[?[??]].
    tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
    destruct p' => /=.
    + apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      destruct ok; [|by tstep_s] => /=.
      apply Hloop; [done|]. split!.
    + split!; [done|]. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      destruct ok; [|by tstep_s] => /=.
      apply Hloop; [done|]. split!.
  - tsim_mirror (m1.(m_trans)) σ1. { tstep_s. by eexists None. }
    move => ??? [??] Pσ Hs ?. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
    apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
    apply Hloop; [done|]. split!.
  - tsim_mirror (m2.(m_trans)) σ2. { tstep_s. by eexists None. }
    move => ??? [??] Pσ Hs p' ?? ok HR1 ?. simplify_eq/=.
    ogeneralize* Hcomm; [done|done|] => /= -[?[??]].
    tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
    destruct p' => /=.
    + apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      destruct ok; [|by tstep_s] => /=.
      apply Hloop; [done|]. split!.
    + split!; [done|]. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      destruct ok; [|by tstep_s] => /=.
      apply Hloop; [done|]. split!.
  - tsim_mirror (m2.(m_trans)) σ2. { tstep_s. by eexists None. }
    move => ??? [??] Pσ Hs ?. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
    apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
    apply Hloop; [done|]. split!.
  - tstep_i. move => ? p' ?? ok HR1.
    ogeneralize* Hcomm; [done|done|] => /= -[?[??]].
    tstep_s. split!; [done|]. destruct ok; [|by tstep_s] => /=.
    apply Hloop; [done|].
    repeat case_match => //; destruct!; split!; destruct sp; by simplify_eq/=.
Qed.

(* identifies modules, naming: (Left + Middle + Right) *)
Inductive link_assoc_side :=
| LALeft | LAMiddle | LARight.

(* identifies linkers, naming: (_ 1_23 (_ 23 _)) ↔ ((_ 12 _) 12_3 _) *)
Inductive link_assoc_linker :=
| LA_1_23 | LA_23 | LA_12_3 | LA_12.

Definition la_side_to_sp_side (ln : link_assoc_linker) (la : option link_assoc_side)
  : option seq_product_side :=
  match ln with
  | LA_1_23 =>
      match la with
      | Some LALeft => Some SPLeft
      | Some LAMiddle => Some SPRight
      | Some LARight => Some SPRight
      | None => None
      end
  | LA_23 =>
      match la with
      | Some LALeft => None
      | Some LAMiddle => Some SPLeft
      | Some LARight => Some SPRight
      | None => None
      end
  | LA_12_3 =>
      match la with
      | Some LALeft => Some SPLeft
      | Some LAMiddle => Some SPLeft
      | Some LARight => Some SPRight
      | None => None
      end
  | LA_12 =>
      match la with
      | Some LALeft => Some SPLeft
      | Some LAMiddle => Some SPRight
      | Some LARight => None
      | None => None
      end
  end.

Definition la_wrap_R {EV S}
  (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop) :
  seq_product_case → seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop :=
  λ pdest p s e p' s' e' ok,
    if bool_decide (p = pdest) then p = p' ∧ s' = s ∧ e' = e ∧ ok = true else R p s e p' s' e' ok.

Arguments la_wrap_R _ _ _ !_ !_ _ _ _ _ _ _ /.

(* The following functions define in which order one traverses the
linkers from a given link_assoc_side.
fst1_23: first linker in 1_23 side of assoc lemma
fst12_3: first linker in 12_3 side of assoc lemma
snd1_23: second linker in 1_23 side of assoc lemma
snd12_3: second linker in 12_3 side of assoc lemma *)
Definition la_side_to_fst_1_23 (la : option link_assoc_side) : link_assoc_linker :=
  match la with
  | Some LALeft => LA_1_23
  | Some LAMiddle => LA_23
  | Some LARight => LA_23
  | None => LA_1_23
  end.

Definition la_side_to_fst_12_3 (la : option link_assoc_side) : link_assoc_linker :=
  match la with
  | Some LALeft => LA_12
  | Some LAMiddle => LA_12
  | Some LARight => LA_12_3
  | None => LA_12_3
  end.

Definition la_side_to_snd_1_23 (la : option link_assoc_side) : link_assoc_linker :=
  match la with
  | Some LALeft => LA_23
  | Some LAMiddle => LA_1_23
  | Some LARight => LA_1_23
  | None => LA_23
  end.

Definition la_side_to_snd_12_3 (la : option link_assoc_side) : link_assoc_linker :=
  match la with
  | Some LALeft => LA_12_3
  | Some LAMiddle => LA_12_3
  | Some LARight => LA_12
  | None => LA_12
  end.

Definition la_sel_state {S} (ln : link_assoc_linker) (s1_23 s23 s12_3 s12 : S) : S :=
  match ln with
  | LA_1_23 => s1_23
  | LA_23 => s23
  | LA_12_3 => s12_3
  | LA_12 => s12
  end.

Definition la_sel_state_rev {S} (la : option link_assoc_side) (ln : link_assoc_linker)
  (sf1 sf2 ss1 ss2 : S) : S :=
  match la with
  | Some LALeft =>
      match ln with
      | LA_1_23 => sf1
      | LA_23 => ss1
      | LA_12_3 => ss2
      | LA_12 => sf2
      end
  | Some LAMiddle =>
      match ln with
      | LA_1_23 => ss1
      | LA_23 => sf1
      | LA_12_3 => ss2
      | LA_12 => sf2
      end
  | Some LARight =>
      match ln with
      | LA_1_23 => ss1
      | LA_23 => sf1
      | LA_12_3 => sf2
      | LA_12 => ss2
      end
  | None =>
      match ln with
      | LA_1_23 => sf1
      | LA_23 => ss1
      | LA_12_3 => sf2
      | LA_12 => ss2
      end
  end.

Lemma la_sel_state_rev_fst_1_23 {S} (s x : S) la :
  la_sel_state_rev la (la_side_to_fst_1_23 la) s x x x = s.
Proof. destruct la as [[]|] eqn:? => //=. Qed.
Lemma la_sel_state_rev_fst_12_3 {S} (s x : S) la :
  la_sel_state_rev la (la_side_to_fst_12_3 la) x s x x = s.
Proof. destruct la as [[]|] eqn:? => //=. Qed.
Lemma la_sel_state_rev_snd_1_23 {S} (s x : S) la :
  la_sel_state_rev la (la_side_to_snd_1_23 la) x x s x = s.
Proof. destruct la as [[]|] eqn:? => //=. Qed.
Lemma la_sel_state_rev_snd_12_3 {S} (s x : S) la :
  la_sel_state_rev la (la_side_to_snd_12_3 la) x x x s = s.
Proof. destruct la as [[]|] eqn:? => //=. Qed.

Lemma link_assoc1 {EV S : Type}
  (R : link_assoc_linker → seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop)
  (INV : option link_assoc_side → S → S → S → S → Prop)
  (m1 m2 m3 : module (io_event EV))
  s1_23 s23 s12_3 s12
  `{!VisNoAng (m_trans m1)} `{!VisNoAng (m_trans m2)} `{!VisNoAng (m_trans m3)}:
  (∀ ln p s e p' s' e' ok, R ln p s e p' s' e' ok → e = e') →
  INV None s1_23 s23 s12_3 s12 →
  (∀ la p1' s1_23 s23 s12_3 s12 sf1' e1 e1' ok1,
      let lnf1 := la_side_to_fst_1_23 la in
      let lnf2 := la_side_to_fst_12_3 la in
      let lns1 := la_side_to_snd_1_23 la in
      let lns2 := la_side_to_snd_12_3 la in
      INV la s1_23 s23 s12_3 s12 →
      (** We first traverse the first linker in the implementation ... *)
      R lnf1 (la_side_to_sp_side lnf1 la) (la_sel_state lnf1 s1_23 s23 s12_3 s12) e1 p1' sf1' e1' ok1 →
      ∃ la' sf2', la_side_to_sp_side lnf1 la' = p1' ∧ ok1 = true ∧
      (** ... then the first linker in the specification ... *)
      R lnf2 (la_side_to_sp_side lnf2 la) (la_sel_state lnf2 s1_23 s23 s12_3 s12) e1
        (la_side_to_sp_side lnf2 la') sf2' e1' ok1 ∧
      ∀ p2' ss1' e2' ok2,
      (** ... then optionally the second linker in the implementation ... *)
      la_wrap_R (R lns1) (la_side_to_sp_side lns1 la') (la_side_to_sp_side lns1 la)
        (la_sel_state lns1 s1_23 s23 s12_3 s12) e2' p2' ss1' e1' ok2 →
      ∃ ss2', la_side_to_sp_side lns1 la' = p2' ∧ ok2 = true ∧
      (** ... and finally optionally the second linker in the specification. *)
      la_wrap_R (R lns2) (la_side_to_sp_side lns2 la') (la_side_to_sp_side lns2 la)
        (la_sel_state lns2 s1_23 s23 s12_3 s12) e2' (la_side_to_sp_side lns2 la') ss2' e1' ok2 ∧
      INV la'
        (la_sel_state_rev la LA_1_23 sf1' sf2' ss1' ss2')
        (la_sel_state_rev la LA_23 sf1' sf2' ss1' ss2')
        (la_sel_state_rev la LA_12_3 sf1' sf2' ss1' ss2')
        (la_sel_state_rev la LA_12 sf1' sf2' ss1' ss2')
   ) →
  trefines (link_mod (R LA_1_23) m1 (link_mod (R LA_23) m2 m3 s23) s1_23)
    (link_mod (R LA_12_3) (link_mod (R LA_12) m1 m2 s12) m3 s12_3).
Proof.
  move => Heq Hinv HR. apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
    '(σ1_23, s1_23, σ1, (σ23, s23, σ2, σ3))
    '(σ12_3, s12_3, (σ12, s12, σ1', σ2'), σ3'),
    ∃ la,
      σ1_23 = MLFRun (la_side_to_sp_side LA_1_23 la) ∧ σ23 = MLFRun (la_side_to_sp_side LA_23 la) ∧
      σ12_3 = MLFRun (la_side_to_sp_side LA_12_3 la) ∧ σ12 = MLFRun (la_side_to_sp_side LA_12 la) ∧
      σ1' = σ1 ∧ σ2' = σ2 ∧ σ3' = σ3 ∧ INV la s1_23 s23 s12_3 s12). }
  { eexists None. split!. } { done. }
  move => {}n _ /= Hloop {Hinv}.
  move => [[[σ1_23 {}s1_23] σ1] [[[σ23 {}s23] σ2] σ3]] [[[σ12_3 {}s12_3] [[[σ12 {}s12] σ1'] σ2']] σ3'] Hinv.
  destruct!. destruct la as [[]|] => /=.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    destruct κ as [[??]|]. 2: {
      tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??.
      tend. split!; [done|]. apply Hloop; [done|]. split!; [..|done]; done.
    }
    move => *. simplify_eq/=.
    exploit HR; [done..|] => -[la'[?[?[?[? Hcont]]]]]. simplify_eq/=.
    destruct la' as [[]|]; simplify_eq/=.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      exploit Hcont; [done|]. move => ?. destruct!/=.
      tsim_mirror (m1.(m_trans)) σ'. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      tstep_i => *. simplify_eq.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tsim_mirror (m2.(m_trans)) σ2. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tend. have [σ' Hσ']:= vis_no_all _ _ _ ltac:(done). split!; [naive_solver|].
      tstep_i => ???? ok' ??. simplify_eq/=.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      exploit Heq; [done|] => ?. subst.
      split!; [done|] => /=. apply: steps_spec_step_end; [done|] => σ'' ?.
      have ? : σ'' = σ' by naive_solver. subst.
      tsim_mirror (m3.(m_trans)) σ3. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      split!; [done|] => /=. split!; [done|].
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      apply Hloop; [done|]. split!; [..|done]; done.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    destruct κ as [[??]|]. 2: {
      tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??.
      tend. split!; [done|]. apply Hloop; [done|]. split!; [..|done]; done.
    }
    move => *. simplify_eq/=.
    exploit HR; [done..|] => -[la'[?[?[?[? Hcont]]]]]. simplify_eq/=.
    destruct la' as [[]|]; simplify_eq/=.
    + move => *. simplify_eq/=.
      exploit Heq; [done|] => ?. subst.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      tsim_mirror (m1.(m_trans)) σ1. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      exploit Hcont; [done|] => *. destruct!/=.
      tsim_mirror (m2.(m_trans)) σ'. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      exploit Hcont; [done|] => *. destruct!/=. split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      tsim_mirror (m3.(m_trans)) σ3. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + move => *. simplify_eq/=.
      exploit Heq; [done|] => ?. subst.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=. split!; [done|] => /=.
      split!; [done|]. apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      apply: Hloop; [done|]. split!; [..|done]; done.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    destruct κ as [[??]|]. 2: {
      tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??.
      tend. split!; [done|]. apply Hloop; [done|]. split!; [..|done]; done.
    }
    move => *. simplify_eq/=.
    exploit HR; [done..|] => -[la'[?[?[?[? Hcont]]]]]. simplify_eq/=.
    destruct la' as [[]|]; simplify_eq/=.
    + move => *. simplify_eq/=.
      exploit Heq; [done|] => ?. subst.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      tstep_s. split!; [done|] => /=.
      tsim_mirror (m1.(m_trans)) σ1. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      exploit Hcont; [done|] => *. destruct!/=.
      tstep_s. split!; [done|] => /=.
      tsim_mirror (m2.(m_trans)) σ2. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      exploit Hcont; [done|] => *. destruct!/=.
      tsim_mirror (m3.(m_trans)) σ'. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + move => *. simplify_eq/=.
      exploit Heq; [done|] => ?. subst.
      exploit Hcont => /=; [done|]. move => *. destruct!/=.
      tstep_s. eexists (Some (Outgoing, _)). split!; [done|] => /=. split!; [done|] => /=.
      apply: steps_spec_step_end; [done|] => σ' ?. tend. split!; [done|].
      apply: Hloop; [done|]. split!; [..|done]; done.
  - tstep_i => ???? ok ?.
    exploit HR; [done..|] => -[la'[?[?[?[? Hcont]]]]]. simplify_eq/=.
    tstep_s. split!; [done|].
    destruct la' as [[]|]; simplify_eq/=.
    + exploit (Hcont None); [done|] => *. destruct!/=.
      tstep_s. split!; [done|] => /=.
      tsim_mirror (m1.(m_trans)) σ1. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_i => ???? ok ??. simplify_eq/=. exploit Hcont; simpl; [done|].
      move => *. destruct!. tstep_s. split!; [done|].
      tsim_mirror (m2.(m_trans)) σ2. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + tstep_i => ???? ok ??. simplify_eq/=. exploit Hcont; simpl; [done|].
      move => *. destruct!/=.
      tsim_mirror (m3.(m_trans)) σ3. { tstep_s. by eexists None. }
      move => ???????. simplify_eq/=. tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [by apply o_lt_impl_le|]. split!; [..|done]; done.
    + exploit (Hcont None); [done|] => *. destruct!/=.
      apply: Hloop; [done|]. split!; [..|done]; done.
Qed.
