From dimsum.core Require Export module trefines.
From dimsum.core Require Import axioms.

(** * Proving refinement *)
(** This file contains various proof techniques for proving
refinement. The development uses mostly [tsim]. *)

(** * [mod_to_trace] *)
Fixpoint mod_to_trace {EV} (m : mod_trans EV) (n : ordinal) (σ : m.(m_state)) : trace EV :=
  match n with
  | oO => tnb
  | oS n' => tall { x : option EV * (m.(m_state) → Prop) | m.(m_step) σ x.1 x.2} (λ x,
         tapp (option_trace (`x).1) (tex {σ' : m.(m_state) | (`x).2 σ'} (λ σ', mod_to_trace m n' (`σ'))))
  | oChoice T fn => tall T (λ x, mod_to_trace m (fn x) σ)
  end.

Lemma thas_trace_mod_to_trace {EV} (m : mod_trans EV) n σ :
  σ ~{m, mod_to_trace m n σ}~>ₜ -.
Proof.
  elim: n σ => /=.
  - move => ?. tend. apply tnb_sub.
  - move => n IH σ. apply thas_trace_all => -[[/=??]?].
    tstep; [done| |done] => ??. apply: (thas_trace_ex (exist _ _ _)); [done|]. naive_solver.
  - move => ?? IH σ. apply thas_trace_all. naive_solver.
Qed.

Lemma mod_to_trace_mono {EV} (m : mod_trans EV) n n' σ :
  n' ⊆ n →
  mod_to_trace m n σ ⊆ mod_to_trace m n' σ.
Proof.
  move => Hsub. elim: Hsub σ => /=.
  - move => ??. apply tnb_sub.
  - move => ??? IH σ.
    apply tall_mono => -[[/=??]?].
    apply tapp_mono; [done|].
    apply tex_mono => ?.
    naive_solver.
  - move => T f {}n ? IH σ. econs. naive_solver.
  - move => T f {}n x Hle IH σ. econs. naive_solver.
Qed.

(** * [inv] *)
Lemma inv_implies_trefines {EV} (m1 m2 : module EV) (inv : m1.(m_trans).(m_state) → m2.(m_trans).(m_state) → Prop):
  inv m1.(m_init) m2.(m_init) →
  (∀ σi1 σs1 Pσi2 e,
      inv σi1 σs1 → m_step m1.(m_trans) σi1 e Pσi2 →
      σs1 ~{ m2.(m_trans), option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(m_init) m2.(m_init) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv Hstep).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ??????????.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

Lemma inv'_implies_trefines {EV} (m1 m2 : module EV) (inv : m1.(m_trans).(m_state) → m2.(m_trans).(m_state) → trace EV → Prop):
  (∀ κs, m_init m1 ~{ m1.(m_trans), κs }~>ₜ (λ _, True) → inv m1.(m_init) m2.(m_init) κs) →
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1.(m_trans) σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2.(m_trans), option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) →
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep Hinvall.
  constructor => // κs. move: m1.(m_init) m2.(m_init) (Hinvinit κs) => σi1 σs1 Hinv Hsteps.
  move: (Hinv Hsteps) => {}Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ _ _ Hinv Hstep Hcons).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ?????? IH ???.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

(** * [wp] *)
Inductive wp {EV} (m1 m2 : mod_trans EV) : ordinal → m1.(m_state) -> m2.(m_state) -> Prop :=
| Wp_step' σi1 σs1 n:
    (∀ Pσi2 κ n', oS n' ⊆ n → m_step m1 σi1 κ Pσi2 -> ∃ Pσ2,
      σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2) ->
    wp m1 m2 n σi1 σs1
.

Lemma Wp_step {EV} (m1 m2 : mod_trans EV) σi1 σs1 n:
  (∀ Pσi2 n' κ, oS n' ⊆ n → m_step m1 σi1 κ Pσi2 ->
      σs1 ~{ m2, option_trace κ }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2)) ->
    wp m1 m2 n σi1 σs1
.
Proof. move => ?. constructor. naive_solver. Qed.

Lemma wp_mono {EV} (m1 m2 : mod_trans EV) n1 n2 σi σs:
  wp m1 m2 n1 σi σs →
  n2 ⊆ n1 →
  wp m1 m2 n2 σi σs.
Proof.
  move => Hwp Hle.
  constructor => ?????.
  inversion_clear Hwp as [??? Hwp2]; subst.
  have {Hwp2}[?[? Hwp]]:= Hwp2 _ _ _ ltac:(by etrans) ltac:(done).
  eexists _. split; [done|] => ??.
  have {Hwp}[?[? Hwp]]:= Hwp _ ltac:(done).
  by eexists _.
Qed.

Lemma wp_implies_refines {EV} (m1 m2 : module EV):
  (∀ n, wp m1.(m_trans) m2.(m_trans) n m1.(m_init) m2.(m_init)) →
  trefines m1 m2.
Proof.
  destruct m1 as [m1 σi1]. destruct m2 as [m2 σs1]. move => /= Hwp.
  constructor => κs /= /thas_trace_n [n Hsteps].
  elim: Hsteps σs1 {Hwp}(Hwp n); clear.
  - move => ????????. tend.
  - move => Pσ2 fn σ1 Pσ3 κ κs κs' n Hstep ? IH Hlt Hκs σs1 Hwp. rewrite -Hκs.
    inversion_clear Hwp as [??? Hwp2]; subst.
    have {Hwp2}[?[? Hwp]]:= Hwp2 _ _ _ ltac:(done) ltac:(done).
    apply: thas_trace_trans; [done|] => ??.
    have {Hwp}[?[? Hwp]]:= Hwp _ ltac:(done).
    apply: IH; [done|] => ?.
    apply: wp_mono; [done|]. by econs.
  - move => T fn f σ κs Pσ n ? IH Hκs Hle σs1 Hwp. rewrite -Hκs.
    apply thas_trace_all => ?. apply: IH.
    apply: wp_mono; [done|]. etrans; [|done]. by econs.
Qed.

(* Print Assumptions wp_implies_refines. *)

Lemma wp_complete {EV} (m1 m2 : module EV):
  trefines m1 m2 →
  ∀ n, wp m1.(m_trans) m2.(m_trans) n m1.(m_init) m2.(m_init).
Proof.
  destruct m1 as [m1 σi1]. destruct m2 as [m2 σs1]. move => /= [Href] n.
  have {Href} := Href (mod_to_trace _ n σi1) ltac:(apply thas_trace_mod_to_trace) => /=.
  elim/o_lt_ind: n σi1 σs1 => /= n IH σi σs Ht.
  apply Wp_step => Pσi n' κ Hsub Hstep.
  move: Ht => /thas_trace_mono Ht.
  have {Ht} := Ht _ (λ _, True) ltac:(by apply mod_to_trace_mono) ltac:(done) => /=.
  move => /thas_trace_all_inv Ht.
  have /=/thas_trace_app_inv {}Ht := (Ht (exist _ (κ, Pσi) Hstep)).
  rewrite -(tapp_tnil_r (option_trace κ)). apply: thas_trace_trans; [done|].
  move => ? /= /thas_trace_ex_inv {}Ht.
  apply: thas_trace_mono; [done..|] => ? /= [[??]?].
  naive_solver.
Qed.

(* Print Assumptions wp_complete. *)


(** * [sim] *)
(** coinductive version of wp *)
CoInductive sim {EV} (m1 m2 : mod_trans EV) σi1 σs1: Prop :=
| sim_step  :
    (∀ Pσi2 κ, m_step m1 σi1 κ Pσi2 ->
     ∃ Pσ2, σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
      ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ sim m1 m2 σi2 σs2) ->
    sim m1 m2 σi1 σs1.

Lemma sim_wp {EV} (m1 m2 : mod_trans EV) σi σs :
  sim m1 m2 σi σs → ∀ n, wp m1 m2 n σi σs.
Proof.
  intros Hsim n; induction n in σi, σs, Hsim |-*.
  - constructor. intros ????. exfalso.
    eapply o_not_le_S. etrans; first done. eapply o_le_O.
  - constructor. intros Pσi' κ' n' Hle Hstep.
    destruct Hsim as [Hsim]. destruct (Hsim _ _ Hstep) as (Pσs' & Hsteps & Hcont).
    eexists _; split; first done.
    intros σs2 [σi2 [HP Hsim']]%Hcont. eexists. split; first done.
    eapply wp_mono; first by eauto.
    inversion Hle; subst. done.
  - constructor. intros Pσi' κ' n' Hle Hstep.
    destruct Hsim as [Hsim]. destruct (Hsim _ _ Hstep) as (Pσs' & Hsteps & Hcont).
    eexists _; split; first done.
    intros σs2 [σi2 [HP Hsim']]%Hcont.
    eexists. split; first done. eapply o_le_choice_inv in Hle as [x Hle].
    eapply wp_mono; first by eauto.
    etrans; last done. eapply o_le_S.
Qed.

Lemma existential_property {X} (P: ordinal → X → Prop):
  (∀ n, ∃ x, P n x) →
  (∀ n n' x, P n x → n' ⊆ n → P n' x) →
  (∃ x, ∀ n, P n x).
Proof.
  intros HP Hdown. destruct (AxClassic (∃ x, ∀ n, P n x)) as [|Hnex]; first done.
  (* we commute the quantifiers inward*)
  assert (∀ x, ∃ n, ¬ P n x) as Hnp.
  { intros x. destruct (AxClassic (∃ n, ¬ P n x)) as [|Hnp]; first done. exfalso.
    eapply Hnex. exists x. intros n'. destruct (AxClassic (P n' x)); first done.
    exfalso. eapply Hnp. exists n'. done. }
  (* choice *)
  have [F Hnx]:= AxChoice _ _ _ Hnp.

  (* we take the supremum *)
  pose (n_sup := (oChoice X (λ x, F x))).

  assert (∀ x, ¬ P n_sup x) as Hnsup.
  { intros x Hp. eapply Hnx. eapply Hdown; first done.
    eapply o_le_choice_r. done. }

  destruct (HP n_sup) as [x_sup HPnx].
  exfalso. by eapply Hnsup.
Qed.


Lemma forall_forall {X Y: Type} (P: X → Y → Prop):
  (∀ x y, P x y) → (∀ y x, P x y).
Proof. naive_solver. Qed.

Lemma wp_sim_inner {EV} (m1 m2 : mod_trans EV) σi1 σs1:
  (∀ n, wp m1 m2 n σi1 σs1) →
  (∀ Pσi2 κ, m_step m1 σi1 κ Pσi2 ->
  ∃ Pσ2, σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
  ∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ (∀ n, wp m1 m2 n σi2 σs2)).
Proof.
  intros Hwp Pσi2 κ Hstep.
  (* destruct Hwp underneath the quantifier *)
  assert (∀ n, ∀ n', oS n' ⊆ n →
       ∃ Pσ2, σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
      (∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n' σi2 σs2)) as Hnext.
  { intros n. destruct (Hwp n) as [σi1 σs1 n Hwp']. intros ??. by unshelve eapply (Hwp' _ _ _ _ Hstep). }
  (* instantiate n' *)
  clear Hwp. assert (∀ n, ∃ Pσ2, σs1 ~{ m2, option_trace κ }~>ₜ Pσ2 ∧
          (∀ σs2, Pσ2 σs2 → ∃ σi2, Pσi2 σi2 ∧ wp m1 m2 n σi2 σs2)) as Hwp.
  { intros n. eapply Hnext. reflexivity. }
  eapply existential_property in Hwp as [Pσ2 Hwp]; last first.
  { (* prove downwards closure *) naive_solver eauto using wp_mono. }
  eapply forall_and_distr in Hwp as [Hstep' Hwp].
  specialize (Hstep' oO).
  eexists. split; first done.
  intros σs2 HPσs2.
  pose proof (forall_forall _ Hwp) as Hwp'. clear Hwp.
  specialize (Hwp' σs2).
  pose proof (forall_forall _ Hwp') as Hwp. clear Hwp'.
  specialize (Hwp HPσs2); simpl in Hwp.
  eapply existential_property in Hwp as [σi2 Hwp]; last first.
  { (* prove downwards closure *) naive_solver eauto using wp_mono. }
  eapply forall_and_distr in Hwp as [HP Hwp].
  specialize (HP oO).
  eexists. split; first done.
  done.
Qed.

Lemma wp_sim {EV} (m1 m2 : mod_trans EV) σi σs :
  (∀ n, wp m1 m2 n σi σs) → sim m1 m2 σi σs.
Proof.
  revert σi σs. cofix IH; intros σi σs Hwp.
  econstructor. intros Pσi2 κ Hstep.
  eapply wp_sim_inner in Hwp as [Pσ2 [Hstep' Hrest]]; last done.
  naive_solver.
Qed.

Lemma sim_wp_iff {EV} (m1 m2 : mod_trans EV) σi σs:
  (∀ n, wp m1 m2 n σi σs) ↔ sim m1 m2 σi σs.
Proof. split; eauto using sim_wp, wp_sim. Qed.

Lemma sim_trefines {EV} (m1 m2 : module EV):
  sim m1.(m_trans) m2.(m_trans) m1.(m_init) m2.(m_init) ↔ trefines m1 m2.
Proof.
  rewrite -sim_wp_iff.
  split; eauto using wp_implies_refines, wp_complete.
Qed.

(* Print Assumptions sim_trefines. *)

(** * [tsim] *)
Definition tsim {EV} (n : ordinal) (b : bool) (mi ms : mod_trans EV) (σi : mi.(m_state)) (κss : trace EV) (σs : ms.(m_state))  :=
  ∀ κs n',
    oS?b n' ⊆ n →
    σi ~{ mi, κs, n' }~>ₜ - →
    σs ~{ ms, tapp κss κs }~>ₜ -.

Notation "σi ⪯{ mi , ms , n , b , κss } σs" := (tsim n b mi ms σi κss σs) (at level 70,
    format "σi  ⪯{ mi ,  ms ,  n ,  b ,  κss }  σs") : type_scope.
Notation "σi ⪯{ mi , ms , n , b } σs" := (tsim n b mi ms σi tnil σs) (at level 70,
    format "σi  ⪯{ mi ,  ms ,  n ,  b }  σs") : type_scope.

Lemma tsim_implies_trefines {EV} (mi ms : module EV) :
  (∀ n, mi.(m_init) ⪯{mi.(m_trans), ms.(m_trans), n, false} ms.(m_init)) →
  trefines mi ms.
Proof. move => Hsim. constructor => ? /thas_trace_n [??]. by apply: Hsim => /=. Qed.

Lemma trefines_implies_tsim {EV} (mi ms : mod_trans EV) σi σs n b:
  trefines (Mod mi σi) (Mod ms σs) →
  σi ⪯{mi, ms, n, b} σs.
Proof. move => [Hr] ??? /=?. apply Hr. by apply: thas_trace_n_2. Qed.

Lemma tsim_mono_to_true {EV} {mi ms : mod_trans EV} σi σs n n' κs b:
  σi ⪯{mi, ms, n', true, κs} σs →
  oS n ⊆ n' →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof. move => Hsim Hn ???. apply: Hsim. etrans; [|done]. econs. etrans; [|done]. apply o_le_S_maybe. Qed.

Lemma tsim_mono_to_tiS {EV} {mi ms : mod_trans EV} σi σs n κs:
  (∀ n', oS n' ⊆ n → σi ⪯{mi, ms, n', false, κs} σs) →
  σi ⪯{mi, ms, n, true, κs} σs.
Proof. move => Hsim ??/=?. by apply: Hsim. Qed.

Lemma tsim_mono {EV} {mi ms : mod_trans EV} σi σs b n n' κs:
  σi ⪯{mi, ms, n', b, κs} σs →
  n ⊆ n' →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof. move => Hsim Hn ???. apply: Hsim. by destruct b; (etrans; [done|]). Qed.

Lemma tsim_mono_b {EV} {mi ms : mod_trans EV} σi σs n κs b:
  σi ⪯{mi, ms, n, b, κs} σs →
  σi ⪯{mi, ms, n, true, κs} σs.
Proof. move => Hsim Hn ??. apply: Hsim. destruct b => //. by apply o_lt_impl_le. Qed.

Lemma tsim_mono_b_false {EV} {mi ms : mod_trans EV} σi σs n κs b:
  σi ⪯{mi, ms, n, false, κs} σs →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof. move => Hsim Hn ??. apply: Hsim. destruct b => //. by apply o_lt_impl_le. Qed.

Definition Plater (P : bool → Prop) : Prop :=
  P true → P false.
Arguments Plater _ /.

Lemma tsim_remember' {EV} {mi ms : mod_trans EV} (Pσ : _ → _ → _ → Prop) σi σs b n :
  (∀ n', oS?b n' ⊆ n → Pσ n' σi σs) →
  (∀ n', oS?b n' ⊆ n →
         (∀ n'' σi σs, n'' ⊆ n' → (∀ n''', oS n''' ⊆ n'' → Pσ n''' σi σs) → σi ⪯{mi, ms, n'', true} σs) →
         (∀ σi σs, Pσ n' σi σs → σi ⪯{mi, ms, n', false} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP Hsim κs' n' Hn Ht /=. exploit HP; [done|] => {}HP.
  elim/o_lt_ind: n' κs' σi σs Hn HP Ht.
  move => n' IHn κs' σi σs Hn HP Ht.
  apply: Hsim; [done| |done| |done]. 2: done.
  move => ???? HP'???? /=. eapply IHn; [by etrans| | |done].
  - etrans; [|done]. apply oS_maybe_mono; [done|]. etrans; [|done]. etrans; [|done]. apply o_le_S.
  - apply: HP'. by etrans.
Qed.

(* Induction principle *)
Lemma tsim_remember {EV} {mi ms : mod_trans EV} (Pσ : _ → _ → _ → Prop) σi σs b n :
  Pσ n σi σs →
  (∀ n n' σi σs, oS?b n' ⊆ n → Pσ n σi σs → Pσ n' σi σs) →
  (∀ n', oS?b n' ⊆ n →
         (∀ n'' σi σs, n'' ⊆ n' → Pσ n'' σi σs → σi ⪯{mi, ms, n'', true} σs) →
         (∀ σi σs, Pσ n' σi σs → σi ⪯{mi, ms, n', false} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => ? HPmono Hsim. apply: (tsim_remember' (Pσ)). { naive_solver. }
  move => ?? Hrec ???. apply Hsim; [done| |done].
  move => ?????. apply: Hrec; [done|]. move => n3 ?. apply: HPmono; [|done]. etrans; [|done].
  change (oS n3) with (oS?true n3). by apply oS_maybe_mono.
Qed.

Lemma tsim_remember_all {EV A} {mi ms : mod_trans EV} σi σs b n:
  (∀ n', oS?b n' ⊆ n → Plater (λ b', ∀ x, σi x ⪯{mi, ms, n', b'} σs x)) →
  ∀ x : A, σi x ⪯{mi, ms, n, b} σs x.
Proof.
  move => Hsim x. apply: (tsim_remember (λ _ σi' σs', ∃ x, σi' = σi x ∧ σs' = σs x)).
  all: naive_solver.
Qed.

Inductive tsim_remember_call_stack {EV} (n : ordinal) (mi ms : mod_trans EV)
          (R : nat → bool → _ → _ → Prop) (RR : mi.(m_state) → ms.(m_state) → _ → _ → Prop) :
  nat → mi.(m_state) → ms.(m_state) → Prop :=
| IPSNil σi σs :
  tsim_remember_call_stack n mi ms R RR 0 σi σs
| IPSStep d σi0 σs0 σi1 σs1:
  tsim_remember_call_stack n mi ms R RR d σi0 σs0 →
  (∀ σi2 σs2 σi3 σs3,
      R (S d) true (σi1, σs1) (σi2, σs2) →
      RR σi2 σs2 σi3 σs3 →
      σi3 ⪯{mi, ms, n, true} σs3) →
  tsim_remember_call_stack n mi ms R RR (S d) σi1 σs1
.

Lemma tsim_remember_call_stack_mono EV mi ms n n' R RR d σi σs:
  tsim_remember_call_stack n mi ms R RR d σi σs →
  n' ⊆ n →
  tsim_remember_call_stack (EV:=EV) n' mi ms R RR d σi σs.
Proof.
  move => Hs. elim: Hs n'; [by econs|].
  move => ?????? IH Hsim ??. econs; [naive_solver|] => *.
  apply: tsim_mono; [|done].
  by apply: Hsim.
Qed.

Lemma tsim_remember_call_stack_mono_R EV mi ms n R RR σi σs σi' σs' d `{!Transitive (R d true)}:
  tsim_remember_call_stack n mi ms R RR d σi σs →
  R d true (σi, σs) (σi', σs') →
  tsim_remember_call_stack (EV:=EV) n mi ms R RR d σi' σs'.
Proof.
  move => Hs. elim: Hs σi' σs' Transitive0; [by econs|].
  move => ?????? IH Hcont σi' σs' ??. econs; [naive_solver|] => *.
  apply: Hcont; [|done]. by etrans.
Qed.

Lemma tsim_remember_call {EV} (mi ms : mod_trans EV) R `{!∀ d b, Transitive (R d b)} σi0 σs0 (RR : _ → _ → _ → _ → Prop) b n0:
  (* d: stack depth *)
  (* R true: public transition relation, R false: private transition relation *)
  (∀ d σi σs σi' σs', R d true (σi, σs) (σi', σs') → R d false (σi, σs) (σi', σs')) →
  R 0%nat false (σi0, σs0) (σi0, σs0) →
  (∀ n σi1 σs1 d,
      oS?b n ⊆ n0 →
      R d false (σi0, σs0) (σi1, σs1) →
      (* Stay *)
      (∀ n' σi2 σs2,
         n' ⊆ n →
         R d true (σi1, σs1) (σi2, σs2) →
          σi2 ⪯{mi, ms, n', true} σs2 ) →
      (* Call *)
      (∀ n' σi2 σs2,
         n' ⊆ n →
         (* TODO: can we require something weaker here (not starting
         from 0) that exploits transitivity of R? *)
         R (S d) false (σi0, σs0) (σi2, σs2) →
         (∀ σi3 σs3 σi4 σs4,
             R (S d) true (σi2, σs2) (σi3, σs3) →
             RR σi3 σs3 σi4 σs4 →
             σi4 ⪯{mi, ms, n', true} σs4
         ) →
         σi2 ⪯{mi, ms, n', true} σs2) →
      (* Return *)
      (∀ n' σi2 σs2,
         n' ⊆ n →
         d ≠ 0%nat →
         R d true (σi1, σs1) (σi1, σs1) →
         RR σi1 σs1 σi2 σs2 →
          σi2 ⪯{mi, ms, n', true} σs2 ) →
      σi1 ⪯{mi, ms, n, false} σs1) →
  σi0 ⪯{mi, ms, n0, b} σs0.
Proof.
  move => HR ? Hcall.
  unshelve apply: tsim_remember. { simpl. exact (λ n σi σs,
      ∃ d,
      R d false (σi0, σs0) (σi, σs)
      ∧ tsim_remember_call_stack n mi ms R RR d σi σs
). }
  { split!. done. econs. } {
    move => ? n' ?? /=??. destruct!. split!; [done|].
    apply: tsim_remember_call_stack_mono; [done|]. etrans; [|done].
    apply o_le_S_maybe.
  }
  move => n ? /= Hloop σi1 σs1 ?. destruct!.
  apply: Hcall; [done..| | |].
  - move => ?????. apply Hloop; [done|]. split!. { etrans; [done|]. naive_solver. }
    apply: tsim_remember_call_stack_mono; [|done].
    by apply: tsim_remember_call_stack_mono_R.
  - move => ??????. apply Hloop; [done|]. split!.
    2: { apply: IPSStep. by apply: tsim_remember_call_stack_mono. done. }
    done.
  - move => ???????.
    revert select (tsim_remember_call_stack _ _ _ _ _ _ _ _) => Hs. inv/= Hs.
    apply: tsim_mono; [|done].
    naive_solver.
Qed.

Lemma tsim_step_l {EV} {mi ms : mod_trans EV} σi σs n b :
  (∀ κ Pσi,
      mi.(m_step) σi κ Pσi →
      ∃ σi', Pσi σi' ∧ σi' ⪯{mi, ms, n, true, option_trace κ} σs) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => Hsim κs' n' Hn /tnhas_trace_inv Ht.
  apply: thas_trace_under_tall; [done..|] => {Ht} κs [[??]|[?[?[?[?[?[?[<- ?]]]]]]]]. { tend. }
  have [?[? {}Hsim]]:= Hsim _ _ ltac:(done).
  apply: Hsim. 2: { by eauto. }
  destruct b; (etrans; [|done]).
  - econs. apply o_lt_impl_le. etrans; [|done]. econs. by econs.
  - etrans; [|done]. econs. by econs.
    Unshelve. done.
Qed.

Lemma tsim_step_r {EV} {mi ms : mod_trans EV} σi σs n b κs κs' κs'' :
  κs = tapp κs' κs'' →
  σs ~{ ms, κs' }~>ₜ (λ σs', σi ⪯{mi, ms, n, b, κs''} σs') →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof.
  move => -> Hsim κss n' HIs Ht. rewrite -assoc_L. apply: thas_trace_trans; [done|] => ? {}Hsim.
  by apply: Hsim.
Qed.

(** * tstep *)
(* The following sadly causes more problems than it solves since
mod_trans is a dependent pair and [m.(m_state)] cannot be reduced if [m] is
opaque. *)
(* Global Hint Constants Opaque : tstep. *)
(* Global Hint Variables Opaque : tstep. *)

Class TStepI {EV} (mi : mod_trans EV) (σi : mi.(m_state)) (P : (bool → option EV → ((mi.(m_state) → Prop) → Prop) → Prop) → Prop) : Prop := {
  tstepi_proof G:
    P G →
    σi -{ mi }-> (λ b κ Pσ, ∃ b' P', G b' κ P' ∧ (b' → b) ∧ ∀ G', P' G' → ∃ σ', Pσ σ' ∧ G' σ')
}.
Global Hint Mode TStepI + + ! - : typeclass_instances.

Lemma tsim_tstep_i {EV} (mi : mod_trans EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ b' κ Pσ, Pσ (λ σi', σi' ⪯{mi, ms, n, b' || b, option_trace κ} σs)) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn /= Hi.
  opose proof* @steps_impl_elim_n as Hd. 2: done. { by apply: tstepi_proof. }
  apply: thas_trace_under_tall; [done..|] => {Hi HP Hd} {}κs /= [?|]. { tend. }
  move => [?[?[?[?[?[[b'[? [HP [? HG']]]][<-[??]]]]]]]]. move: HP => /HG'[?[? Hs]].
  apply: Hs. 2: naive_solver.
  etrans; [|done]. rewrite orb_comm. etrans; [ apply oS_maybe_orb|]. apply oS_maybe_mono; [done|].
  etrans; [|done]. by apply oS_maybe_mono.
Qed.

Lemma tsim_tstep_both {EV} (mi : mod_trans EV) σi P `{!TStepI mi σi P} ms σs n b:
  P (λ b' κ Pσ, σs ~{ms, option_trace κ}~>ₜ (λ σs', Pσ (λ σi', σi' ⪯{mi, ms, n, b' || b, tnil} σs'))) →
  σi ⪯{mi, ms, n, b} σs.
Proof.
  move => HP κs n' Hn Hi /=.
  opose proof* @steps_impl_elim_n as Hd. 2: done. { by apply: tstepi_proof. }
  apply: thas_trace_under_tall; [done..|] => {Hi HP Hd} {}κs /= [?|]. { tend. }
  move => [?[?[?[?[?[[?[?[?[? HG']]]][<-[??]]]]]]]].
  apply: thas_trace_trans; [done|] => ? /HG' [σi' [? {}Ht]].
  apply: Ht; [|naive_solver].
  etrans; [|done]. rewrite orb_comm. etrans; [ apply oS_maybe_orb|]. apply oS_maybe_mono; [done|].
  etrans; [|done]. by apply oS_maybe_mono.
Qed.

Class TStepS {EV} (ms : mod_trans EV) (σs : ms.(m_state)) (P : (option EV → ((ms.(m_state) → Prop) → Prop) → Prop) → Prop) : Prop := {
  tsteps_proof G:
    P G →
    ∃ κ P',
      G κ P' ∧
      ∀ G', P' G' → σs -{ ms, κ }->ₛ G'
}.
Global Hint Mode TStepS + + ! - : typeclass_instances.

Lemma tsim_tstep_s {EV} (ms : mod_trans EV) σs κs P `{!TStepS ms σs P} mi σi n b :
  P (λ κ P',
      if κ is Some e then
        if κs is tcons e' κs' then e = e' ∧ P' (λ σs', σi ⪯{mi, ms, n, b, κs'} σs') else False
      else
        P' (λ σs', σi ⪯{mi, ms, n, b, κs} σs')) →
  σi ⪯{mi, ms, n, b, κs} σs.
Proof.
  move: TStepS0 => [] /[apply] -[κ [?[? HG']]] ????.
  repeat case_match => //; destruct!.
  - apply: (thas_trace_trans (tcons _ tnil)); simplify_eq/=.
    { apply (steps_spec_has_trace' _ (Some _)); naive_solver. }
    naive_solver.
  - apply: (thas_trace_trans tnil); simplify_eq/=.
    { apply (steps_spec_has_trace' _ None); naive_solver. }
    naive_solver.
Qed.

Lemma thas_trace_tstep_s {EV} (m : mod_trans EV) σ κs Pσ `{!TStepS m σ P} :
  P (λ κ P',
      if κ is Some e then
        ∃ κs', tcons e κs' ⊆ κs ∧ P' (λ σ', σ' ~{m, κs'}~>ₜ Pσ)
      else
        P' (λ σ', σ' ~{m, κs}~>ₜ Pσ)
  ) →
  σ ~{m, κs}~>ₜ Pσ.
Proof.
  move: TStepS0 => [] /[apply] -[κ [?[? HG']]].
  case_match; destruct!.
  - revert select (_ ⊆ _) => <-.
    apply: (thas_trace_trans (tcons _ tnil)); simplify_eq/=.
    { apply (steps_spec_has_trace' _ (Some _)); naive_solver. }
    naive_solver.
  - apply: (thas_trace_trans tnil); simplify_eq/=.
    { apply (steps_spec_has_trace' _ None); naive_solver. }
    naive_solver.
Qed.

Lemma steps_spec_tstep_s {EV} (m : mod_trans EV) σ κ Pσ `{!TStepS m σ P} :
  P (λ κ' P', κ = κ' ∧ P' Pσ) →
  σ -{m, κ}->ₛ Pσ.
Proof. move: TStepS0 => [] /[apply] -[?[?[[? HP] HG']]]. subst. move: HP => /HG'. done. Qed.

Lemma steps_impl_tstep_i {EV} (m : mod_trans EV) σ (Pσ : _ → _ → _ → Prop) `{!TStepI m σ P} :
  P (λ b κ' P', ∀ (b' : bool) (Pσ' : _ → Prop), (b → b') → P' (λ σ', Pσ' σ' → Pσ b' κ' Pσ')) →
  σ -{m}-> Pσ.
Proof.
  move: TStepI0 => [] /[apply]?. apply: steps_impl_mono; [done|] => ??? [?[?[HP[? HG']]]].
  naive_solver.
Qed.

Ltac eauto_tstep :=
  solve [typeclasses eauto with typeclass_instances].

Ltac tstep_s :=
  first [
      once (notypeclasses refine (tsim_tstep_s _ _ _ _ _ _ _ _ _); [eauto_tstep|]); simpl
    | once (notypeclasses refine (thas_trace_tstep_s _ _ _ _ _); [eauto_tstep|]); simpl
    | once (notypeclasses refine (steps_spec_tstep_s _ _ _ _ _)); [eauto_tstep|]; simpl
    ].
Ltac tstep_i :=
  first [
      once (notypeclasses refine (tsim_tstep_i _ _ _ _ _ _ _ _); [eauto_tstep|]); simpl
    | once (notypeclasses refine (steps_impl_tstep_i _ _ _ _); [eauto_tstep|]); simpl
    ].
Ltac tstep_both :=
  once (notypeclasses refine (tsim_tstep_both _ _ _ _ _ _ _ _); [eauto_tstep|]); simpl.

Lemma tstep_i_generic EV (m : mod_trans EV) σ:
  TStepI m σ (λ G, σ -{ m }-> (λ b κ Pσ, G b κ (λ G', ∃ σ', Pσ σ' ∧ G' σ'))).
Proof. constructor => ? HG. apply: steps_impl_mono; [done|]. naive_solver. Qed.
Global Hint Resolve tstep_i_generic | 1000 : typeclass_instances.

Lemma tstep_s_generic EV (m : mod_trans EV) σ:
  TStepS m σ (λ G, ∃ κ, G κ (λ G', σ -{m, κ}->ₛ G')).
Proof. constructor => ? [??]. eexists _, _. split; [done|]. done. Qed.
Global Hint Resolve tstep_s_generic | 1000 : typeclass_instances.

(** * tsim mirror *)

Lemma tsim_mirror {EV1 EV2} (m : mod_trans EV1) (σ : m.(m_state)) (fm1 : mod_trans EV1 → mod_trans EV2) fm2 fσ1 fσ2 n b  :
  (∀ σ n',
      oS?b n' ⊆ n →
      (∀ (P : _ → _ → _ → Prop),
          (∀ κ Pσ, m_step m σ κ Pσ → (∀ σ', fσ1 σ' ⪯{fm1 m, fm2 m, n', true} fσ2 σ') → P true κ Pσ) →
            σ -{ m }-> P) →
      fσ1 σ ⪯{fm1 m, fm2 m, n', false} fσ2 σ) →

  fσ1 σ ⪯{fm1 m, fm2 m, n, b} fσ2 σ.
Proof.
  move => Hσ.
  unshelve apply: tsim_remember. { exact: (λ _ σ1 σ2, ∃ σ', σ1 = fσ1 σ' ∧ σ2 = fσ2 σ'). }
  { by split!. } { done. }
  move => n1 /= ? IH ???. destruct!.
  apply Hσ; [done|].
  move => P Hcont.
  apply steps_impl_step_end => κ Pσ2 ?.
  naive_solver.
Qed.

Lemma tsim_mirror_s {EV1 EV2} (m : mod_trans EV1) (σ : m.(m_state)) (fm1 : mod_trans EV1 → mod_trans EV2) fm2 fσ1 fσ2 n (Pσ : m.(m_state) → Prop) :
  m_step m σ None Pσ →
  (∀ σ', fσ1 σ' ⪯{fm1 m, fm2 m, n, true} fσ2 σ') →
  σ -{ m, None }->ₛ (λ σ2', (fσ2 σ2') ~{ fm2 m, tnil }~>ₜ (λ σ2'',
                      ∃ σ1', Pσ σ1' ∧ fσ1 σ1' ⪯{fm1 m, fm2 m, n, true} σ2'')).
Proof. move => ??. apply: steps_spec_step_end; [done|]. move => ??. tend. split!; naive_solver. Qed.

Ltac tsim_mirror m σ :=
  lazymatch goal with
  | |- ?σ1 ⪯{?m1, ?m2, _, _} ?σ2 =>
  let x := fresh "x" in
  lazymatch m1 with | context C [m] =>
  let fm1 := constr:(λ x, ltac:(let y := context C [x] in exact y)) in
  lazymatch m2 with | context C [m] =>
  let fm2 := constr:(λ x, ltac:(let y := context C [x] in exact y)) in
  lazymatch σ1 with | context C [σ] =>
  let fσ1 := constr:(λ x, ltac:(let y := context C [x] in exact y)) in
  lazymatch σ2 with | context C [σ] =>
  let fσ2 := constr:(λ x, ltac:(let y := context C [x] in exact y)) in
  (* idtac fm1 fm2 fσ1 fσ2 *)
  apply (tsim_mirror m σ fm1 fm2 fσ1 fσ2);
  let σ' := fresh "σ'" in
  let n := fresh "n" in
  let Hn := fresh "Hn" in
  let Hcont := fresh "Hcont" in
  intros σ' n Hn Hcont;
  tstep_both;
  apply Hcont; clear Hcont;
  case; last first; [
    let Pσ := fresh "Pσ" in
    let Hstep := fresh "Hstep" in
    let Hloop := fresh "Hloop" in
    let Hend := fresh "Hend" in
    intros Pσ Hstep Hloop;
    pose proof (tsim_mirror_s m _ fm1 fm2 fσ1 fσ2 n Pσ Hstep Hloop) as Hend;
    clear Hstep Hloop
  | let e := fresh "e" in
    let Pσ := fresh "Pσ" in
    let Hstep := fresh "Hstep" in
    intros e Pσ Hstep _; revert σ' n Hn e Pσ Hstep]
      end end end end
  end.


(** * proving a refinement based on another refinement *)

Lemma forall_to_ex1 A B (P1 : A → Prop)  P2 (Q : B → Prop):
 (∃ n : A, P1 n ∧ (∀ y, P2 n y → Q y)) -> (∀ y, (∀ n : A, P1 n → P2 n y) → Q y).
Proof. naive_solver. Qed.

(** Exploration of a proof technique that is more complete than other ones: *)
Lemma trefines_implies_trefines {EV} (m1 m2 : module EV):
  trefines m1 m2 → trefines m1 m2.
Proof.
  move => [/=Hr]. constructor => κs Ht.
  move: Hr. move: (m_init m1) (m_init m2) Ht => σ1 σ2 Ht.
  move: σ2. apply: forall_to_ex1.
  elim: Ht.
  - move => ?????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ??. by apply: TTraceEnd.
  - move => ??? κ ?? Hstep ? IH ?.
    have [f Hf]:= AxChoice1 IH.
    eexists (tapp (option_trace κ) (tex _ f)). split.
    + apply: TTraceStep; [done| |done]. move => ??. apply: thas_trace_ex. by apply Hf.
    + move => σ2. destruct κ; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _) Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [?[? {}Ht]].
        apply: thas_trace_mono; [|done|done].
        apply: TTraceStep; [done | |simpl; done]. move => ??.
        have /thas_trace_ex_inv{}Ht := Ht _ ltac:(done).
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done| ]. naive_solver. done.
      * move => /thas_trace_ex_inv Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done|done]. naive_solver.
  - move => ?????? IH ?.
    have [fx Hfx]:= AxChoice _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. done.
Qed.

Lemma forall_to_ex2 A B1 B2 (P1 : A → Prop)  P2 (Q : B1 → B2 → Prop) R:
 (∃ n : A, P1 n ∧ (∀ y1 y2, R y1 y2 → P2 n y1 y2 → Q y1 y2)) -> (∀ y1 y2, R y1 y2 → (∀ n : A, P1 n → P2 n y1 y2) → Q y1 y2).
Proof. naive_solver. Qed.

Lemma trefines1_implies_trefines2 {EV1 EV2} (mi1 ms1 : module EV1) (mi2 ms2 : module EV2)
      (iinv : mi1.(m_trans).(m_state) → mi2.(m_trans).(m_state) → Prop)
      (sinv : ms1.(m_trans).(m_state) → ms2.(m_trans).(m_state) → Prop):
  trefines mi1 ms1 →
  iinv mi1.(m_init) mi2.(m_init) →
  sinv ms1.(m_init) ms2.(m_init) →
  (∀ σ1 σ2 κ Pσ2, iinv σ1 σ2 → m_step mi2.(m_trans) σ2 κ Pσ2 → ∃ κ',
    (if κ' is Some e then
       ∀ σs1 σs2 Pσs1, sinv σs1 σs2 → m_step ms1.(m_trans) σs1 κ' Pσs1 →
          σs2 ~{ ms2.(m_trans), option_trace κ }~>ₜ (λ σs2', ∃ σs1', Pσs1 σs1' ∧ sinv σs1' σs2')
     else κ = None) ∧
       σ1 ~{ mi1.(m_trans), option_trace κ' }~>ₜ (λ σ1', ∃ σ2', Pσ2 σ2' ∧ iinv σ1' σ2')) →
  (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → m_step ms1.(m_trans) σ1 None Pσ1 →
                σ2 ~{ ms2.(m_trans), tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')) →
  trefines mi2 ms2.
Proof.
  move => [/=Hr] Hiinvinit Hsinvinit Histep Hsnil.
  have {}Hsnil: (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → σ1 ~{ ms1.(m_trans), tnil }~>ₜ Pσ1 →
                σ2 ~{ ms2.(m_trans), tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')). {
    clear -Hsnil.
    move => σ1 σ2 Pσ1 Hsinv /thas_trace_nil_inv.
    have : @tnil EV1 ⊆ tnil by done. move: {1 3}(@tnil EV1) => κs Hκs Ht.
    elim: Ht σ2 Hsinv Hκs.
    - move => ????????. apply: TTraceEnd; naive_solver.
    - move => ??? κ ?? Hstep ? IH Hs1 ?? Hs2.
      pose proof (transitivity Hs1 Hs2) as Hs. destruct κ; simplify_eq/=; [easy| ].
      move: Hstep => /Hsnil {}Hstep.
      apply: (thas_trace_trans tnil); naive_solver.
  }
  constructor => κs Ht. move: Hiinvinit Hsinvinit Hr.
  move: (m_init mi1) (m_init mi2) (m_init ms1) (m_init ms2) Ht => σi1 σi2 σs1 σs2 Ht Hiinit Hsinit.
  move: σs1 σs2 Hsinit. apply: forall_to_ex2.
  elim: Ht σi1 Hiinit.
  - move => ???????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ????. by apply: TTraceEnd.
  - move => ? Pσ2 ? κ ? κs' Hstep ? IH ? ? Hiinv.
    have [κ' [Hsend Hsteps]]:= Histep _ _ _ _ Hiinv Hstep.
    have {}IH : ∀ σi1, (∃ σ2', Pσ2 σ2' ∧ iinv σi1 σ2') → ∃ n, σi1 ~{ mi1.(m_trans), n }~>ₜ (λ _, True) ∧
       (∀ y1 y2, sinv y1 y2 → y1 ~{ ms1.(m_trans), n }~>ₜ (λ _, True) → y2 ~{ ms2.(m_trans), κs' }~>ₜ (λ _, True)).
    { move => ?. naive_solver. }
    have [f Hf]:= AxChoice1 IH.
    eexists (tapp (option_trace κ') (tex _ f)). split.
    + apply: thas_trace_trans; [done| ] => ?[?[??]].
      apply: thas_trace_ex. by apply Hf.
    + move => σs1 σs2 ? /thas_trace_app_inv Happ.
      apply: (thas_trace_mono _ _ (λ _, True)); [|done|done].
      move: Happ. destruct κ'; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _)/Hsnil Ht.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => {Ht} ? [? [[?[? HP]]?]].
        apply: thas_trace_trans; [naive_solver|].
        move => ?[?[??]].
        have /Hsnil ?:= HP _ ltac:(done).
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[/thas_trace_ex_inv/Hsnil??]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ?[?[[[?[?[??]]]?]?]].
        naive_solver.
      * move => /Hsnil Hs.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [? [/thas_trace_ex_inv/Hsnil? ?]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[[[?[?[??]]]?]?]]. naive_solver.
  - move => ?????? IH ???.
    have {}IH := (IH _ _ ltac:(done)).
    have [fx Hfx]:= AxChoice _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ??? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. all: naive_solver.
Qed.
