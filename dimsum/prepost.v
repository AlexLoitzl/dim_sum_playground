From dimsum.core Require Export proof_techniques satisfiable seq_product.
From dimsum.core Require Import link.
From dimsum.core Require Import axioms.
From dimsum.core.iris Require Import weak_embed sat.

Set Default Proof Using "Type".

(** * Prepost *)

(** * [prepost] *)
Section prepost.
Context {R : Type}.
Context {M : ucmra}.


Inductive prepost : Type :=
| pp_end (r : R)
| pp_prop (P : Prop) (pp : prepost)
| pp_quant {T} (pp : T → prepost)
| pp_star (P : uPred M) (pp : prepost)
.

Fixpoint pp_to_ex (pp : prepost) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r True%I
  | pp_prop P pp' => P ∧ pp_to_ex pp' Q
  | pp_quant pp' => ∃ y, pp_to_ex (pp' y) Q
  | pp_star P pp' => pp_to_ex pp' (λ r y, Q r (P ∗ y)%I)
  end.

Fixpoint pp_to_all (pp : prepost) (Q : R → uPred M → Prop) : Prop :=
  match pp with
  | pp_end r => Q r True%I
  | pp_prop P pp' => P → pp_to_all pp' Q
  | pp_quant pp' => ∀ y, pp_to_all (pp' y) Q
  | pp_star P pp' => pp_to_all pp' (λ r y, Q r (P ∗ y)%I)
  end.

Lemma pp_to_ex_exists pp Q:
  pp_to_ex pp Q ↔ ∃ r y, Q r y ∧ pp_to_ex pp (λ r' y', r' = r ∧ y' = y).
Proof.
  elim: pp Q => /=; try naive_solver.
  move => ?? IH Q. rewrite IH.
  split; move => [?[?[? Hex]]].
  - eexists _, _. split; [done|]. rewrite IH. naive_solver.
  - move: Hex. rewrite IH. naive_solver.
Qed.

Lemma pp_to_all_forall pp Q:
  pp_to_all pp Q ↔ (∀ r y, pp_to_ex pp (λ r' y', r' = r ∧ y' = y) → Q r y).
Proof.
  elim: pp Q => /=; try naive_solver.
  move => ?? IH Q. rewrite IH.
  split; move => Hall ??.
  - rewrite pp_to_ex_exists => -[?[?[??]]]. naive_solver.
  - move => ?. apply Hall. rewrite pp_to_ex_exists. naive_solver.
Qed.

Lemma pp_to_all_forall_2 pp Q:
  pp_to_all pp Q →
  ∀ r y, pp_to_ex pp (λ r' y', r' = r ∧ y' = y) → Q r y.
Proof. apply pp_to_all_forall. Qed.

Lemma pp_to_all_mono pp (Q1 Q2 : _ → _ → Prop):
  pp_to_all pp Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_all pp Q2.
Proof. rewrite !pp_to_all_forall. naive_solver. Qed.

Lemma pp_to_ex_mono pp (Q1 Q2 : _ → _ → Prop):
  pp_to_ex pp Q1 →
  (∀ r y, Q1 r y → Q2 r y) →
  pp_to_ex pp Q2.
Proof. rewrite !pp_to_ex_exists. naive_solver. Qed.

Lemma pp_to_all_ex pp Q1 Q2:
  pp_to_all pp Q1 →
  pp_to_ex pp Q2 →
  ∃ y r, Q1 r y ∧ Q2 r y.
Proof. move => /pp_to_all_forall ? /pp_to_ex_exists. naive_solver. Qed.


Fixpoint pp_to_ex_bi {PROP : bi} (W : BiWeakEmbed (uPredI M) PROP)
  (pp : prepost) (Q : R → PROP) : PROP :=
  match pp with
  | pp_end r => Q r
  | pp_prop P pp' => ⌜P⌝ ∗ pp_to_ex_bi W pp' Q
  | pp_quant pp' => ∃ y, pp_to_ex_bi W (pp' y) Q
  | pp_star P pp' => ⌈P @ W⌉ ∗ pp_to_ex_bi W pp' Q
  end.

Lemma pp_to_ex_bi_to_ex {PROP : bi} (W : BiWeakEmbed (uPredI M) PROP)
  (pp : prepost) Q `{!BiAffine PROP}:
  pp_to_ex_bi W pp Q -∗
  ∃ r y, ⌜pp_to_ex pp (λ r' y', r = r' ∧ y = y')⌝ ∗ ⌈y @ W⌉ ∗ Q r.
Proof.
  iIntros "Hp". iInduction pp as [] "IH" => /=.
  - iFrame. iSplit!.
  - iDestruct "Hp" as (?) "Hp". iDestruct ("IH" with "Hp") as (???) "$". iSplit!.
  - iDestruct "Hp" as (?) "Hp". iDestruct ("IH" with "Hp") as (???) "$". by iSplit!.
  - iDestruct "Hp" as "[? Hp]". iDestruct ("IH" with "Hp") as (???) "[??]".
    iExists _, _. iSplit!.
    { apply: pp_to_ex_mono; [done|]. move => ?? /= [<- <-]. done. }
    iFrame.
Qed.

End prepost.

Arguments prepost : clear implicits.

(** * Shrinking of types *)
Class Shrink (X : TypeOfe) := MkShrink {
  small_car : TypeBelowState;
  type_to_small : X → small_car;
  small_to_type : small_car → X;
  type_to_small_bij x : type_to_small (small_to_type x) = x;
  small_to_type_bij x : small_to_type (type_to_small x) = x;
}.
Arguments small_car _ {_}.
Arguments type_to_small _ {_} _.
Arguments small_to_type _ {_} _.
Arguments type_to_small_bij _ {_} _.
Arguments small_to_type_bij _ {_} _.

Global Hint Mode Shrink + : typeclass_instances.

Create HintDb shrink_db discriminated.
Hint Constants Transparent : shrink_db.
Ltac solve_shrink_direct :=
  lazy; refine (MkShrink _ _ (λ x, x) (λ x, x) (λ x, eq_refl) (λ x, eq_refl)).
Hint Extern 100 (Shrink _) => solve_shrink_direct : shrink_db.
(** solve_shrink_direct can be very slow so it should not be triggered
by normal typeclass search, only by solve_shrink *)
Ltac solve_shrink := typeclasses eauto with typeclass_instances shrink_db.

Global Instance unitUR_shrink : Shrink unitUR.
Proof. solve_shrink. Qed.

Global Instance prod_shrink (x y : Type) `{!Shrink x} `{!Shrink y} : Shrink (prod x y).
Proof.
  refine (MkShrink _ (small_car x * small_car y)
            (λ v, (type_to_small x v.1, type_to_small y v.2))
            (λ v, (small_to_type x v.1, small_to_type y v.2)) _ _) => -[??] /=.
  - by rewrite !type_to_small_bij.
  - by rewrite !small_to_type_bij.
Qed.

(** * [uPred_small] *)
Record uPred_small (M : ucmra) `{!Shrink M} : TypeBelowState := UPred_small {
  uPred_small_holds : nat → (small_car M) → Prop;

  uPred_small_mono n1 n2 x1 x2 :
    uPred_small_holds n1 x1 → small_to_type M x1 ≼{n2} small_to_type M x2 → n2 ≤ n1 → uPred_small_holds n2 x2
}.
Arguments uPred_small_holds {_ _} _ _ _.
Add Printing Constructor uPred_small.

Program Definition uPred_shrink {M : ucmra} `{!Shrink M} (P : uPred M) : uPred_small M :=
 let '(UPred _ P HP) := P in
 {|
   uPred_small_holds n x := P n (small_to_type M x);
|}.
Next Obligation. move => M s ? P HP n1 n2 x1 x2 /=. apply HP. Qed.

Program Definition uPred_expand {M : ucmra} `{!Shrink M} (P : uPred_small M) : uPred M := {|
   uPred_holds n x := uPred_small_holds P n (type_to_small M x);
|}.
Next Obligation.
  move => M s P n1 n2 x1 x2 /=.
  have <- := small_to_type_bij M x1. have <- := small_to_type_bij M x2.
  rewrite !type_to_small_bij. apply uPred_small_mono.
Qed.

Lemma uPred_eq {M : ucmra} (x1 x2 : uPred M) :
  x1 = x2 ↔ ∀ n r, uPred_holds x1 n r = uPred_holds x2 n r.
Proof.
  split; [naive_solver|]. move => Heq.
  destruct x1 as [P1 HP1], x2 as [P2 HP2]; simpl in *.
  have ? : P1 = P2. { by do 2 apply AxFunctionalExtensionality => ?. }
  subst. f_equal. apply AxProofIrrelevance.
Qed.

Lemma uPred_expand_shrink {M : ucmra} `{!Shrink M} (x : uPred M) :
  uPred_expand (uPred_shrink x) = x.
Proof.
  apply uPred_eq => ??.
  destruct x as [P HP] => //=.
  rewrite /uPred_expand/uPred_shrink/=/uPred_holds/=.
  by rewrite small_to_type_bij.
Qed.

Global Instance uPred_shrink_inj (M : ucmra) `{!Shrink M} : Inj (=) (=) (uPred_shrink (M:=M)).
Proof.
  move => x y Hxy.
  by rewrite -(uPred_expand_shrink x) -(uPred_expand_shrink y) Hxy.
Qed.

(** * [mod_prepost] *)
Section prepost.
  Context {EV1 EV2 S : Type}.
  Context {M : ucmra} `{!Shrink M}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S) M) (o : EV1 → S → prepost (EV2 * S) M).

  Inductive pp_case : Type :=
  | PPOutside
  | PPRecv1 (e : EV2)
  | PPRecv2 (e : EV1)
  | PPInside
  | PPSend1 (e : EV1)
  | PPSend2 (e : EV2)
  .

  Inductive pp_filter_step i o :
    (pp_case * S * uPred_small M) → option (sm_event EV1 EV2) → ((pp_case * S * uPred_small M) → Prop) → Prop :=
  | PPOutsideS s x e:
    (* TODO: Add a user-defined predicate here to rule out choosing
    non-sensical events? E.g. allow only Incoming events or prevent
    syscall events. *)
    pp_filter_step i o (PPOutside, s, x) (Some (SMEEmit e)) (λ σ, σ = (PPRecv1 e, s, x))
  | PPRecv1S s x e:
    pp_filter_step i o (PPRecv1 e, s, x) None (λ σ,
        pp_to_ex (i e s) (λ r y, ∃ x', satisfiable (uPred_expand x ∗ y ∗ x') ∧ σ = (PPRecv2 r.1, r.2, uPred_shrink x')))
  | PPRecv2S s x e:
    pp_filter_step i o (PPRecv2 e, s, x) (Some (SMEReturn (Some e))) (λ σ, σ = (PPInside, s, x))
  | PPInsideS s x e:
    pp_filter_step i o (PPInside, s, x) (Some (SMERecv e)) (λ σ, σ = (PPSend1 e, s, x))
  | PPSend1S s x e r y x':
    satisfiable (x' ∗ y ∗ uPred_expand x) →
    pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y) →
    pp_filter_step i o (PPSend1 e, s, x) None (λ σ, σ = (PPSend2 r.1, r.2, uPred_shrink x'))
  | PPSend2S s x e:
    pp_filter_step i o (PPSend2 e, s, x) (Some (SMEEmit e)) (λ σ, σ = (PPOutside, s, x))
  .

  Definition prepost_filter_trans i o := ModTrans (pp_filter_step i o).

  Global Instance prepost_filter_vis_no_all i o : VisNoAng (prepost_filter_trans i o).
  Proof. move => ????. inv_all @m_step; naive_solver. Qed.

  Definition prepost_trans i o (m : mod_trans EV1) : mod_trans EV2 :=
    seq_map_trans m (prepost_filter_trans i o).

  Global Instance prepost_vis_no_all i o m `{!VisNoAng m}: VisNoAng (prepost_trans i o m).
  Proof. apply _. Qed.

  (* If one needs a version of prepost_mod that starts on the inside,
  one can define prepost_mod_inside or similar. *)
  Definition prepost_mod i o (m : module EV1) (s : S) (x : uPred M) : module EV2 :=
    Mod (prepost_trans i o m.(m_trans)) (SMFilter, m.(m_init), (PPOutside, s, uPred_shrink x)).

  Lemma prepost_mod_trefines i o (m m' : module EV1) σm s `{!VisNoAng m.(m_trans)}:
    trefines m m' →
    trefines (prepost_mod i o m σm s) (prepost_mod i o m' σm s).
  Proof.
    move => ?. apply: (seq_map_mod_trefines (Mod _ _) (Mod _ _) (Mod _ _)). destruct m, m' => //.
  Qed.

  Lemma prepost_trans_step_Outside_i i o m σ s x:
    TStepI (prepost_trans i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∀ e, G true (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= ?. tstep_i.
    apply steps_impl_step_end => ???. inv_all @m_step => ???. split! => ?. split!; [naive_solver|done|].
    naive_solver.
  Qed.

  Lemma prepost_trans_step_Recv1_i i o m σ s e x:
    TStepI (prepost_trans i o m) (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) (λ G,
        pp_to_ex (i e s) (λ r y, ∃ x', satisfiable (x ∗ y ∗ x') ∧
                      G true None (λ G', G' (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x'))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[r [? [[?[? HG]]?]]]. tstep_i.
    apply steps_impl_step_next => ???. inv_all @m_step.
    eexists (_, _). split!. {
      apply pp_to_ex_exists. setoid_rewrite uPred_expand_shrink. naive_solver. }
    apply steps_impl_step_end => ???. inv_all @m_step => ???. naive_solver.
  Qed.

  Lemma prepost_trans_step_Inside_i i o m σ s e x:
    TStepI (prepost_trans i o m) (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) (λ G,
        pp_to_all (o e s) (λ r y, ∀ x', satisfiable (x' ∗ y ∗ x) →
            G true (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, uPred_shrink x'))))).
  Proof.
    constructor => G /= ?. apply steps_impl_step_trans. tstep_i.
    apply steps_impl_step_end => ???. inv_all @m_step => ? b *; simplify_eq. split! => ?. split!; [done|].
    tstep_i.
    apply steps_impl_step_next => ???. inv_all @m_step => *; simplify_eq. split!.
    apply steps_impl_step_end => ???. inv_all @m_step => *; simplify_eq. split! => ?.
    have [?[?[?[??]]]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    revert select (satisfiable _). rewrite uPred_expand_shrink => ?.
    split!; [naive_solver|by destruct b|]. naive_solver.
  Qed.

  Lemma prepost_trans_step_Outside_s i o m σ s x:
    TStepS (prepost_trans i o m) (SMFilter, σ, (PPOutside, s, x)) (λ G,
        ∃ e, G (Some e) (λ G', G' (SMFilter, σ, (PPRecv1 e, s, x)))).
  Proof.
    constructor => G /= [??]. split!; [done|] => /= ??. tstep_s. eexists (Some (SMEEmit _)). split!.
    apply: steps_spec_step_end; [by econs|]. naive_solver.
  Qed.


  Lemma prepost_trans_step_Recv1_s i o m σ s e x:
    TStepS (prepost_trans i o m) (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) (λ G,
        G None (λ G', pp_to_all (i e s) (λ r y, ∀ x', satisfiable (x ∗ y ∗ x') →
             G' (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x'))))).
  Proof.
    constructor => G /= ?. split!; [done|] => /= ??. apply steps_spec_step_trans.
    tstep_s. eexists None. split!.
    apply: steps_spec_step_end; [by econs|] => ? /=?.
    have [?[?[?[?[??]]]]]:= pp_to_all_ex _ _ _ ltac:(done) ltac:(done); subst.
    tstep_s. eexists (Some (SMEReturn _)). split!.
    rename select (satisfiable _) into Hsat. rewrite uPred_expand_shrink in Hsat.
    apply: steps_spec_step_end; [econs|]. naive_solver.
  Qed.

  Lemma prepost_trans_step_Inside_s i o m σ s e x:
    TStepS (prepost_trans i o m) (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) (λ G,
        pp_to_ex (o e s) (λ r y, ∃ x', satisfiable (x' ∗ y ∗ x) ∧
           G (Some (r.1)) (λ G', G' (SMFilter, σ, (PPOutside, r.2, uPred_shrink x'))))).
  Proof.
    constructor => G /= /pp_to_ex_exists[?[?[[?[??]]?]]]. split!; [done|] => /= ??.
    apply steps_spec_step_trans. tstep_s. eexists (Some _). split!.
    apply: steps_spec_step_end; [by econs|] => /= ? ->. tstep_s. eexists (Some (SMEEmit _)). split!.
    apply: steps_spec_step. { by econs; [by rewrite uPred_expand_shrink|]. } move => /= ? ->.
    apply: steps_spec_step_end; [by econs|] => /= ? ->.
    naive_solver.
  Qed.
End prepost.

Global Hint Resolve
       prepost_trans_step_Outside_i
       prepost_trans_step_Recv1_i
       prepost_trans_step_Inside_i
       prepost_trans_step_Outside_s
       prepost_trans_step_Recv1_s
       prepost_trans_step_Inside_s
 | 3 : typeclass_instances.

(** * Lemmas for proving refinements of prepost  *)

Definition prepost_id {EV} : EV → unit → prepost (EV * unit) unitUR :=
  λ x _, pp_end (x, tt).

Lemma prepost_id_l (M : ucmra) `{!Shrink M} S EV1 EV2 (m : module EV1) i o s x:
  trefines (prepost_mod i o
              (prepost_mod prepost_id prepost_id m tt True) s x)
           (prepost_mod (M:=M) (S:=S) (EV2:=EV2) i o m s x).
Proof.
  apply tsim_implies_trefines => /= n.
  tstep_i => ?.
  tstep_s. split!.
  tstep_s. apply pp_to_all_forall => ?????.
  tstep_i. apply: pp_to_ex_mono; [done|].
  move => ?? [? ?]. subst. eexists _. split; [done|].
  tstep_i => ? <-.
  tstep_i. eexists True%I. split. { apply satisfiable_emp_valid. by iSplit. }
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σf1, (σf1', σ1, (σpp1', _, x')), (σpp1, s1, x1)) '(σf2, σ2, (σpp2, s2, x2)),
         ∃ rx,
         x' = uPred_shrink True%I ∧ σf1 = SMProg ∧ σf1' = σf2 ∧ σ1 = σ2 ∧ σpp1 = PPInside ∧ x1 = x2 ∧ x1 = uPred_shrink rx
         ∧ σpp1' = PPInside ∧ σpp2 = PPInside ∧ s1 = s2 ∧
         ((∃ e, σf1' = SMProgRecv e) ∨ σf1' = SMProg)). }
  { split!. } { done. }
  move => {}n _ Hloop [[σf1 [[σf1' σ1] [[σpp1' []] ?]] [[σpp1 s1] x1]]] [[σf2 σ2] [[σpp2 s2] x2]] ?.
  destruct!.
  - tstep_both. apply: steps_impl_step_end => κ ??. case_match => *.
    + subst. tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply: steps_impl_step_end => κ ??.
    tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    case_match; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i => ??. tstep_i. apply pp_to_all_forall => ?????.
    tstep_s. apply: pp_to_ex_mono; [done|]. move => ?? [? ?]. split!; subst; [done..|].
    tstep_i => ?.
    tstep_s. split!.
    tstep_s. apply pp_to_all_forall => ?????.
    tstep_i. apply: pp_to_ex_mono; [done|]. move => ?? [??]; subst. split!; [done|].
    tstep_i => ? <-.
    tstep_i. split!; [done|].
    apply Hloop; [done|]. split!.
Qed.


Section prepost.

  Lemma prepost_link
        {EV1 EV2 S1 S2 S' Sr1 Sr2 : Type}
        {M : ucmra} `{!Shrink M}
        (INV : seq_product_case → S1 → S2 → S' → uPred M → uPred M → uPred M → Sr1 → Sr2 → Prop)
        (i1 : io_event EV2 → S1 → prepost (io_event EV1 * S1) M)
        (o1 : io_event EV1 → S1 → prepost (io_event EV2 * S1) M)
        (i2 : io_event EV2 → S2 → prepost (io_event EV1 * S2) M)
        (o2 : io_event EV1 → S2 → prepost (io_event EV2 * S2) M)
        (i : io_event EV2 → S' → prepost (io_event EV1 * S') M)
        (o : io_event EV1 → S' → prepost (io_event EV2 * S') M)
        (R1 : seq_product_case → Sr1 → EV2 → seq_product_case → Sr1 → EV2 → bool → Prop)
        (R2 : seq_product_case → Sr2 → EV1 → seq_product_case → Sr2 → EV1 → bool → Prop)
        (m1 m2 : module (io_event EV1))
        s1 s2 x1 x2 x sr1 sr2 s
        `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}
        :

       (∀ p s e p' s' e' ok1, R1 p s e p' s' e' ok1 → p ≠ p') →
       INV None s1 s2 s x1 x2 x sr1 sr2 →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e sr1' e' ok1,
          INV None s1 s2 s x1 x2 x sr1 sr2 →
          R1 None sr1 e (Some SPLeft) sr1' e' ok1 →
          pp_to_all (i (Incoming, e') s) (λ r1 y1,
          ∀ x', satisfiable (x ∗ y1 ∗ x') →
          ok1 ∧
          pp_to_ex (i1 (Incoming, e') s1) (λ r2 y2, ∃ e sr2' x'2 ok2,
            satisfiable (x1 ∗ y2 ∗ x'2) ∧
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 None sr2 e (Some SPLeft) sr2' r1.1.2 ok2 ∧
            (ok2 → INV (Some SPLeft) r2.2 s2 r1.2 x'2 x2 x' sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e sr1' e' ok1,
          INV None s1 s2 s x1 x2 x sr1 sr2 →
          R1 None sr1 e (Some SPRight) sr1' e' ok1 →
          pp_to_all (i (Incoming, e') s) (λ r1 y1,
          ∀ x', satisfiable (x ∗ y1 ∗ x') →
          ok1 ∧
          pp_to_ex (i2 (Incoming, e') s2) (λ r2 y2, ∃ e sr2' x'2 ok2,
            satisfiable (x2 ∗ y2 ∗ x'2) ∧
            r1.1.1 = Incoming ∧
            r2.1.1 = Incoming ∧
            r1.1.2 = r2.1.2 ∧
            R2 None sr2 e (Some SPRight) sr2' r1.1.2 ok2 ∧
            (ok2 → INV (Some SPRight) s1 r2.2 r1.2 x1 x'2 x' sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV (Some SPLeft) s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x1) →
             r1.1.1 = Outgoing →
             R1 (Some SPLeft) sr1 r1.1.2 (Some SPRight) sr1' e' ok1 →
             ok1 ∧
             pp_to_ex (i2 (Incoming, e') s2) (λ r2 y2, ∃ sr2' x'2 ok2,
               satisfiable (x2 ∗ y2 ∗ x'2) ∧
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               R2 (Some SPLeft) sr2 e.2 (Some SPRight) sr2' r2.1.2 ok2 ∧
               (ok2 → INV (Some SPRight) r1.2 r2.2 s x' x'2 x sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV (Some SPLeft) s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o1 e s1) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x1) →
             r1.1.1 = Outgoing →
             R1 (Some SPLeft) sr1 r1.1.2 None sr1' e' ok1 →
             ∃ e'' sr2' ok2,
               e.1 = Outgoing ∧
               R2 (Some SPLeft) sr2 e.2 None sr2' e'' ok2 ∧
               ok1 ∧
               (* There should not be ub when going out *)
               ok2 ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2 y2, ∃ x'2,
                 satisfiable (x'2 ∗ y2 ∗ x) ∧
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV None r1.2 s2 r2.2 x' x2 x'2 sr1' sr2'))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV (Some SPRight) s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x2) →
             r1.1.1 = Outgoing →
             R1 (Some SPRight) sr1 r1.1.2 (Some SPLeft) sr1' e' ok1 →
             ok1 ∧
             pp_to_ex (i1 (Incoming, e') s1) (λ r2 y2, ∃ sr2' x'2 ok2,
               satisfiable (x1 ∗ y2 ∗ x'2) ∧
               e.1 = Outgoing ∧
               r2.1.1 = Incoming ∧
               R2 (Some SPRight) sr2 e.2 (Some SPLeft) sr2' r2.1.2 ok2 ∧
               (ok2 → INV (Some SPLeft) r2.2 r1.2 s x'2 x' x sr1' sr2')))) →
       (∀ s1 s2 s x1 x2 x sr1 sr2 e ok1,
           INV (Some SPRight) s1 s2 s x1 x2 x sr1 sr2 →
           pp_to_all (o2 e s2) (λ r1 y1, ∀ sr1' e' x',
             satisfiable (x' ∗ y1 ∗ x2) →
             r1.1.1 = Outgoing →
             R1 (Some SPRight) sr1 r1.1.2 None sr1' e' ok1 →
             ∃ e'' sr2' ok2,
               e.1 = Outgoing ∧
               R2 (Some SPRight) sr2 e.2 None sr2' e'' ok2 ∧
               ok1 ∧
               (* There should not be ub when going out *)
               ok2 ∧
               pp_to_ex (o (Outgoing, e'') s) (λ r2 y2, ∃ x'2,
                 satisfiable (x'2 ∗ y2 ∗ x) ∧
                 r2.1.1 = Outgoing ∧
                 r2.1.2 = e' ∧
                 INV None s1 r1.2 r2.2 x1 x' x'2 sr1' sr2'))) →
    trefines (link_mod R1 (prepost_mod i1 o1 m1 s1 x1) (prepost_mod i2 o2 m2 s2 x2) sr1)
             (prepost_mod i o (link_mod R2 m1 m2 sr2) s x).
    Proof.
      move => Hneq Hinv HN2L HN2R HL2R HL2N HR2L HR2N.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σl1, sr1, (σf1, σ1, (σpp1, s1, x1)), (σf2, σ2, (σpp2, s2, x2)))
          '(σf, (σl2, sr2, σ1', σ2'), (σpp, s, x)),
           ∃ sp rx1 rx2 rx,
           x1 = uPred_shrink rx1 ∧ x2 = uPred_shrink rx2 ∧ x = uPred_shrink rx ∧
           σ1 = σ1' ∧ σ2 = σ2' ∧ INV sp s1 s2 s rx1 rx2 rx sr1 sr2 ∧
          (( sp = None ∧
              σl1 = MLFRun None ∧ σf = SMFilter
            ∧ σpp1 = PPOutside ∧ σpp2 = PPOutside ∧ σpp = PPOutside
            ∧ σf1 = SMFilter ∧ σf2 = SMFilter
            ∧ σl2 = MLFRun None)
           ∨ (sp = (Some SPLeft) ∧
              ((∃ e, σl2 = MLFRecv SPLeft e ∧ σf1 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFRun (Some SPLeft) ∧ σf1 = SMProg))
            ∧ σpp1 = PPInside ∧ σpp2 = PPOutside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf2 = SMFilter
            ∧ σl1 = MLFRun (Some SPLeft))
           ∨ (sp = (Some SPRight) ∧
              ((∃ e, σl2 = MLFRecv SPRight e ∧ σf2 = SMProgRecv (Incoming, e))
               ∨ (σl2 = MLFRun (Some SPRight) ∧ σf2 = SMProg))
            ∧ σpp1 = PPOutside ∧ σpp2 = PPInside ∧ σpp = PPInside
            ∧ σf = SMProg ∧ σf1 = SMFilter
            ∧ σl1 = MLFRun (Some SPRight)) )). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[[σl1 {}sr1] [[σf1 {}σ1] [[σpp1 {}s1] {}x1]]] [[σf2 {}σ2] [[σpp2 {}s2] {}x2]]].
      move => [[σf [[[σl2 {}sr2] σ1'] σ2']] [[σpp {}s] {}x]] ?. destruct!.
      - tstep_i => ? p' ?? ok1 ?.
        tstep_s. split!.
        tstep_s. apply pp_to_all_forall => ri xi Hi x' Hsat.
        destruct p' as [[]|] => /=. 3: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HN2L|].
          move => [[??]?] ? /= Hcont ??.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??. simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /= *. destruct!. split!; [done|].
          tstep_s.
          split!; [done..|] => /=.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto.
        + move: ri xi Hi x' Hsat. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HN2R|].
          move => [[??]?] ? /= Hcont ??.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??. simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /= *. destruct!. split!; [done|].
          tstep_s.
          split!; [done..|] => /=.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto.
      - tsim_mirror m1.(m_trans) σ1'. { tstep_s. by exists None. }
        move => *. subst. tstep_s. eexists (Some (Incoming, _)). split!.
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. by split!.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done).
        eexists σ'. split; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
        tstep_i. apply pp_to_all_forall => ri xi Hi x' Hsat p' sr1' e' ok1 HR1 Hri.
        destruct p' as [[]|] => /=. 1: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2R|].
          move => [[??]?] ? /= Hcont ??????.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??; simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HL2N|].
          move => [[??]?] ? /= Hcont ??????.
          have {}Hcont := Hcont _ _ _ ltac:(done) ltac:(done) ltac:(done). destruct!.
          destruct e; simplify_eq/=.
          destruct ok1, ok2 => //.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          apply: Hloop; [done|]. split!. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ?. case_match; intros; simplify_eq.
        + tstep_s. eexists (Some (Incoming, _)). split!.
          apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
          apply: Hloop; [done|]. by split!.
        + tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
          apply: Hloop; [done|]. by split!.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done).
        eexists σ'. split; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
        tstep_i. apply pp_to_all_forall => ri xi Hi x' Hsat p' sr1' e' ok1 HR1 Hri.
        destruct p' as [[]|] => /=. 2: clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2L|].
          move => [[??]?] ? /= Hcont ??????.
          destruct ok1; [|clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver].
          tstep_i => ??; simplify_eq.
          tstep_i.
          apply: pp_to_ex_mono; [clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver|].
          move => [[??]?] ? /=?. destruct!. split!; [done|].
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          destruct e; simplify_eq/=.
          apply: steps_spec_step_end; [done|] => ??.
          destruct ok2; [|by tstep_s].
          apply: Hloop; [done|]. split!; eauto. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
        + move: ri xi Hi x' Hsat sr1' e' Hri HR1. apply: pp_to_all_forall_2.
          apply: pp_to_all_mono; [by apply: HR2N|].
          move => [[??]?] ? /= Hcont ??????.
          have {}Hcont := Hcont _ _ _ ltac:(done) ltac:(done) ltac:(done). destruct!.
          destruct e; simplify_eq/=.
          destruct ok1, ok2 => //.
          tstep_s. eexists (Some (Outgoing, _)). split!; [done|].
          apply: steps_spec_step_end; [done|] => ??.
          tstep_s.
          apply: pp_to_ex_mono; [done|].
          move => [[??]?] ? /= ?. destruct!. split!; [done|].
          apply: Hloop; [done|]. split!. clear HN2L HN2R HL2R HL2N HR2L HR2N; naive_solver.
  Qed.

  Lemma mod_prepost_combine
        {EV1 EV2 EV S1 S2 S : Type}
        {M1 M2 M : ucmra} `{!Shrink M1} `{!Shrink M2} `{!Shrink M}
        (m : module EV)
        (INV : player → S1 → S2 → S → uPred M1 → uPred M2 → uPred M → Prop)
        (i1 : EV1 → S1 → prepost (EV2 * S1) M1)
        (o1 : EV2 → S1 → prepost (EV1 * S1) M1)
        (i2 : EV2 → S2 → prepost (EV * S2) M2)
        (o2 : EV → S2 → prepost (EV2 * S2) M2)
        (i : EV1 → S → prepost (EV * S) M)
        (o : EV → S → prepost (EV1 * S) M)
        s1 s2 s x1 x2 x
        `{!VisNoAng m.(m_trans)}
        :
        (∀ e, pp_to_all (i e s) (λ r y, ∀ x',
            satisfiable (x ∗ y ∗ x') →
            ∃ x0, INV Env s1 s2 s x1 x2 x0 ∧ satisfiable (x0 ∗ y ∗ x'))) →
       (∀ s1 s2 s x1 x2 x e,
           INV Env s1 s2 s x1 x2 x →
           pp_to_all (i e s) (λ r y, ∀ x',
            satisfiable (x ∗ y ∗ x') →
             pp_to_ex (i1 e s1) (λ r1 y1, ∃ x1',
               satisfiable (x1 ∗ y1 ∗ x1') ∧
               pp_to_ex (i2 r1.1 s2) (λ r2 y2, ∃ x2',
                 satisfiable (x2 ∗ y2 ∗ x2') ∧
                 r.1 = r2.1 ∧
                 INV Prog r1.2 r2.2 r.2 x1' x2' x')))) →
       (∀ s1 s2 s x1 x2 x e,
           INV Prog s1 s2 s x1 x2 x →
           pp_to_all (o2 e s2) (λ r2 y2, ∀ x2',
             satisfiable (x2' ∗ y2 ∗ x2) →
             pp_to_all (o1 r2.1 s1) (λ r1 y1, ∀ x1',
             satisfiable (x1' ∗ y1 ∗ x1) →
               pp_to_ex (o e s) (λ r y, ∃ x',
                 satisfiable (x' ∗ y ∗ x) ∧
                 r.1 = r1.1 ∧
                 INV Env r1.2 r2.2 r.2 x1' x2' x')))) →
    trefines (prepost_mod i1 o1 (prepost_mod i2 o2 m s2 x2) s1 x1)
             (prepost_mod i o m s x).
    Proof.
      move => Hinv Henv Hprog.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σf1, (σf2, σ1, (σpp2, s2, x2)), (σpp1, s1, x1))
          '(σf, σ, (σpp, s, x)),
           ∃ p rx1 rx2 rx,
           x1 = uPred_shrink rx1 ∧ x2 = uPred_shrink rx2 ∧ x = uPred_shrink rx ∧
           σ = σ1 ∧ (if p is Env then
            (∀ e, pp_to_all (i e s) (λ r y, ∀ x', satisfiable (rx ∗ y ∗ x') →
                ∃ rx0, INV p s1 s2 s rx1 rx2 rx0 ∧ satisfiable (rx0 ∗ y ∗ x')))
                     else INV p s1 s2 s rx1 rx2 rx) ∧
           ((p = Env ∧ σf1 = SMFilter ∧ σf2 = SMFilter ∧ σf = SMFilter ∧
              σpp1 = PPOutside ∧ σpp2 = PPOutside ∧ σpp = PPOutside) ∨
            (p = Prog ∧ σf1 = SMProg ∧ σpp1 = PPInside ∧ σpp2 = PPInside ∧ σpp = PPInside ∧
               (σf = SMProg ∧ σf2 = SMProg ∨ ∃ e, σf = SMProgRecv e ∧ σf2 = SMProgRecv e)))). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[σf1 [[σf2 σ1] [[σpp2 {}s2] {}x2]]] [[σpp1 {}s1] {}x1]].
      move => [[σf {}σ] [[σpp {}s] {}x]] ?. destruct!.
      - tstep_i => ?.
        tstep_s. split!.
        tstep_s.
        apply pp_to_all_forall => ?????.
        revert select (∀ e, pp_to_all _ _).
        setoid_rewrite pp_to_all_forall => Hinit.
        exploit Hinit; [done..|] => -[? [??]].
        setoid_rewrite pp_to_all_forall in Henv.
        exploit Henv; [done..|] => ?.
        tstep_i. apply: pp_to_ex_mono; [naive_solver|]. move => r1 y1 /= [?[??]]. split!; [done|].
        tstep_i => ??. subst.
        tstep_i. apply: pp_to_ex_mono; [done|]. move => r2 y2 /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. by f_equal.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply: pp_to_all_mono; [by apply: Hprog|]. move => r2 y2 /= ???.
        tstep_i. apply: pp_to_all_mono; [naive_solver|]. move => r1 y1 /= ???.
        tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ?? /=.
        tstep_s. apply: pp_to_ex_mono; [naive_solver|]. move => r y /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. naive_solver.
        move => ?. apply pp_to_all_forall => *. naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        move => ->.
        tstep_s. eexists (Some _). split; [done|].
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. split!.
  Qed.


  Lemma mod_prepost_combine_bi
      {EV1 EV2 EV S1 S2 S : Type}
      {M1 M2 M : ucmra} `{!Shrink M1} `{!Shrink M2} `{!Shrink M}
      `{!CmraDiscrete M1} `{!CmraDiscrete M2} `{!CmraDiscrete M}
      `{!∀ x : M1, CoreCancelable x} `{!∀ x : M2, CoreCancelable x}
      `{!∀ x : M, CoreCancelable x}
      (m : module EV)
      (i1 : EV1 → S1 → prepost (EV2 * S1) M1)
      (o1 : EV2 → S1 → prepost (EV1 * S1) M1)
      (i2 : EV2 → S2 → prepost (EV * S2) M2)
      (o2 : EV → S2 → prepost (EV2 * S2) M2)
      (i : EV1 → S → prepost (EV * S) M)
      (o : EV → S → prepost (EV1 * S) M)
      s1 s2 s x1 x2 x
      `{!VisNoAng m.(m_trans)}
      :
      (∃ Σ `{!satG Σ M1} `{!satG Σ M2} `{!satG Σ M}, ∀ γ1 γ2 γ,
        ∃ (INV : player → S1 → S2 → S → iProp Σ),
        (∀ e, pp_to_all (i e s) (λ r y, (⌈x ∗ y @ sat γ⌉ -∗
           ∃ x1' x2', ⌜satisfiable (x1' ∗ x1)⌝ ∗ ⌜satisfiable (x2' ∗ x2)⌝ ∗ (
             ⌈{sat (M:=M1) γ1}⌉ -∗ ⌈{sat (M:=M2) γ2}⌉ -∗ ⌈{sat (M:=M) γ}⌉ -∗ ⌈x1' @ sat γ1⌉ -∗ ⌈x2' @ sat γ2⌉ ==∗
             INV Env s1 s2 s ∗ ⌈y @ sat γ⌉ ∗ ⌈{sat (M:=M1) γ1}⌉ ∗ ⌈{sat (M:=M2) γ2}⌉ ∗ ⌈{sat (M:=M) γ}⌉)))) ∧
       (∀ s1 s2 s e,
           pp_to_all (i e s) (λ r y,
            ⌈{sat (M:=M1) γ1}⌉ -∗ ⌈{sat (M:=M2) γ2}⌉ -∗ ⌈{sat (M:=M) γ}⌉ -∗
            ⌈y @ sat γ⌉ -∗
            INV Env s1 s2 s ==∗
            pp_to_ex_bi (sat γ1) (i1 e s1) (λ r1,
            pp_to_ex_bi (sat γ2) (i2 r1.1 s2) (λ r2,
            ⌜r.1 = r2.1⌝ ∗ INV Prog r1.2 r2.2 r.2 ∗
            ⌈{sat (M:=M1) γ1}⌉ ∗ ⌈{sat (M:=M2) γ2}⌉ ∗ ⌈{sat (M:=M) γ}⌉
)))) ∧
       (∀ s1 s2 s e,
           pp_to_all (o2 e s2) (λ r2 y2,
             pp_to_all (o1 r2.1 s1) (λ r1 y1,
            ⌈{sat (M:=M1) γ1}⌉ -∗ ⌈{sat (M:=M2) γ2}⌉ -∗ ⌈{sat (M:=M) γ}⌉ -∗
            ⌈y1 @ sat γ1⌉ -∗
            ⌈y2 @ sat γ2⌉ -∗
            INV Prog s1 s2 s ==∗
            pp_to_ex_bi (sat γ) (o e s) (λ r,
            ⌜r.1 = r1.1⌝ ∗ INV Env r1.2 r2.2 r.2 ∗
            ⌈{sat (M:=M1) γ1}⌉ ∗ ⌈{sat (M:=M2) γ2}⌉ ∗ ⌈{sat (M:=M) γ}⌉
))))
) →
  trefines (prepost_mod i1 o1 (prepost_mod i2 o2 m s2 x2) s1 x1)
           (prepost_mod i o m s x).
  Proof.
    move => [Σ [HG1 [HG2 [HG]]]].
    have ? : @satisfiable (iResUR Σ) (∃ γ1 γ2 γ,
      sat_closed γ1 true x1 ∗ sat_closed γ2 true x2 ∗ sat_closed γ true x). {
      apply: satisfiable_bmono; [by apply (satisfiable_emp_valid True)|].
      iIntros "_". iMod (sat_alloc_closed x1) as (?) "$".
      iMod (sat_alloc_closed x2) as (?) "$".
      by iMod (sat_alloc_closed x) as (?) "$".
    }
    iSatStart. iDestruct 1 as (γ1 γ2 γ) "(Hγ1 & Hγ2 & Hγ)". iSatStop Hsat.
    move => /(_ γ1 γ2 γ) [INV [? [??]]].
    unshelve apply: mod_prepost_combine. {
      exact (λ pl s1 s2 s x1 x2 x,
              satisfiable (INV pl s1 s2 s ∗
                if pl is Env then
                  ⌈x1 @ sat γ1⌉ ∗ ⌈{sat (M:=M1) γ1}⌉ ∗ ⌈x2 @ sat γ2⌉ ∗
                    ⌈{sat (M:=M2) γ2}⌉ ∗ sat_closed γ false x
                else
                  sat_closed γ1 false x1 ∗ sat_closed γ2 false x2 ∗
                    ⌈x @ sat γ⌉ ∗ ⌈{sat (M:=M) γ}⌉)).
    } {
      move => ?. apply: pp_to_all_mono; [done|]. move => ?? /= Hwand ? Hsat0.
      iSatStartBupd Hsat.
      iMod ("Hγ" with "[]") as "[? Hx]". { iPureIntro. by rewrite comm in Hsat0. }
      iDestruct "Hx" as "[[? H1] ?]".
      iDestruct (Hwand with "[$]") as (?? Hsat1 Hsat2) "Hwand".
      iMod ("Hγ1" with "[]") as "[? [??]]"; [done|].
      iMod ("Hγ2" with "[]") as "[? [??]]"; [done|].
      iMod ("Hwand" with "[$] [$] [$] [$] [$]") as "[? [H2 [? [??]]]]".
      iCombine "H2 H1" as "H".
      iDestruct (sat_close with "H [$]") as (? ?) "?".
      iModIntro. iSatStop. split!. 2: by rewrite comm.
      iSatMono. iFrame.
    }
    - iSatClear. move => /= ??????? Hsat.
      apply: pp_to_all_mono; [done|]. move => ?? /= Hwand ? Hsat0.
      iSatStartBupd Hsat. iIntros "(? & Hx1 & ? & Hx2 & ? & Hγ)".
      iMod ("Hγ" with "[]") as "[? Hx]". { iPureIntro. by rewrite comm in Hsat0. }
      iDestruct "Hx" as "[??]".
      iMod (Hwand with "[$] [$] [$] [$] [$]").
      iDestruct (pp_to_ex_bi_to_ex with "[$]") as (???) "[Hy1 ?]".
      iDestruct (pp_to_ex_bi_to_ex with "[$]") as (???) "[Hy2 [% [? [? [??]]]]]".
      iModIntro. iSatStop Hsat.
      apply: pp_to_ex_mono; [done|]. move => /= ?? [<- <-].
      iSatStart Hsat.
      iCombine "Hx1 Hy1" as "H1".
      iDestruct (sat_close with "H1 [$]") as (? ?) "?".
      iSatStop Hsat. split!. { by rewrite assoc. }
      apply: pp_to_ex_mono; [done|]. move => /= ?? [<- <-].
      iSatStart Hsat.
      iCombine "Hx2 Hy2" as "H2".
      iDestruct (sat_close with "H2 [$]") as (? ?) "?".
      iSatStop Hsat. split!. { by rewrite assoc. }
      iSatMono Hsat. iFrame.
    - iSatClear. move => /= ??????? Hsat.
      apply: pp_to_all_mono; [done|]. move => ?? /= ?? Hsat2.
      apply: pp_to_all_mono; [done|]. move => ?? /= Hwand ? Hsat1.
      iSatStartBupd Hsat. iIntros "(? & Hγ1 & Hγ2 & Hx & Hγ)".
      iMod ("Hγ1" with "[]") as "[? H]". { iPureIntro. by rewrite assoc in Hsat1. }
      iDestruct "H" as "[??]".
      iMod ("Hγ2" with "[]") as "[? H]". { iPureIntro. by rewrite assoc in Hsat2. }
      iDestruct "H" as "[??]".
      iMod (Hwand with "[$] [$] [$] [$] [$] [$]").
      iDestruct (pp_to_ex_bi_to_ex with "[$]") as (???) "[Hy [% [? [? [??]]]]]".
      iModIntro. iSatStop Hsat.
      apply: pp_to_ex_mono; [done|]. move => /= ?? [<- <-].
      iSatStart Hsat.
      iCombine "Hx Hy" as "H".
      iDestruct (sat_close with "H [$]") as (? ?) "?".
      iSatStop Hsat. split!. { by rewrite comm (comm _ y). }
      iSatMono Hsat. iFrame.
  Qed.

  Lemma mod_prepost_impl
        {EV1 EV2 Si Ss : Type}
        {Mi Ms : ucmra} `{!Shrink Mi} `{!Shrink Ms}
        (m : module EV2)
        (INV : player → Si → Ss → uPred Mi → uPred Ms → Prop)
        (i_i : EV1 → Si → prepost (EV2 * Si) Mi)
        (o_i : EV2 → Si → prepost (EV1 * Si) Mi)
        (i_s : EV1 → Ss → prepost (EV2 * Ss) Ms)
        (o_s : EV2 → Ss → prepost (EV1 * Ss) Ms)
        si ss xi xs
        `{!VisNoAng m.(m_trans)}
        :
        INV Env si ss xi xs →
       (∀ si ss xi xs e,
           INV Env si ss xi xs →
           pp_to_all (i_s e ss) (λ rs ys, ∀ xs',
            satisfiable (xs ∗ ys ∗ xs') →
             pp_to_ex (i_i e si) (λ ri yi, ∃ xi',
               satisfiable (xi ∗ yi ∗ xi') ∧
               rs.1 = ri.1 ∧
               INV Prog ri.2 rs.2 xi' xs'))) →
       (∀ si ss xi xs e,
           INV Prog si ss xi xs →
           pp_to_all (o_i e si) (λ ri yi, ∀ xi',
             satisfiable (xi' ∗ yi ∗ xi) →
             pp_to_ex (o_s e ss) (λ rs ys, ∃ xs',
               satisfiable (xs' ∗ ys ∗ xs) ∧
               rs.1 = ri.1 ∧
               INV Env ri.2 rs.2 xi' xs'))) →
    trefines (prepost_mod i_i o_i m si xi)
             (prepost_mod i_s o_s m ss xs).
    Proof.
      move => Hinv Henv Hprog.
      apply tsim_implies_trefines => /= n.
      unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σfi, σi, (σppi, si, xi))
          '(σfs, σs, (σpps, ss, xs)),
           ∃ p rxi rxs,
           xi = uPred_shrink rxi ∧ xs = uPred_shrink rxs ∧
           σi = σs ∧ INV p si ss rxi rxs ∧ σfi = σfs ∧ σppi = σpps ∧
           ((p = Env ∧ σfi = SMFilter ∧ σppi = PPOutside) ∨
            (p = Prog ∧ σppi = PPInside ∧
               (σfi = SMProg ∨ ∃ e, σfi = SMProgRecv e)))). }
      { split!. } { done. }
      move => {}n _ /= Hloop {Hinv}.
      move => [[σfi σi] [[σppi {}si] {}xi]].
      move => [[σfs {}σs] [[σpps {}ss] {}xs]] ?. destruct!.
      - tstep_i => ?.
        tstep_s. split!.
        tstep_s. apply: pp_to_all_mono; [by apply: Henv|]. move => r y /= ???.
        tstep_i. apply: pp_to_ex_mono; [naive_solver|]. move => r1 y1 /= [?[??]]. split!; [done|]. destruct!.
        apply: Hloop; [done|]. split!. by f_equal.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        tend. have [σ' Hσ'] := vis_no_all _ _ _ ltac:(done). eexists σ'. split; [naive_solver|].
        tstep_i. apply: pp_to_all_mono; [by apply: Hprog|]. move => r2 y2 /= ???.
        tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ?? /=.
        tstep_s. apply: pp_to_ex_mono; [naive_solver|]. move => r y /= [?[?[??]]]. split!; [done|].
        apply: Hloop; [done|]. split!. naive_solver.
      - tstep_both.
        apply steps_impl_step_end => κ Pσ2 ? *. destruct κ as [e'|]. 2: {
          tstep_s. eexists None. split!.
          apply: steps_spec_step_end; [done|] => ??. tend. eexists _. split; [done|].
          apply: Hloop; [done|]. by split!.
        }
        move => ->.
        tstep_s. eexists (Some _). split; [done|].
        apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop; [done|]. split!.
    Qed.

  Lemma mod_prepost_impl_prop
        {EV1 EV2 S : Type}
        {M : ucmra} `{!Shrink M}
        (m : module EV2)
        (i : EV1 → S → prepost (EV2 * S) M)
        (o : EV2 → S → prepost (EV1 * S) M)
        s xi0 xs0
        `{!VisNoAng m.(m_trans)}
        :
         (∀ e, pp_to_all (i e s) (λ s' x',
             (xs0 -∗ x' ==∗ xi0 ∗ x'))) →
        trefines (prepost_mod i o m s xi0)
                 (prepost_mod i o m s xs0).
    Proof.
      move => Hsub.
      unshelve apply: mod_prepost_impl. {
        exact (λ p si ss xi xs, si = ss ∧
          match p with | Env => ss = s ∧ xs = xs0 ∧ xi = xi0 ∨ xs = xi | Prog => xi = xs end). }
      { naive_solver. }
      - move => /= ????? [? Hx]. subst. apply/pp_to_all_forall => ?????.
        apply: pp_to_ex_mono; [done|].
        move => ?? /= [-> ->]. split!.
        move: Hx => [[? [??]] | <-] //. simplify_eq.
        setoid_rewrite pp_to_all_forall in Hsub.
        ospecialize* Hsub; [done|].
        iSatMonoBupd. iIntros!. iMod (Hsub with "[$] [$]"). by iFrame.
      - move => /= ????? [? ?]. subst. apply/pp_to_all_forall => ?????.
        apply: pp_to_ex_mono; [done|].
        move => ?? /= [-> ->]. split!; [done|naive_solver].
    Qed.

End prepost.
