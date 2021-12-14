Require Export refframe.module.
Require Export refframe.trace_index.

(** [trefines] is a weaker notion of refinement that does not allow commuting choices and externally visible events*)

(** * tree traces *)
Inductive trace (EV : Type) : Type :=
| tnil
| tcons (κ : EV) (κs : trace EV)
| tex (T : Type) (f : T → trace EV)
| tall (T : Type) (f : T → trace EV).
Arguments tnil {_}.
Arguments tcons {_}.
Arguments tex {_}.
Arguments tall {_}.

Fixpoint tapp {EV} (κs1 κs2 : trace EV) :=
  match κs1 with
  | tnil => κs2
  | tcons κ κs' => tcons κ (tapp κs' κs2)
  | tex T f => tex T (λ x, tapp (f x) κs2)
  | tall T f => tall T (λ x, tapp (f x) κs2)
  end.

Definition option_trace {EV} (κ : option EV) : trace EV :=
  match κ with
  | Some κ => tcons κ tnil
  | None => tnil
  end.

Inductive subtrace {EV} : trace EV → trace EV → Prop :=
| subtrace_nil :
    subtrace tnil tnil
| subtrace_cons κ κs κs':
    subtrace κs κs' →
    subtrace (tcons κ κs) (tcons κ κs')
| subtrace_ex_l T f κs':
    (∀ x, subtrace (f x) κs') →
    subtrace (tex T f) κs'
| subtrace_all_r T f κs:
    (∀ x, subtrace κs (f x)) →
    subtrace κs (tall T f)
| subtrace_ex_r {T f} x κs:
    subtrace κs (f x) →
    subtrace κs (tex T f)
| subtrace_all_l {T f} x κs':
    subtrace (f x) κs' →
    subtrace (tall T f) κs'
.
Global Instance trace_subseteq EV : SubsetEq (trace EV) := @subtrace EV.
Global Instance trace_equiv EV : Equiv (trace EV) := λ x y, x ⊆ y ∧ y ⊆ x.
Global Instance subtrace_rewrite {EV} : RewriteRelation (@subtrace EV) := {}.

Global Instance subtrace_preorder EV : PreOrder (@subtrace EV).
Proof.
  constructor.
  - move => κs. elim: κs.
    + constructor.
    + move => ???. by constructor.
    + move => ???. constructor => ?. econstructor. naive_solver.
    + move => ???. constructor => ?. econstructor. naive_solver.
  - move => x y z Hs. elim: Hs z.
    + done.
    + move => ???? IH z Hs.
      elim: z Hs.
      * inversion 1.
      * move => ??? Hs. inversion Hs; simplify_eq. constructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        econstructor. naive_solver.
    + move => ???? IH ??. constructor. naive_solver.
    + move => ???? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K.
        -- econstructor. naive_solver.
        -- naive_solver.
    + move => ?? v ?? IH z Hs.
      elim: z Hs.
      * inversion 1; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
      * move => ??? Hs. inversion Hs; simplify_K; [ naive_solver |].
        econstructor. naive_solver.
    + move => ?? v ?? IH z Hs. econstructor. naive_solver.
Qed.
Global Instance equiv_trace_equiv EV : Equivalence (≡@{trace EV}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.

Lemma subtrace_nil_ex_inv EV T f:
  @tnil EV ⊆ tex T f →
  ∃ x, tnil ⊆ f x.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_cons_ex_inv {EV} (κ : EV) κs T f:
  tcons κ κs ⊆ tex T f →
  ∃ x, tcons κ κs ⊆ f x.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_all_nil_inv EV T f:
  tall T f ⊆ @tnil EV →
  ∃ x, f x ⊆ tnil.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Lemma subtrace_all_cons_inv {EV} (κ : EV) κs T f:
  tall T f ⊆ tcons κ κs →
  ∃ x, f x ⊆ tcons κ κs.
Proof. inversion 1; simplify_K. naive_solver. Qed.

Global Instance tapp_assoc {EV} : Assoc (=) (@tapp EV).
Proof.
  move => x. elim: x => //=.
  - move => ?????. f_equal. naive_solver.
  - move => ?? IH ??. f_equal. apply functional_extensionality. naive_solver.
  - move => ?? IH ??. f_equal. apply functional_extensionality. naive_solver.
Qed.

Lemma tapp_mono {EV} (κs1 κs1' κs2 κs2' : trace EV) :
  κs1 ⊆ κs1' →
  κs2 ⊆ κs2' →
  tapp κs1 κs2 ⊆ tapp κs1' κs2'.
Proof.
  move => Hs.
  elim: Hs κs2 κs2' => /=.
  - naive_solver.
  - move => ????????. constructor. naive_solver.
  - move => ????????. constructor => ?. naive_solver.
  - move => ????????. econstructor. naive_solver.
  - move => ?????????. econstructor. naive_solver.
  - move => ?????????. econstructor. naive_solver.
Qed.

Global Instance tapp_proper {EV} :
  Proper ((⊆) ==> (⊆) ==> (⊆)) (@tapp EV).
Proof. move => ??????. by apply tapp_mono. Qed.
Global Instance tapp_proper_flip {EV} :
  Proper (flip (⊆) ==> flip (⊆) ==> (flip (⊆))) (@tapp EV).
Proof. move => ??????. by apply tapp_mono. Qed.

Lemma tapp_tnil_r {EV} (κs : trace EV) :
  tapp κs tnil = κs.
Proof.
  elim: κs.
  - done.
  - move => ?? Htapp /=. by f_equal.
  - move => ?? IH /=. f_equal. apply functional_extensionality. naive_solver.
  - move => ?? IH /=. f_equal. apply functional_extensionality. naive_solver.
Qed.

Definition tub {EV} :=
  @tex EV Empty_set (λ x, match x with end).

Definition tnb {EV} :=
  @tall EV Empty_set (λ x, match x with end).

Lemma tub_sub {EV} (κs : trace EV):
  tub ⊆ κs.
Proof. by constructor. Qed.

Lemma tnb_sub {EV} (κs : trace EV):
  κs ⊆ tnb.
Proof. by constructor. Qed.

Lemma tex_unit EV (f : _ → trace EV):
  tex () f ≡ f tt.
Proof. split; econstructor; [case|]; done. Qed.

(** * under_tall *)
Inductive under_tall {EV} : trace EV → (trace EV → Prop) → Prop :=
| UTEnd κs (P : _ → Prop):
  P κs →
  under_tall κs P
| UTAll T f κs (P : _ → Prop):
  (∀ x, under_tall (f x) P) →
  tall T f ⊆ κs →
  under_tall κs P.

Lemma under_tall_mono {EV} (κs1 κs2 : trace EV) (P1 P2 : _ → Prop):
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs1' κs2', κs1' ⊆ κs2' → P1 κs1' → P2 κs2') →
  under_tall κs2 P2.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ????? HP. econs. apply: HP; [..|done] => //.
  - move => ????? IH ??? HP. apply: UTAll; [|by etrans]. move => ?. apply: IH; [done|].
    done.
Qed.

Global Instance under_tall_proper {EV} :
  Proper ((⊆) ==> ((⊆) ==> impl) ==> impl) (@under_tall EV).
Proof. move => κs1 κs2 Hsub ?? HP Hall. by apply: under_tall_mono. Qed.

Lemma subtrace_under_tall {EV} (κs κs1 : trace EV) (P1 : _ → Prop):
  under_tall κs1 P1 →
  (∀ κs', P1 κs' → κs ⊆ κs') →
  κs ⊆ κs1.
Proof.
  move => Hall. elim: Hall.
  - move => ??? HP. by apply: HP.
  - move => ????????. etrans; [|done]. econs => ?. naive_solver.
Qed.

(** * trefines *)

(* Definition VisNoUb {EV} (m : module EV) (κ : option EV) (Pσ : (m.(m_state) → Prop)) := *)
  (* is_Some κ → ∃ σ, Pσ σ. *)

Inductive thas_trace {EV} (m : module EV) : m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| TTraceEnd σ (Pσ : _ → Prop) κs:
    Pσ σ →
    tnil ⊆ κs →
    thas_trace m σ κs Pσ
| TTraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → thas_trace m σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    (* VisNoUb m κ Pσ2 → *)
    thas_trace m σ1 κs Pσ3
| TTraceAll T f σ κs Pσ:
    (∀ x, thas_trace m σ (f x) Pσ) →
    tall T f ⊆ κs →
    thas_trace m σ κs Pσ
.
Notation " σ '~{' m , Pκs '}~>ₜ' P " := (thas_trace m σ Pκs P) (at level 40).
Notation " σ '~{' m , Pκs '}~>ₜ' - " := (thas_trace m σ Pκs (λ _, True)) (at level 40).

Inductive thas_trace_simple {EV} (m : module EV) : m.(m_state) → trace EV → (m.(m_state) → Prop) → Prop :=
| TSTraceEnd σ (Pσ : _ → Prop) κs:
    Pσ σ →
    tnil ⊆ κs →
    thas_trace_simple m σ κs Pσ
| TSTraceStep σ1 Pσ2 Pσ3 κ κs κs':
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2, Pσ2 σ2 → thas_trace_simple m σ2 κs' Pσ3) →
    tapp (option_trace κ) κs' ⊆ κs →
    (* VisNoUb m κ Pσ2 → *)
    thas_trace_simple m σ1 κs Pσ3
.
Notation " σ '~{' m , Pκs '}~>ₜₛ' P " := (thas_trace_simple m σ Pκs P) (at level 40).
Notation " σ '~{' m , Pκs '}~>ₜₛ' - " := (thas_trace_simple m σ Pκs (λ _, True)) (at level 40).

Inductive tnhas_trace {EV} (m : module EV) : m.(m_state) → trace EV → trace_index → (m.(m_state) → Prop) → Prop :=
| TNTraceEnd σ (Pσ : _ → Prop) κs n:
    Pσ σ →
    tnil ⊆ κs →
    tnhas_trace m σ κs n Pσ
| TNTraceStep Pσ2 fn σ1 Pσ3 κ κs κs' n:
    m.(m_step) σ1 κ Pσ2 →
    (∀ σ2 (H : Pσ2 σ2), tnhas_trace m σ2 κs' (fn (σ2 ↾ H)) Pσ3) →
    (∀ x, fn x ⊂ n) →
    tapp (option_trace κ) κs' ⊆ κs →
    (* VisNoUb m κ Pσ2 → *)
    tnhas_trace m σ1 κs n Pσ3
| TNTraceAll T fn f σ κs Pσ n:
    (∀ x, tnhas_trace m σ (f x) (fn x) Pσ) →
    tall T f ⊆ κs →
    (∀ x, fn x ⊆ n) →
    tnhas_trace m σ κs n Pσ
.
Notation " σ '~{' m , Pκs , n '}~>ₜ' P " := (tnhas_trace m σ Pκs n P) (at level 40).
Notation " σ '~{' m , Pκs , n '}~>ₜ' - " := (tnhas_trace m σ Pκs n (λ _, True)) (at level 40).

Lemma TTraceStepNone {EV} (m : module EV) σ1 Pσ2 Pσ3 κs:
  m_step m σ1 None Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs }~>ₜ Pσ3) →
  σ1 ~{ m, κs }~>ₜ Pσ3.
Proof. move => ??. by apply: TTraceStep. Qed.

Lemma TTraceStepSome {EV} (m : module EV) σ1 Pσ2 Pσ3 e κs:
  m_step m σ1 (Some e) Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs }~>ₜ Pσ3) →
  σ1 ~{ m, tcons e κs }~>ₜ Pσ3.
Proof. move => ??. by apply: TTraceStep. Qed.

Ltac tstep_None :=
  apply: TTraceStepNone.
Ltac tstep_Some :=
  apply: TTraceStepSome.
Ltac tstep :=
  first [
      apply: TTraceStep |
      apply: TNTraceStep
    ].
Ltac tend :=
  move => *;
         first [
             apply: TTraceEnd; [try done|try done]
           |
             apply: TNTraceEnd; try done
           ]
.

Global Instance thas_trace_proper {EV} (m : module EV) :
  Proper ((=) ==> (⊆) ==> (pointwise_relation m.(m_state) impl) ==> impl) (thas_trace m).
Proof.
  move => ?? -> κs1 κs2 Hκs Pσ1 Pσ2 HP Ht.
  elim: Ht κs2 Pσ2 Hκs HP.
  - move => ???????? HP. tend; [ by apply: HP | by etrans].
  - move => ??????? IH Hnext ??? Hκs HP.
    tstep; [done| |].
    + move => ??. naive_solver.
    + by etrans.
  - move => *. eapply TTraceAll. naive_solver. by etrans.
Qed.

Global Instance thas_trace_proper_flip {EV} (m : module EV) :
  Proper ((=) ==> (flip (⊆)) ==> (=) ==> flip impl) (thas_trace m).
Proof. move => ?? -> ?? Hsub ?? -> /=. by rewrite Hsub. Qed.

Lemma thas_trace_mono {EV} {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~>ₜ Pσ2' →
  κs' ⊆ κs →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs }~>ₜ Pσ2.
Proof. move => ???. by apply: thas_trace_proper. Qed.

Lemma thas_trace_mono' {EV} {m : module EV} κs' κs (Pσ2 : _ → Prop)  σ1 :
  σ1 ~{ m, κs' }~>ₜ Pσ2 →
  κs' ⊆ κs →
  σ1 ~{ m, κs }~>ₜ Pσ2.
Proof. by move => ? <-. Qed.

Lemma thas_trace_under_tall {EV} m (κs1 κs2 : trace EV) (P1 Pσ : _ → Prop) σ:
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs', P1 κs' → σ ~{ m, κs' }~>ₜ Pσ) →
  σ ~{ m, κs2 }~>ₜ Pσ.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ???? <- HP. by apply: HP.
  - move => ????? IH Hκ ?? HP. apply: TTraceAll; [|by etrans]. naive_solver.
Qed.

Lemma thas_trace_all {EV T} f (m : module EV) σ Pσ:
  (∀ x, σ ~{ m, f x }~>ₜ Pσ) →
  σ ~{ m, tall T f }~>ₜ Pσ.
Proof. move => ?. by eapply TTraceAll. Qed.

Lemma thas_trace_ex {EV T} x f (m : module EV) σ Pσ:
  σ ~{ m, f x }~>ₜ Pσ →
  σ ~{ m, tex T f }~>ₜ Pσ.
Proof. move => ?. apply: thas_trace_mono'; [done|]. by econstructor. Qed.

Lemma thas_trace_inv {EV} (m : module EV) κs (Pσ : _ → Prop) σ:
  σ ~{ m, κs }~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ σ) ∨
    ∃ κ κs' Pσ2, m_step m σ κ Pσ2 ∧ (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ Pσ) ∧ tapp (option_trace κ) κs' ⊆ κs).
Proof.
  elim.
  - move => ?????. econs. naive_solver.
  - move => *. econs. naive_solver.
  - move => ?????? IH ?. apply: UTAll; [|done]. done.
Qed.

Lemma thas_trace_trans {EV} κs1 κs2 (m : module EV) σ1 Pσ2 Pσ3 :
  σ1 ~{ m, κs1 }~>ₜ Pσ2 →
  (∀ σ2, Pσ2 σ2 → σ2 ~{ m, κs2 }~>ₜ Pσ3) →
  σ1 ~{ m, tapp κs1 κs2 }~>ₜ Pσ3.
Proof.
  elim.
  - move => ???? <- /= ?. naive_solver.
  - move => ????????? <- ?. rewrite -assoc_L.
    tstep; [done| |done]. naive_solver.
  - move => ??????? <- ?.
    eapply TTraceAll; [|simpl; done].
    naive_solver.
Qed.

Lemma thas_trace_nil_inv' {EV} κs (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tnil →
  σ1 ~{ m, tnil }~>ₜₛ Pσ3.
Proof.
  elim.
  - move => *. by apply: TSTraceEnd.
  - move => ??? κ ???? IH <- Ht.
    destruct κ; simplify_eq/=. 1: by inversion Ht.
    apply: TSTraceStep; [done| move => ??; by apply: IH | done].
  - move => ?????? IH <- Ht. inversion Ht; simplify_K. by apply: IH.
Qed.

Lemma thas_trace_nil_inv {EV} (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tnil }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜₛ Pσ3.
Proof. move => ?. by apply: thas_trace_nil_inv'. Qed.

Lemma thas_trace_cons_inv' {EV} κs κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tcons κ κs' →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~>ₜ Pσ3).
Proof.
  move => Hs.
  elim: Hs κ κs'.
  - move => ???? Hnil κ κs'. rewrite -Hnil => ?. easy.
  - move => ??? κ' ???? IH Hs ??. rewrite -Hs => Ht.
    destruct κ'; simplify_eq/=.
    + inversion Ht; simplify_eq. tend.
      eexists _. split; [ done |]. move => ??.
      apply: thas_trace_mono; [ naive_solver | | naive_solver].
      done.
    + tstep; [ done | | by constructor].
      move => ??. by apply: IH.
  - move => ?????? IH Hsub ??. rewrite -Hsub => /(subtrace_all_cons_inv _ _)[??].
    naive_solver.
Qed.

Lemma thas_trace_cons_inv {EV} κs' κ (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tcons κ κs' }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ Pσ2', m.(m_step) σ2 (Some κ) Pσ2' ∧ ∀ σ2', Pσ2' σ2' → σ2' ~{ m, κs' }~>ₜ Pσ3).
Proof. move => ?. by apply: thas_trace_cons_inv'. Qed.

Lemma thas_trace_ex_inv' {EV} κs T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tex T f →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ x, σ2 ~{ m, f x }~>ₜ Pσ3).
Proof.
  move => Hs.
  elim: Hs T f.
  - move => ????? T f ?.
    have : tnil ⊆ tex T f by etrans.
    move => /subtrace_nil_ex_inv[??].
    tend. eexists _. by constructor.
  - move => ??? κ ???? IH Hs ?? Hsub.
    destruct κ; simplify_eq/=.
    + pose proof (transitivity Hs Hsub) as Ht.
      move: Ht => /(subtrace_cons_ex_inv _ _)[??].
      constructor; [|done]. eexists _.
      apply: TTraceStep; [done|done|done].
    + apply: TTraceStep; [ done | | by constructor].
      move => ??. apply: IH; [done|].
      by etrans.
  - move => T1 f1 ???? IH Hsub1 T2 f2 Hsub2.
    pose proof (transitivity Hsub1 Hsub2) as Ht.
    inversion Ht; simplify_K. 2: naive_solver.
    constructor; [|done]. eexists _. apply: thas_trace_mono; [|done|done].
    by apply: thas_trace_all.
Qed.

Lemma thas_trace_ex_inv {EV} T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tex T f }~>ₜ Pσ3 →
  σ1 ~{ m, tnil }~>ₜ (λ σ2, ∃ x, σ2 ~{ m, f x }~>ₜ Pσ3).
Proof. move => ?. by apply: thas_trace_ex_inv'. Qed.

Lemma thas_trace_all_inv' {EV T} κs f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, κs }~>ₜ Pσ3 → κs ⊆ tall T f →
  ∀ x, σ1 ~{ m, f x }~>ₜ Pσ3.
Proof.
  move => ???. apply: thas_trace_mono; [done| |done].
  etrans; [done|]. by econstructor.
Qed.

Lemma thas_trace_all_inv {EV} T f (m : module EV) σ1 Pσ3:
  σ1 ~{ m, tall T f }~>ₜ Pσ3 →
  ∀ x, σ1 ~{ m, f x }~>ₜ Pσ3.
Proof. move => ??. by apply: thas_trace_all_inv'. Qed.

Lemma thas_trace_app_inv {EV} κs1 κs2 (m : module EV) σ1 Pσ3 :
  σ1 ~{ m, tapp κs1 κs2 }~>ₜ Pσ3 →
  σ1 ~{ m, κs1 }~>ₜ (λ σ2, σ2 ~{ m, κs2 }~>ₜ Pσ3).
Proof.
  elim: κs1 σ1 => /=.
  - move => ??. by tend.
  - move => ???? /(thas_trace_cons_inv _ _)?.
    apply: (thas_trace_trans tnil); [done| ].
    move => ?[?[??]]. tstep; [done| |simpl; done].
    naive_solver.
  - move => ???? /thas_trace_ex_inv?.
    apply: (thas_trace_trans tnil); [done| ].
    move => ?[??]. apply: thas_trace_ex. naive_solver.
  - move => ???? /thas_trace_all_inv?.
    apply: thas_trace_all. naive_solver.
Qed.

Lemma has_trace_inv {EV} κs (m : module EV) σ1 Pσ2:
  σ1 ~{ m, κs }~>ₜ Pσ2 →
  σ1 ~{ m, κs }~>ₜ (λ _, False) ∨ ∃ σ, Pσ2 σ.
Proof.
  elim; clear.
  - naive_solver.
  - move => σ1 Pσ2 Pσ3 κ κs κs' ? ? IH ?.
    have [?|HF]:= EM (∀ σ2 : m_state m, Pσ2 σ2 → σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)).
    + left. by tstep.
    + have [?|?]:= EM (∃ σ2, Pσ2 σ2 ∧ ¬ σ2 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)).
      naive_solver.
      exfalso. apply: HF => σ3?.
      have [//|?]:= EM (σ3 ~{ m, κs' }~>ₜ (λ _ : m_state m, False)). naive_solver.
  - move => T f σ κs Pσ _ IH Hsub.
    have [[x ?]|?]:= EM (∃ x : T, ¬ σ ~{ m, f x }~>ₜ (λ _, False)). naive_solver.
    left. eapply TTraceAll; [|done] => x.
    have [|]:= EM (σ ~{ m, f x }~>ₜ (λ _ : m_state m, False)); naive_solver.
Qed.

(** tnhas_trace *)
Global Instance tnhas_trace_proper {EV} (m : module EV) :
  Proper ((=) ==> (⊆) ==> (⊆) ==> (pointwise_relation m.(m_state) impl) ==> impl) (tnhas_trace m).
Proof.
  move => ?? -> κs1 κs2 Hκs n1 n2 Hn Pσ1 Pσ2 HP Ht.
  elim: Ht κs2 n2 Pσ2 Hκs Hn HP.
  - move => ??????????? HP. tend; [ by apply: HP | by etrans].
  - move => ?????????? IH ????????.
    tstep; [done| | | by etrans].
    + move => ??. naive_solver.
    + move => ?. by apply: ti_lt_le.
  - move => *. eapply TNTraceAll. naive_solver. by etrans. move => ?. etrans; [|done]. done.
Qed.

Global Instance tnhas_trace_proper_flip {EV} (m : module EV) :
  Proper ((=) ==> (flip (⊆)) ==> (flip (⊆)) ==> (=) ==> flip impl) (tnhas_trace m).
Proof. move => ?? -> ?? Hsub ?? Hsub2 ?? -> /=. by rewrite Hsub Hsub2. Qed.

Lemma tnhas_trace_mono {EV} {m : module EV} κs' κs (Pσ2' Pσ2 : _ → Prop)  σ1 n n' :
  σ1 ~{ m, κs', n' }~>ₜ Pσ2' →
  κs' ⊆ κs →
  n' ⊆ n →
  (∀ σ, Pσ2' σ → Pσ2 σ) →
  σ1 ~{ m, κs, n }~>ₜ Pσ2.
Proof. move => ????. by apply: tnhas_trace_proper. Qed.

Lemma tnhas_trace_under_tall {EV} m (κs1 κs2 : trace EV) (P1 Pσ : _ → Prop) σ n:
  under_tall κs1 P1 →
  κs1 ⊆ κs2 →
  (∀ κs', P1 κs' → σ ~{ m, κs', n }~>ₜ Pσ) →
  σ ~{ m, κs2, n }~>ₜ Pσ.
Proof.
  move => Hall. elim: Hall κs2.
  - move => ???? <- HP. by apply: HP.
  - move => ????? IH Hκ ?? HP. apply: TNTraceAll; [|by etrans |]. naive_solver. done.
Qed.

Lemma tnhas_trace_inv {EV} (m : module EV) κs (Pσ : _ → Prop) σ n:
  σ ~{ m, κs, n }~>ₜ Pσ →
  under_tall κs (λ κs, (tnil ⊆ κs ∧ Pσ σ) ∨
    ∃ κ κs' Pσ2 fn, m_step m σ κ Pσ2 ∧ (∀ σ2 (H : Pσ2 σ2), σ2 ~{ m, κs', fn (σ2 ↾ H) }~>ₜ Pσ)
      ∧ tapp (option_trace κ) κs' ⊆ κs ∧ (∀ x, fn x ⊂ n)).
Proof.
  elim.
  - move => ??????. econs. naive_solver.
  - move => *. econs. right. naive_solver.
  - move => ???????? IH ??. apply: UTAll; [|done].
    move => ?. apply: under_tall_mono; [done..|].
    move => ?? Hκ [[??]|?]; [left|right].
    + split; [|done]. by rewrite -Hκ.
    + destruct_all?. eexists _, _, _, _. split_and! => //. { by etrans. } move => ?.
      by apply: ti_lt_le.
Qed.

Lemma thas_trace_n_1 {EV} (m : module EV) σ κs Pσ:
  σ ~{m, κs}~>ₜ Pσ → ∃ n, σ ~{m, κs, n}~>ₜ Pσ.
Proof.
  elim.
  - move => ?????. eexists tiO. tend.
  - move => ???????? IH ?.
    have [f Hf]:= CHOICE IH. eexists (tiS (tiChoice _ f)).
    tstep; [done| | |done].
    + move => ??. apply Hf.
    + move => [??].
      apply: ti_lt_le; [apply ti_lt_S|]. apply ti_le_S_S. by apply: ti_le_choice_r.
  - move => ?????? IH ?.
    have [f Hf]:= AxCHOICE _ _ _ IH. eexists (tiChoice _ f).
    apply: TNTraceAll; [done|done|] => ?. by apply: ti_le_choice_r.
Qed.

Lemma thas_trace_n_2 {EV} (m : module EV) σ κs Pσ n:
  σ ~{m, κs, n}~>ₜ Pσ → σ ~{m, κs}~>ₜ Pσ.
Proof.
  elim.
  - tend.
  - move => *. by tstep.
  - move => *. by apply: TTraceAll.
Qed.

Lemma thas_trace_n {EV} (m : module EV) σ κs Pσ:
  σ ~{m, κs}~>ₜ Pσ ↔ ∃ n, σ ~{m, κs, n}~>ₜ Pσ.
Proof. split; [apply: thas_trace_n_1 | move => [??]; by apply: thas_trace_n_2]. Qed.

Record trefines {EV} (mimpl mspec : mod_state EV) : Prop := {
  tref_subset:
    ∀ κs, mimpl.(ms_state) ~{ mimpl, κs }~>ₜ - →
          mspec.(ms_state) ~{ mspec, κs }~>ₜ -
}.

Global Instance trefines_preorder EV : PreOrder (@trefines EV).
Proof.
  constructor.
  - constructor => // κ Hi; naive_solver.
  - move => ??? [Hr1] [Hr2]. constructor => /=. naive_solver.
Qed.

Tactic Notation "thas_trace_inv" ident(H) :=
  lazymatch type of H with
  | _ ~{ _, ?κs }~>ₜ _ =>
      apply thas_trace_inv in H
  | _ ~{ _, ?κs, _ }~>ₜ _ =>
      apply tnhas_trace_inv in H
  end;
  lazymatch goal with
  | |- under_tall _ _ =>
      let Hsub := fresh "Hsub" in
      apply (under_tall_mono _ _ _ _ H); [done|] => {H} ?? Hsub [H|H]; destruct_all?
  | |- _ ~{ _, _ }~>ₜ _ =>
      apply (thas_trace_under_tall _ _ _ _ _ _ H); [done|] => {H} ? [H|H]; destruct_all?
  | |- _ ⊆@{trace _} _ =>
      apply (subtrace_under_tall _ _ _ H) => {H} ? [H|H]; destruct_all?
  | |- subtrace _ _ =>
      apply (subtrace_under_tall _ _ _ H) => {H} ? [H|H]; destruct_all?
  end
.
Tactic Notation "thas_trace_inv" :=
  match goal with
  | H : _ |- _ =>  thas_trace_inv H
  end.
