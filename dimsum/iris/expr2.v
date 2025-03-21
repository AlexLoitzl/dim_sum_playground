From iris.bi Require Import fixpoint_mono.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core Require Import nb_mod.
From dimsum.core.iris Require Export ord_later sim.
Set Default Proof Using "Type".

(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mectx : Type;
  mfill : mectx → mexpr → mexpr;
  mcomp_ectx : mectx → mectx → mectx;
  mtrans :> mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
  mstate_interp : mtrans.(m_state) → iProp Σ;
  mfill_comp K1 K2 e : mfill K1 (mfill K2 e) = mfill (mcomp_ectx K1 K2) e
}.
Global Arguments mexpr {_ _} _.
Global Arguments mectx {_ _} _.
Global Arguments mfill {_ _} _.
Global Arguments mcomp_ectx {_ _} _.
Global Arguments mtrans {_ _} _.
Global Arguments mexpr_rel {_ _} _ _ _.
Global Arguments mstate_interp {_ _} _ _.

Definition sim_gen_mapsto_state `{!dimsumGS Σ} {EV} (ts : tgt_src) (m : mod_trans EV)
  (H_s : (m_state m) → (option EV → m_state m → iProp Σ) → iProp Σ) : iProp Σ :=
  ∀ σ Π, H_s σ Π -∗ σ ≈{ts, m}≈> Π.
Notation "'⥥{' ts , m '}' PΠ" := (sim_gen_mapsto_state ts m PΠ)
  (at level 20, only parsing) : bi_scope.

Notation "'⥥{' ts '}' PΠ" := (sim_gen_mapsto_state ts _ PΠ)
  (at level 20, format "'⥥{' ts '}' PΠ") : bi_scope.
Notation "'⥥{' m '}ₜ' PΠ" := (sim_gen_mapsto_state Tgt m PΠ)
  (at level 20, only parsing) : bi_scope.
Notation "'⥥ₜ' PΠ" := (sim_gen_mapsto_state Tgt _ PΠ)
  (at level 20, format "'⥥ₜ' PΠ") : bi_scope.

Notation "'⥥{' m '}ₛ' PΠ" := (sim_gen_mapsto_state Src m PΠ)
  (at level 20, only parsing) : bi_scope.
Notation "'⥥ₛ' PΠ" := (sim_gen_mapsto_state Src _  PΠ)
  (at level 20, format "'⥥ₛ' PΠ") : bi_scope.

Definition switch `{!dimsumGS Σ} {S EV} (Π : option EV → S → iProp Σ)
  (K : option EV → S → (tgt_src → ∀ EV2, ∀ m : mod_trans EV2, _ → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ κ σ, K κ σ (λ ts' EV2 m' PΠ', ⥥{ts', m'}PΠ') -∗  Π κ σ).
  (* (∀ κ σ, K κ σ (λ ts' EV2 m' PΠ', ∀ σ' Π', PΠ' σ' Π' -∗ σ' ≈{ ts', m' }≈> Π') -∗  Π κ σ). *)

Lemma switch_mono `{!dimsumGS Σ} {S' EV} (Π : option EV → S' → iProp Σ) K1 K2 :
  switch Π K1 -∗
  (∀ κ σ P1 P2, K2 κ σ P1 -∗ (∀ ts m Q1 Q2, P1 ts EV m Q1 -∗ (∀ σ Π, Q2 σ Π -∗ Q1 σ Π) -∗ P2 ts EV m Q2) -∗ K1 κ σ P2) -∗
  switch Π K2.
Proof.
  iIntros "Hs Hmono" (??) "HK2". iApply "Hs".
  iApply ("Hmono" with "HK2").
  iIntros (????) "HQ Hmono". iIntros (??) "?". iApply "HQ". by iApply "Hmono".
Qed.

Definition switch_id `{!dimsumGS Σ} {EV} (ts : tgt_src) (m : mod_trans EV)
  (Π : option EV → m.(m_state) → iProp Σ)
  (κ : option EV) (σ : m.(m_state)) (C : m.(m_state) → iProp Σ) : iProp Σ :=
  switch Π ({{ κs σs POST, ⌜κs = κ⌝ ∗ ⌜σs = σ⌝ ∗
  POST ts _ m ({{ σ' Πs, ⌜Πs = Π⌝ ∗ C σ'}})}})%I.

Lemma test `{!dimsumGS Σ} {EV} (ts : tgt_src) (m : mod_trans EV)
  (Π : option EV → m.(m_state) → iProp Σ)
  (κ : option EV) (σ : m.(m_state)) (C : m.(m_state) → iProp Σ) :
  switch_id ts m Π κ σ C ⊣⊢ ((∀ σ', C σ' -∗ σ' ≈{ts, m}≈> Π) -∗ Π κ σ).
Proof.
  iSplit.
  - rewrite /switch_id.
    iIntros "Hs HC".
    iApply "Hs" => /=. iSplit!.
    iIntros (??) "[-> HC']".
    by iApply "HC".
  - iIntros "H" (??) => /= . iIntros "[-> [-> Hs]]".
    iApply "H". iIntros (?) "HC". iApply "Hs". iSplit!.
Qed.

Lemma switch_id_mono `{!dimsumGS Σ} {EV} ts (m : mod_trans EV)
  (Π : option EV → m.(m_state) → iProp Σ) κ σ C1 C2 :
  switch_id ts m Π κ σ C1 -∗
  (∀ σ', C1 σ' -∗ C2 σ') -∗
  switch_id ts m Π κ σ C2.
Proof.
  iIntros "Hs Hmono" (??) "[% [% HC2]]". iApply "Hs".
  iSplit!. iIntros (??) "[% ?]". iApply "HC2". iSplit!.
  by iApply "Hmono".
Qed.

(* Switching for an externally visible event *)
(* TODO: Prove lemmas about this *)
Definition switch_external `{!dimsumGS Σ} {S EV} (Π : option EV → S → iProp Σ)
  (K : _) : iProp Σ :=
  switch Π ({{ κ σ POST,
    K κ σ ({{ m2 σ2 K2,
  POST Src _ m2 ({{ σ_s Π_s,
    ⌜σ_s = σ2⌝ ∗
  switch Π_s ({{ κ' σ_s2 POST,
    ⌜κ' = κ⌝ ∗
  POST Src _ _ ({{ σ_s2' Π',
    ⌜σ_s2' = σ_s2⌝ ∗ K2 σ_s2 Π'}})}})}})}})}})%I.

(* Variant of switch_external with which we can fix the module we switch to *)
Definition switch_external_fixed `{!dimsumGS Σ} {S EV} (Π : option EV → S → iProp Σ)
  (m : mod_trans EV) (Π' : option EV → m_state m → iProp Σ)
  (K : _) : iProp Σ :=
  switch Π ({{ κ σ POST,
    K κ σ ({{ σ2 K2,
  POST Src _ m ({{ σ_s Π_s,
    ⌜σ_s = σ2⌝ ∗ ⌜Π_s = Π'⌝ ∗
  switch Π_s ({{ κ' σ_s2 POST,
    ⌜κ' = κ⌝ ∗
  POST Src _ _ ({{ σ_s2' Π',
    ⌜σ_s2' = σ_s2⌝ ∗ K2 σ_s2 Π'}})}})}})}})}})%I.

(* Switching to a linked module *)
Definition switch_link `{!dimsumGS Σ} {S EV} (ts : tgt_src) (Π : option (io_event EV) → S → iProp Σ)
  (K : _) : iProp Σ :=
  switch Π ({{ κ σ0 POST,
    K σ0 ({{ e m2 σ2 K2, ⌜κ = Some (Outgoing, e)⌝ ∗
  POST ts _ m2 ({{ σi Πi,
    ⌜σi = σ2⌝ ∗
  switch Πi ({{ κ' σ POST,
    ∃ e', ⌜κ' = Some (Incoming, e')⌝ ∗
  POST ts _ m2 ({{ σr Πr,
    ⌜σr = σ⌝ ∗ ⌜e' = e⌝ ∗ K2 σ Πr}})}})}})}})}})%I.

Definition switch_link_fixed `{!dimsumGS Σ} {S EV} (ts : tgt_src) (Π : option (io_event EV) → S → iProp Σ)
  (m : mod_trans (io_event EV)) (Π' : option (io_event EV) → m_state m → iProp Σ) (K : _) : iProp Σ :=
  switch Π ({{ κ σ0 POST,
    K σ0 ({{ e σ2 K2, ⌜κ = Some (Outgoing, e)⌝ ∗
  POST ts _ m ({{ σi Πi,
    ⌜σi = σ2⌝ ∗ ⌜Πi = Π'⌝ ∗
  switch Πi ({{ κ' σ POST,
    ∃ e', ⌜κ' = Some (Incoming, e')⌝ ∗
  POST ts _ m ({{ σr Πr,
    ⌜σr = σ⌝ ∗ ⌜e' = e⌝ ∗ K2 σ Πr}})}})}})}})}})%I.

(** * [sim_gen_expr] *)
Section sim_gen_expr.
  Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
  Context (ts : tgt_src).
  Implicit Types (e : mexpr Λ).

  Definition sim_gen_expr_pre (Π : option EV → m_state Λ → iProp Σ)
    (sim_gen_expr : leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ := λ e Φ,
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ -∗
       σ ≈{ ts, Λ }≈> (λ κ σ',
        (∃ e', ⌜κ = None⌝ ∗ ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ ∗
          mstate_interp Λ σ' ∗ Φ e') ∨
        (switch_id ts Λ Π κ σ' (λ σ'',
         ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' ∗ sim_gen_expr e' Φ))))%I.

  (* For Spec *)
  (* Definition sim_gen_expr_pre' (Π : option EV → m_state Λ → iProp Σ) *)
  (*   (sim_gen_expr : leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ) : *)
  (*   leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ := λ e Φ, *)
  (*   (∀ σ, ⌜σ.1 ≡ e⌝ -∗ (spec_state σ.2) -∗ *)
  (*      σ ≈{ ts, Λ }≈> (λ κ σ', *)
  (*       (∃ e', ⌜κ = None⌝ ∗ ⌜σ'.1 ≡ e'⌝ ∗ *)
  (*         spec_state σ'.2 ∗ Φ e') ∨ *)
  (*       (switch_id ts Λ Π κ σ' (λ σ'', *)
  (*        ∃ e', ⌜σ''.1 ≡ e'⌝ ∗ spec_state σ'' ∗ sim_gen_expr e' Φ))))%I. *)

  Global Instance sim_gen_expr_pre_ne Π n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) (sim_gen_expr_pre Π).
  Proof.
    move => ?? Hsim ?? -> ?? HΦ. rewrite /sim_gen_expr_pre.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
    move => ?? -> ?? ->. unfold switch_id, curly_lambda2, curly_lambda3, switch, sim_gen_mapsto_state.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
  Qed.

  Lemma sim_gen_expr_pre_mono J sim1 sim2:
    ⊢ □ (∀ e Φ, sim1 e Φ -∗ sim2 e Φ)
    → ∀ e Φ, sim_gen_expr_pre J sim1 e Φ -∗ sim_gen_expr_pre J sim2 e Φ.
  Proof.
    iIntros "#Hinner" (e Φ) "Hsim". iIntros (???) "?".
    iSpecialize ("Hsim" with "[//] [$]"). iApply (sim_gen_wand with "Hsim").
    iIntros (??) "[$|Hsim]". iRight.
    iApply (switch_id_mono with "Hsim").
    iIntros (?) "[%e' [% [??]]]". iSplit!; [done|]. iFrame.
    by iApply "Hinner".
  Qed.

  Local Instance sim_gen_expr_pre_monotone J :
    BiMonoPred (λ sim_gen_expr : prodO (leibnizO (mexpr Λ)) (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ, uncurry (sim_gen_expr_pre J (curry sim_gen_expr))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=.
      iApply sim_gen_expr_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => sim_gen Hsim n [σ1 Φ1] [σ2 Φ2] /= [/=??].
      apply sim_gen_expr_pre_ne; eauto. move => ?????? /=. by apply: Hsim.
  Qed.

  Definition sim_gen_expr J : mexpr Λ → (mexpr Λ → iProp Σ) → iProp Σ :=
    curry (bi_least_fixpoint (λ sim_gen_expr : prodO (leibnizO (mexpr Λ)) (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ, uncurry (sim_gen_expr_pre J (curry sim_gen_expr)))).

  Global Instance sim_gen_expr_ne J n:
    Proper ((=) ==> (pointwise_relation _ (dist n)) ==> dist n) (sim_gen_expr J).
  Proof. move => ?? -> ?? HΦ. unfold sim_gen_expr. f_equiv. intros ?. by apply HΦ. Qed.
End sim_gen_expr.

Global Typeclasses Opaque sim_gen_expr.

Notation "'WP{' ts '}' e @ J {{ Φ } }" := (sim_gen_expr ts J e Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'WP{' ts '}' e @ J {{ e' , Φ } }" := (sim_gen_expr ts J e (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'WP{' ts '}'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'TGT' e @ J {{ Φ } }" := (sim_gen_expr Tgt J e Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'TGT' e @ J {{ e' , Φ } }" := (sim_gen_expr Tgt J e (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'SRC' e @ J {{ Φ } }" := (sim_gen_expr Src J e Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'SRC' e @ J {{ e' , Φ } }" := (sim_gen_expr Src J e (λ e', Φ%I)) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Section sim_gen_expr.
  Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
  Context (ts : tgt_src).
  Implicit Types (e : mexpr Λ).

  Local Existing Instance sim_gen_expr_pre_monotone.
  Lemma sim_gen_expr_unfold e Π Φ:
    WP{ts} e @ Π {{ Φ }} ⊣⊢ sim_gen_expr_pre ts Π (sim_gen_expr ts Π) e Φ.
  Proof. rewrite /sim_gen_expr /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_gen_expr_strong_ind Π (R: leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 R →
    ⊢ (□ ∀ e Φ, sim_gen_expr_pre ts Π (λ e Φ, R e Φ ∧ WP{ts} e @ Π {{Φ}}) e Φ -∗ R e Φ)
      -∗ ∀ e Φ, WP{ts} e @ Π {{Φ}} -∗ R e Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (e Φ) "Hsim".
    rewrite {2}/sim_gen_expr {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry R) with "[] Hsim").
    iIntros "!>" ([??]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_gen_expr_ind Π (R: leibnizO (mexpr Λ) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive2 R →
    ⊢ (□ ∀ e Φ, sim_gen_expr_pre ts Π R e Φ -∗ R e Φ)
      -∗ ∀ e Φ, WP{ts} e @ Π {{ Φ }} -∗ R e Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_gen_expr_strong_ind.
    iIntros "!>" (e Φ) "Hsim".
    iApply "HPre". iApply (sim_gen_expr_pre_mono with "[] Hsim").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Lemma sim_gen_expr_wand e Π Φ Ψ :
    WP{ts} e @ Π {{ Ψ }} -∗
    (∀ e', Ψ e' -∗ Φ e') -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HWP Hwand".
    pose (F := (λ e Ψ, ∀ Φ,
        (∀ e', Ψ e' -∗ Φ e') -∗
         WP{ts} e @ Π {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ Π {{Ψ}} -∗ F e Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP"). iIntros (?) "?". by iApply "Hwand". }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iSpecialize ("Hsim" with "[//] [$]").
    iApply (sim_gen_wand with "Hsim").
    iIntros (? ?) "[[% [% [% [? HΦ]]]]|Hsim] /=".
    - iLeft. iExists _. iSplit!; [done|]. iFrame. by iApply "Hc".
    - iRight. iApply (switch_id_mono with "Hsim"). iIntros (?) "[% [% [? Hsim]]] /=".
      iFrame. iSplit!; [done|]. by iApply "Hsim".
  Qed.

  Lemma sim_gen_expr_bind K e Π Φ :
    WP{ts} e @ Π {{ e', WP{ts} mfill Λ K e' @ Π {{Φ}} }} -∗
    WP{ts} mfill Λ K e @ Π {{ Φ }}.
  Proof.
    iIntros "HWP".
    pose (F := (λ e Ψ, ∀ Φ,
        (∀ e', Ψ e' -∗ WP{ts} mfill Λ K e' @ Π {{Φ}}) -∗
         WP{ts} mfill Λ K e @ Π {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ Π {{Ψ}} -∗ F e Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP"). iIntros (?) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_expr_unfold. iIntros (?? Hf) "?". rewrite mfill_comp in Hf.
    iApply sim_gen_bind.
    iSpecialize ("Hsim" with "[//] [$]").
    iApply (sim_gen_wand with "Hsim").
    iIntros (? ?) "[[% [% [% [? HΦ]]]]|Hsim] /=".
    - iRight. iSpecialize ("Hc" with "[$]"). rewrite sim_gen_expr_unfold.
      iDestruct ("Hc" with "[] [$]") as "?". { by rewrite mfill_comp. }
      iSplit!.
    - iLeft. iRight. iApply (switch_id_mono with "Hsim").
      iIntros (?) "[% [%Hf' [? Hsim]]] /=". rewrite -mfill_comp in Hf'.
      iFrame. iSplit!; [done|]. by iApply "Hsim".
  Qed.

  (* TODO: derive this lemma from the previous by requiring an empty context? *)
  Lemma sim_gen_expr_bind0 e Π Φ :
    WP{ts} e @ Π {{ e', WP{ts} e' @ Π {{Φ}} }} -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HWP".
    pose (F := (λ e Ψ, ∀ Φ,
        (∀ e', Ψ e' -∗ WP{ts} e' @ Π {{Φ}}) -∗
         WP{ts} e @ Π {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ Π {{Ψ}} -∗ F e Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP"). iIntros (?) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_expr_unfold. iIntros (?? Hf) "?".
    iApply sim_gen_bind.
    iSpecialize ("Hsim" with "[//] [$]").
    iApply (sim_gen_wand with "Hsim").
    iIntros (? ?) "[[% [% [% [? HΦ]]]]|Hsim] /=".
    - iRight. iSpecialize ("Hc" with "[$]"). rewrite sim_gen_expr_unfold.
      iDestruct ("Hc" with "[//] [$]") as "?".
      iSplit!.
    - iLeft. iRight. iApply (switch_id_mono with "Hsim").
      iIntros (?) "[% [%Hf' [? Hsim]]] /=".
      iFrame. iSplit!; [done|]. by iApply "Hsim".
  Qed.

  (*
  Lemma sim_gen_expr_handler_wand Π1 Π2 e os Φ :
    WP{ts} e @ ? os, Π1 {{ Φ }} -∗
    subMH Π1 Π2 -∗
    WP{ts} e @ ? os, Π2 {{ Φ }}.
  Proof.
    iIntros "HWP #Hwand".
    pose (F := (λ e os Φ, WP{ts} e @ ? os, Π2 {{Φ}})%I).
    iAssert (WP{ts} e @ ? os, Π1 {{Φ}} -∗ F e os Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP"). }
    iIntros "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (???) "Hsim". unfold F at 2.
    rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iMod ("Hsim" with "[//] [$]") as "[[% [% [? HΦ]]]|Hsim]"; iModIntro.
    - iLeft. iExists _. by iFrame.
    - iRight. iApply (sim_gen_wand with "Hsim"). iIntros (? ?) "Hsim /=".
      iApply "Hwand". iApply (imodhandle_mono with "Hsim").
      iIntros (?) "(%e'&?&?&Hsim)". iExists _. by iFrame.
  Qed.
   *)

  Definition sim_post (K : mectx Λ) (Π : option EV → m_state Λ → iProp Σ) (e : mexpr Λ) : iProp Σ :=
    ∀ σ', ⌜mexpr_rel Λ σ' (mfill Λ K e)⌝ -∗ mstate_interp Λ σ' -∗ σ' ≈{ts, Λ}≈> Π.

  (* Be careful when choosing Π when applying this rule, it must never change! *)
  Lemma sim_gen_expr_intro K e Π σ :
    mexpr_rel Λ σ (mfill Λ K e) →
    mstate_interp Λ σ -∗
    WP{ts} e @ Π {{ sim_post K Π }} -∗
    σ ≈{ts, Λ}≈> Π.
  Proof.
    iIntros (?) "Hσ Hsim".
    pose (F := (λ e Ψ, ∀ σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ -∗
       (∀ e', Ψ e' -∗ sim_post K Π e') -∗
       σ ≈{ ts, Λ }≈> Π)%I).
    iAssert (∀ e Φ, WP{ts} e @ Π {{Φ}} -∗ F e Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim [//] Hσ"). iIntros (?) "$". }
    iIntros (??) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (??) "Hσ HΦ".
    iSpecialize ("Hsim" with "[//] Hσ").
    iApply sim_gen_bind. iApply (sim_gen_wand with "Hsim").
    iIntros (??) "[[% [% [% [??]]]]|Hsim]".
    - iRight. iSplit!. iApply ("HΦ" with "[$] [//] [$]").
    - iLeft. iApply "Hsim". iSplit!. iIntros (??) "[% [% [% [? HF]]]]". subst.
      iApply ("HF" with "[//] [$] [$]").
Qed.

  Lemma sim_gen_expr_ctx e Π Φ :
    (ord_later_ctx -∗ WP{ts} e @ Π {{ Φ }}) -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iApply sim_gen_ctx. iIntros "?". iApply ("Hsim" with "[$] [//] [$]").
  Qed.

  Lemma fupd_sim_gen_expr e Π Φ :
    (|={∅}=> WP{ts} e @ Π {{ Φ }}) -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite sim_gen_expr_unfold.
    iIntros (???) "?". iApply fupd_sim_gen.
    iMod "Hsim". by iApply "Hsim".
  Qed.

  Global Instance elim_modal_fupd_sim_gen_expr p P e Π Φ :
    ElimModal True p false (|={∅}=> P) P (WP{ts} e @ Π {{ Φ }}) (WP{ts} e @ Π {{ Φ }}).
  Proof.
    iIntros (?) "[HP HT]". rewrite bi.intuitionistically_if_elim.
    iApply fupd_sim_gen_expr. iMod "HP". by iApply "HT".
  Qed.

  Global Instance elim_modal_bupd_sim_gen_expr p P e Π Φ :
    ElimModal True p false (|==> P) P (WP{ts} e @ Π {{ Φ }}) (WP{ts} e @ Π {{ Φ }}).
  Proof.
    iIntros (?) "[HP HT]". rewrite bi.intuitionistically_if_elim.
    iApply fupd_sim_gen_expr. iMod "HP". by iApply "HT".
  Qed.

  Global Instance is_except_0_fupd_sim_gen_expr e Π Φ : IsExcept0 (WP{ts} e @ Π {{ Φ }}).
  Proof. rewrite /IsExcept0. iIntros "?". iApply fupd_sim_gen_expr. by rewrite -except_0_fupd -fupd_intro. Qed.


  Lemma sim_gen_expr_stop e Π Φ :
    Φ e -∗ WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite sim_gen_expr_unfold. iIntros (???) "HF".
    iApply sim_gen_stop. iLeft. iSplit!; [done|]. iFrame.
  Qed.

  Lemma sim_gen_expr_steps_None e Π Φ :
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ -∗
          σ ≈{ ts, Λ }≈> (λ κ σ', ∃ e',
           ⌜κ = None⌝ ∗ ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ ∗
           mstate_interp Λ σ' ∗ WP{ts} e' @ Π {{Φ}})) -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iApply sim_gen_bind.
    iApply (sim_gen_wand with "[-]"). { by iApply "HΦ". }
    iIntros (??) "[% [% [% [? Hsim]]]]". iRight. iSplit!.
    rewrite sim_gen_expr_unfold. by iApply "Hsim".
  Qed.

  Lemma sim_gen_expr_steps e Π Φ :
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ -∗
          σ ≈{ ts, Λ }≈> (λ κ σ', switch_id ts Λ Π κ σ' (λ σ'',
             ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' ∗ WP{ts} e' @ Π {{Φ}}))) -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iApply (sim_gen_wand with "[-]"). { by iApply "HΦ". }
    iIntros (??) "?". iRight. done.
  Qed.

  Lemma sim_gen_expr_None e Π Φ :
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ -∗
          switch_id ts Λ Π None σ (λ σ'',
             ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' ∗ WP{ts} e' @ Π {{Φ}})) -∗
    WP{ts} e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply sim_gen_expr_steps. iIntros (???) "?".
    iApply sim_gen_stop. by iApply "HΦ".
  Qed.

  (* Lemma sim_gen_expr_None e os Π Φ : *)
  (*   (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os -∗ *)
  (*         handle_cont _ ts Π None σ (λ σ'', *)
  (*            ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' os ∗ WP{ts} e' @ ? os , Π {{Φ}})) -∗ *)
  (*   WP{ts} e @ ? os , Π {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "HΦ". iApply sim_gen_expr_steps. iIntros (???) "?". *)
  (*   iApply sim_gen_stop. by iApply "HΦ". *)
  (* Qed. *)
End sim_gen_expr.

(*
(** * [sim_tgt_expr] *)
Section sim_tgt.
  Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
  Implicit Types (e : mexpr Λ).

Lemma sim_tgt_expr_step e Φ Π os :
  (∀ K σ κ Pσ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ ⌜m_step Λ σ κ Pσ⌝ -∗ mstate_interp Λ σ os ={∅}=∗
    ∃ σ', ⌜Pσ σ'⌝ ∗ ((∀ os' e',
           ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ -∗
           mstate_interp Λ σ' os' -∗
           σ' ⤇ₜ λ Π', TGT e' @ ? os' [{ Π' }] {{ Φ }}) -∗
           ▷ₒ Π κ σ')) -∗
  TGT e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hsim" (?). iIntros "HΦ" (??) "#? Hσ".
  iApply sim_gen_step_end. iIntros (???). iMod ("Hsim" with "[//] [//] [$]") as (??) "Hsim".
  iModIntro. iExists _. iSplit; [done|].
  iSpecialize ("Hsim" with "[-]"); [|by do 2 iModIntro].
  iIntros (???) "?". iIntros (?) "Hsim". iApply (sim_gen_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.

End sim_tgt.

(** * [sim_src_expr] *)
Section sim_src.
Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
Implicit Types (e : mexpr Λ).

Lemma sim_src_expr_raw_step e Π os :
  (∀ σ, ⌜mexpr_rel Λ σ e⌝ -∗ mstate_interp Λ σ os ==∗
    ∃ κ Pσ, ⌜m_step Λ σ κ Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ if κ is Some _ then Π κ σ' else
       ∃ os' e', ⌜mexpr_rel Λ σ' e'⌝ ∗ mstate_interp Λ σ' os' ∗ SRC e' @ ? os' [{ Π }]) -∗
  SRC e @ ? os [{ Π }].
Proof.
  iIntros "HΠ" (σ ?) "#??". iApply fupd_sim_gen.
  iMod ("HΠ" with "[//] [$]") as (???) "HΠ". iModIntro.
  iApply sim_gen_step. iExists _, _. iSplit; [done|]. iIntros "!>" (??).
  iMod ("HΠ" with "[//]") as "HΠ". iModIntro. simpl. case_match; [iFrame|].
  iRight. iSplit; [done|]. iDestruct ("HΠ") as (???) "[? Hsim]".
  by iApply "Hsim".
Qed.

Lemma sim_src_expr_step_None e Π Φ os :
  (∀ K σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os ==∗
    ∃ Pσ, ⌜m_step Λ σ None Pσ⌝ ∗
     ∀ σ', ⌜Pσ σ'⌝ ={∅}=∗ ∃ os' e', ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ ∗
       mstate_interp Λ σ' os' ∗ SRC e' @ ? os' [{ Π }] {{ Φ }}) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "Hs" (?) "HΦ". iApply sim_src_expr_raw_step. iIntros (??) "?".
  iMod ("Hs" with "[//] [$]") as (??) "Hs". iModIntro. iExists _, _. iSplit; [done|].
  iIntros (??). iMod ("Hs" with "[//]") as (???) "[? Hs]". iModIntro. iExists _, _. iFrame. iSplit; [done|].
  by iApply "Hs".
Qed.

Lemma sim_src_expr_step e Φ Π os :
  (∀ K σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os ==∗
     ∃ κ' Pσ_s, ⌜m_step Λ σ κ' Pσ_s⌝ ∗
       ∀ σ', ⌜Pσ_s σ'⌝ ={∅}=∗
          ((∀ os' e',
              ⌜mexpr_rel Λ σ' (mfill Λ K e')⌝ -∗
              mstate_interp Λ σ' os' -∗
              σ' ⤇ₛ λ Π', SRC e' @ ? os' [{ Π' }] {{ Φ }}) -∗
          Π κ' σ')) -∗
  SRC e @ ? os [{ Π }] {{ Φ }}.
Proof.
  iIntros "He" (?). iIntros "HΦ" (??) "#? Hσ". iApply fupd_sim_gen.
  iMod ("He" with "[//] [$]") as (???) "Hsim". iModIntro.
  iApply sim_gen_step_end. iExists _, _. iSplit; [done|].
  iIntros "!>" (??). iMod ("Hsim" with "[//]") as "Hsim". iModIntro.
  iApply "Hsim". iIntros (???) "?". iIntros (?) "Hsim".
  iApply (sim_gen_expr_raw_elim with "[$]"); [done|].
  by iApply "Hsim".
Qed.
End sim_src.
*)
Global Opaque sim_gen_expr.

(* (** * [sim_expr_s] *) *)
(* Definition sim_expr_s `{!dimsumGS EV Σ Λ_t Λ_s} (q : Qp) (e : mexpr Λ_s) : iProp Σ := *)
(*   ghost_var dimsum_ghost_var_s_name q e. *)

(* Notation "'⤇{' q } e" := (sim_expr_s q e) *)
(*   (at level 20, format "'⤇{' q }  e") : bi_scope. *)
(* Notation "'⤇' e" := (sim_expr_s (1/2) e) *)
(*   (at level 20, format "'⤇'  e") : bi_scope. *)
(* Notation "'⤇?' e" := (if e is Some e' then sim_expr_s (1/2) e' else True)%I *)
(*   (at level 20, format "'⤇?'  e") : bi_scope. *)

(* Section sim_expr. *)
(*   Context `{!dimsumGS EV Σ Λ_t Λ_s}. *)

(*   Lemma sim_expr_s_agree e1 e2 : *)
(*     ⤇ e1 -∗ ⤇ e2 -∗ ⌜e1 = e2⌝. *)
(*   Proof. iIntros "??". by iDestruct (ghost_var_agree with "[$] [$]") as %->. Qed. *)

(*   Lemma sim_expr_s_update e' e1 e2 : *)
(*     ⤇ e1 -∗ ⤇ e2 ==∗ ⤇ e' ∗ ⤇ e'. *)
(*   Proof. iApply ghost_var_update_halves. Qed. *)
(* End sim_expr. *)


(*

TGT e init [{ λ κ, if κ in locle then locle ≈>ₜ ... else src ≈>ₛ λ κ', κ = κ' ... }]
----------------------------------------
memmove ≈>ₜ λ κ, if κ in locle then locle ≈>ₜ ... else src ≈>ₛ λ κ', κ = κ' ...
-----------------------
memmove + locle ≈>ₜ λ κ, src ≈>ₛ λ κ', κ = κ' ...
-----------------------
memmove + locle <= src


TGT Call locle [{ Π }] {{ λ e' Π', ∃ b, e' = ValBool b ∗ Π' = Π }}


TGT if b then ... else [{ Π }] {{ Φ }}
---------------------------------------------------
TGT Call locle [{ Π }] {{ λ e Π', TGT if e then ... else [{ Π' }] {{ Φ }} }}
---------------------------------------------------
TGT if Call locle then... else ... [{ Π }] {{ Φ }}


Left, (Call main vs, h), locle_prog ⪯ main_spec_prog
---------------------------------------------
None, (Waiting, ∅), locle_prog ⪯ main_spec_prog
----------------------------------------------
[main ∪r memmove]r +r [locle]s <= [main_spec]s



*)
