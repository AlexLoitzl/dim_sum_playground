From iris.bi Require Import fixpoint.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core Require Import nb_mod.
From dimsum.core.iris Require Export ord_later sim.
Set Default Proof Using "Type".

(** * mod_lang *)
Structure mod_lang EV Σ := ModLang {
  mexpr : Type;
  mstate : Type;
  mectx : Type;
  mfill : mectx → mexpr → mexpr;
  mcomp_ectx : mectx → mectx → mectx;
  mtrans :> mod_trans EV;
  mexpr_rel : mtrans.(m_state) → mexpr → Prop;
  mstate_interp : mtrans.(m_state) → option mstate → iProp Σ;
  mfill_comp K1 K2 e : mfill K1 (mfill K2 e) = mfill (mcomp_ectx K1 K2) e
}.
Global Arguments mexpr {_ _} _.
Global Arguments mstate {_ _} _.
Global Arguments mectx {_ _} _.
Global Arguments mfill {_ _} _.
Global Arguments mcomp_ectx {_ _} _.
Global Arguments mtrans {_ _} _.
Global Arguments mexpr_rel {_ _} _ _ _.
Global Arguments mstate_interp {_ _} _ _.

Record iModHandler Σ (S EV : Type) := {
  (* TODO: make this a coercion? *)
  imodhandle : option EV → S → (S → iProp Σ) → iProp Σ;
  imodhandle_mono κ σ C C' : imodhandle κ σ C -∗ (∀ σ', C σ' -∗ C' σ') -∗ imodhandle κ σ C';
}.
Global Arguments imodhandle {_ _ _}.

Global Instance imodhandle_ne Σ S EV (J : iModHandler Σ S EV) n:
  Proper ((=) ==> (=) ==> pointwise_relation S (dist n) ==> dist n) (imodhandle J).
Proof.
  move => ? κ -> ? σ -> ?? HC.
  have Heq : (∀ C, imodhandle J κ σ C ⊣⊢ ∃ C', (∀ σ', C' σ' -∗ C σ') ∗ imodhandle J κ σ C').
  - move => C. apply (anti_symm (⊢)).
    + iIntros "?". iExists _. iFrame. iIntros (?) "$".
    + iIntros "(%C'&?&?)". by iApply (imodhandle_mono with "[$]").
  - rewrite !Heq. by repeat f_equiv.
Qed.


Definition subMH {Σ S EV} (J1 J2 : iModHandler Σ S EV) : iProp Σ :=
  □ (∀ κ σ C, imodhandle J1 κ σ C -∗ imodhandle J2 κ σ C).

Class inMH {Σ S EV} (J1 : iModHandler Σ S EV) (J2 : iModHandler Σ S EV) :=
  is_inMH : ⊢ subMH J1 J2.

Global Hint Mode inMH + + + ! ! : typeclass_instances.

Lemma inMH_apply {Σ S EV} (J1 : iModHandler Σ S EV) {J2} (H : inMH J1 J2) κ σ C :
  imodhandle J1 κ σ C -∗
  imodhandle J2 κ σ C.
Proof. iIntros "?". by iApply (is_inMH (J1:=J1) (J2:=J2)). Qed.

Lemma subMH_trans Σ S EV (J1 J2 J3 : iModHandler Σ S EV) :
  subMH J1 J2 -∗ subMH J2 J3 -∗ subMH J1 J3.
Proof. iIntros "#H1 #H2" (???) "!> HJ". iApply "H2". by iApply "H1". Qed.


Global Program Instance iModHandler_union Σ S EV : Union (iModHandler Σ S EV) := λ J1 J2, {|
  imodhandle κ σ C := imodhandle J1 κ σ C ∨ imodhandle J2 κ σ C;
|}%I.
Next Obligation.
  iIntros (?????????) "[?|?] HC"; [iLeft|iRight]; by iApply (imodhandle_mono with "[$]").
Qed.

Lemma subMH_union_l Σ S EV (J1 J2 : iModHandler Σ S EV) :
  ⊢ subMH J1 (J1 ∪ J2).
Proof. iIntros "!>" (???) "HJ". by iLeft. Qed.

Lemma subMH_union_r Σ S EV (J1 J2 : iModHandler Σ S EV) :
  ⊢ subMH J2 (J1 ∪ J2).
Proof. iIntros "!>" (???) "HJ". by iRight. Qed.

Program Definition nopMH {Σ S EV} : iModHandler Σ S EV := {|
  imodhandle κ σ C := ⌜κ = None⌝ ∗ C σ;
|}%I.
Next Obligation. iIntros (???????) "[-> ?] HC". iSplit; [done|]. by iApply "HC". Qed.

Program Definition directMH {Σ EV} {Λ : mod_lang EV Σ} `{!dimsumGS Σ} ts Π : iModHandler Σ (Λ.(m_state)) EV := {|
  imodhandle κ σ C := (∀ σ', C σ' -∗ σ' ≈{ts, Λ}≈> Π) -∗ Π κ σ;
|}%I.
Next Obligation.
  iIntros (??????????) "HΠ HC". iIntros "Hw". iApply "HΠ". iIntros (?) "?".
  iApply "Hw". by iApply "HC".
Qed.


Program Definition sim_tgtMH {Σ EV} {m1 : mod_trans EV} `{!dimsumGS Σ}
  γσ_t γσ_s γκ m1_full Pκ m2 Π
  : iModHandler Σ (m1.(m_state)) EV := {|
  imodhandle κ σ C :=
     (∀ σ', C σ' -∗ σ' ≈{m1}≈>ₜ Π) -∗
        Pκ κ σ (λ σ_full : m_state m1_full, sim_tgt_constP (m_t:=m1_full) (m_s := m2) γσ_t γσ_s γκ κ σ_full) |}%I.
Next Obligation.
  iIntros (???????????????) "HΠ HC". iIntros "Hw". iApply "HΠ". iIntros (?) "?".
  iApply "Hw". by iApply "HC".
Qed.

(** * [sim_gen_expr] *)
Section sim_gen_expr.
  Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
  Context (ts : tgt_src).
  Implicit Types (e : mexpr Λ).

  (* TODO: Should one be able to change os during the WP? If so, it
  needs to be added to the postcondition. But it does not seem
  necessary, I guess one can use a variant of bind for that. *)
  (* TODO: Change this, to not assert the state interpretation on
  every step? That seems necessary to be able to go from @ ? None to @
  ? Some s. However, this would require splitting this definition into
  two (and break concurrent reasoning, but not sure that we care /
  that would be the point). *)
  Definition sim_gen_expr_pre (J : iModHandler Σ (m_state Λ) EV)
    (sim_gen_expr : leibnizO (mexpr Λ) -d> leibnizO (option (mstate Λ)) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ) :
    leibnizO (mexpr Λ) -d> leibnizO (option (mstate Λ)) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ := λ e os Φ,
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os -∗ |={∅}=> ((∃ e', ⌜mexpr_rel Λ σ (mfill Λ K e')⌝ ∗ mstate_interp Λ σ os ∗ Φ e') ∨
        σ ≈{ ts, Λ }≈> (λ κ σ', imodhandle J κ σ' (λ σ'',
         ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' os ∗ sim_gen_expr e' os Φ))))%I.

  Global Instance sim_gen_expr_pre_ne J n:
    Proper ((dist n ==> dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n ==> dist n) (sim_gen_expr_pre J).
  Proof.
    move => ?? Hsim ?? -> ?? -> ?? HΦ. rewrite /sim_gen_expr_pre.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
    move => ?? -> ?? ->.
    repeat (f_equiv || eapply Hsim || eapply HΦ || reflexivity).
  Qed.

  Lemma sim_gen_expr_pre_mono J sim1 sim2:
    ⊢ □ (∀ e os Φ, sim1 e os Φ -∗ sim2 e os Φ)
    → ∀ e os Φ, sim_gen_expr_pre J sim1 e os Φ -∗ sim_gen_expr_pre J sim2 e os Φ.
  Proof.
    iIntros "#Hinner" (e os Φ) "Hsim". iIntros (???) "?".
    iMod ("Hsim" with "[//] [$]") as "[?|Hsim]"; [by iLeft; iFrame| iRight; iModIntro].
    iApply (sim_gen_wand with "Hsim"). iIntros (??) "?". iApply (imodhandle_mono with "[$]").
    iIntros (?) "(%e'&?&?&?)". iExists _. iFrame. by iApply "Hinner".
  Qed.

  Local Instance sim_gen_expr_pre_monotone J :
    BiMonoPred (λ sim_gen_expr : prodO (prodO (leibnizO (mexpr Λ)) (leibnizO (option (mstate Λ)))) (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_gen_expr_pre J (curry3 sim_gen_expr))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([[??]?]) "Hsim" => /=.
      iApply sim_gen_expr_pre_mono; [|done].
      iIntros "!>" (???) "HΠ". by iApply ("Hinner" $! (_, _, _)).
    - move => sim_gen Hsim n [[σ1 os1] Φ1] [[σ2 os2] Φ2] /= [[/=??]?].
      apply sim_gen_expr_pre_ne; eauto. move => ????????? /=. by apply: Hsim.
  Qed.

  Definition sim_gen_expr J : mexpr Λ → option (mstate Λ) → (mexpr Λ → iProp Σ) → iProp Σ :=
    curry3 (bi_least_fixpoint (λ sim_gen_expr : prodO (prodO (leibnizO (mexpr Λ)) (leibnizO (option (mstate Λ)))) (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ, uncurry3 (sim_gen_expr_pre J (curry3 sim_gen_expr)))).

  Global Instance sim_gen_expr_ne J n:
    Proper ((=) ==> (=) ==> (pointwise_relation _ (dist n)) ==> dist n) (sim_gen_expr J).
  Proof. move => ?? -> ?? -> ?? HΦ. unfold sim_gen_expr. f_equiv. intros ?. by apply HΦ. Qed.
End sim_gen_expr.

Global Typeclasses Opaque sim_gen_expr.

Notation "'WP{' ts '}' e @ ? os , J {{ Φ } }" := (sim_gen_expr ts J e os Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'WP{' ts '}' e @ s , J {{ Φ } }" := (sim_gen_expr ts J e (Some s) Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'WP{' ts '}' e @ J {{ Φ } }" := (sim_gen_expr ts J e None Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'WP{' ts '}' e @ ? os , J {{ e' , Φ } }" := (sim_gen_expr ts J e os (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'WP{' ts '}'  e  '/' @  ?  os ,  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'WP{' ts '}' e @ s , J {{ e' , Φ } }" := (sim_gen_expr ts J e (Some s) (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'WP{' ts '}'  e  '/' @  s ,  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'WP{' ts '}' e @ J {{ e' , Φ } }" := (sim_gen_expr ts J e None (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'WP{' ts '}'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'TGT' e @ ? os , J {{ Φ } }" := (sim_gen_expr Tgt J e os Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'TGT' e @ s , J {{ Φ } }" := (sim_gen_expr Tgt J e (Some s) Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'TGT' e @ J {{ Φ } }" := (sim_gen_expr Tgt J e None Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'TGT' e @ ? os , J {{ e' , Φ } }" := (sim_gen_expr Tgt J e os (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  ?  os ,  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'TGT' e @ s , J {{ e' , Φ } }" := (sim_gen_expr Tgt J e (Some s) (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  s ,  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'TGT' e @ J {{ e' , Φ } }" := (sim_gen_expr Tgt J e None (λ e', Φ%I))
  (at level 70, Φ at level 200,
    format "'[hv' 'TGT'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Notation "'SRC' e @ ? os , J {{ Φ } }" := (sim_gen_expr Src J e os  Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'SRC' e @ s , J {{ Φ } }" := (sim_gen_expr Src J e (Some s) Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.
Notation "'SRC' e @ J {{ Φ } }" := (sim_gen_expr Src J e None Φ%I)
  (at level 70, Φ at level 200, only parsing) : bi_scope.

Notation "'SRC' e @ ? os , J {{ e' , Φ } }" := (sim_gen_expr Src J e os (λ e', Φ%I)) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  ?  os , J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'SRC' e @ s , J {{ e' , Φ } }" := (sim_gen_expr Src J e (Some s) (λ e', Φ%I)) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  s ,  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.
Notation "'SRC' e @ J {{ e' , Φ } }" := (sim_gen_expr Src J e None (λ e', Φ%I)) (at level 70, Φ at level 200,
  format "'[hv' 'SRC'  e  '/' @  J  {{  '[ ' e' ,  '/' Φ  ']' } } ']'") : bi_scope.

Section sim_gen_expr.
  Context {EV} {Σ} {Λ : mod_lang EV Σ} `{!dimsumGS Σ}.
  Context (ts : tgt_src).
  Implicit Types (e : mexpr Λ).

  Local Existing Instance sim_gen_expr_pre_monotone.
  Lemma sim_gen_expr_unfold e J os Φ:
    WP{ts} e @ ? os, J {{ Φ }} ⊣⊢ sim_gen_expr_pre ts J (sim_gen_expr ts J) e os Φ.
  Proof. rewrite /sim_gen_expr /curry3. apply: least_fixpoint_unfold. Qed.

  Lemma sim_gen_expr_strong_ind J (R: leibnizO (mexpr Λ) -d> leibnizO (option (mstate Λ)) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive3 R →
    ⊢ (□ ∀ e os Φ, sim_gen_expr_pre ts J (λ e os Φ, R e os Φ ∧ WP{ts} e @ ? os, J {{Φ}}) e os Φ -∗ R e os Φ)
      -∗ ∀ e os Φ, WP{ts} e @ ? os, J {{Φ}} -∗ R e os Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (e os Φ) "Hsim".
    rewrite {2}/sim_gen_expr {1}/curry3.
    iApply (least_fixpoint_ind _ (uncurry3 R) with "[] Hsim").
    iIntros "!>" ([[??]?]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_gen_expr_ind J (R: leibnizO (mexpr Λ) -d> leibnizO (option (mstate Λ)) -d> (leibnizO (mexpr Λ) -d> iPropO Σ) -d> iPropO Σ) :
    NonExpansive3 R →
    ⊢ (□ ∀ e os Φ, sim_gen_expr_pre ts J R e os Φ -∗ R e os Φ)
      -∗ ∀ e os Φ, WP{ts} e @ ? os, J {{ Φ }} -∗ R e os Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_gen_expr_strong_ind. iIntros "!>" (e os Φ) "Hsim".
    iApply "HPre". iApply (sim_gen_expr_pre_mono with "[] Hsim").
    iIntros "!>" (???) "[? _]". by iFrame.
  Qed.

  Lemma sim_gen_expr_wand e os J Φ Ψ :
    WP{ts} e @ ? os, J {{ Ψ }} -∗
    (∀ e', Ψ e' -∗ Φ e') -∗
    WP{ts} e @ ? os, J {{ Φ }}.
  Proof.
    iIntros "HWP Hwand".
    pose (F := (λ e os Ψ, ∀ Φ,
        (∀ e', Ψ e' -∗ Φ e') -∗
         WP{ts} e @ ? os, J {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ ? os, J {{Ψ}} -∗ F e os Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP"). iIntros (?) "?". by iApply "Hwand". }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (???) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_expr_unfold. iIntros (???) "?".
    iMod ("Hsim" with "[//] [$]") as "[[% [% [? HΦ]]]|Hsim]"; iModIntro.
    - iLeft. iExists _. iSplit; [done|]. iFrame. by iApply "Hc".
    - iRight. iApply (sim_gen_wand with "Hsim"). iIntros (? ?) "Hsim /=".
      iApply (imodhandle_mono with "Hsim"). iIntros (?) "(%e'&?&?&Hsim)". iExists _. iFrame.
      by iApply "Hsim".
  Qed.

  Lemma sim_gen_expr_bind K e os J Φ :
    WP{ts} e @ ? os, J {{ e', WP{ts} mfill Λ K e' @ ? os , J {{Φ}} }} -∗
    WP{ts} mfill Λ K e @ ? os, J {{ Φ }}.
  Proof.
    iIntros "HWP".
    pose (F := (λ e os' Ψ, ∀ Φ, ⌜os' = os⌝ -∗
        (∀ e', Ψ e' -∗ WP{ts} mfill Λ K e' @ ? os, J {{Φ}}) -∗
         WP{ts} mfill Λ K e @ ? os , J {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ ? os , J {{Ψ}} -∗ F e os Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP [//]"). iIntros (?) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (???) "Hsim". iIntros (? ?) "Hc". subst.
    rewrite sim_gen_expr_unfold. iIntros (?? Hf) "?". rewrite mfill_comp in Hf.
    iMod ("Hsim" with "[//] [$]") as "[[% [% [? HΦ]]]|Hsim]".
    - iSpecialize ("Hc" with "[$]"). rewrite sim_gen_expr_unfold.
      iDestruct ("Hc" with "[] [$]") as "?". { by rewrite mfill_comp. }
      done.
    - iModIntro. iRight. iApply (sim_gen_wand with "Hsim"). iIntros (??) "Hsim /=".
      iApply (imodhandle_mono with "Hsim"). iIntros (?) "(%e'&?&?&Hsim)". rewrite -mfill_comp.
      iExists _. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_gen_expr_bind0 e os J Φ :
    WP{ts} e @ ? os, J {{ e', WP{ts} e' @ ? os , J {{Φ}} }} -∗
    WP{ts} e @ ? os, J {{ Φ }}.
  Proof.
    iIntros "HWP".
    pose (F := (λ e os' Ψ, ∀ Φ, ⌜os' = os⌝ -∗
        (∀ e', Ψ e' -∗ WP{ts} e' @ ? os, J {{Φ}}) -∗
         WP{ts} e @ ? os , J {{Φ}})%I).
    iAssert (∀ Ψ, WP{ts} e @ ? os , J {{Ψ}} -∗ F e os Ψ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HWP [//]"). iIntros (?) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (???) "Hsim". iIntros (? ?) "Hc". subst.
    rewrite sim_gen_expr_unfold. iIntros (?? Hf) "?".
    iMod ("Hsim" with "[//] [$]") as "[[% [% [? HΦ]]]|Hsim]".
    - iSpecialize ("Hc" with "[$]"). rewrite sim_gen_expr_unfold.
      iDestruct ("Hc" with "[] [$]") as "?". { done. }
      done.
    - iModIntro. iRight. iApply (sim_gen_wand with "Hsim"). iIntros (??) "Hsim /=".
      iApply (imodhandle_mono with "Hsim"). iIntros (?) "(%e'&?&?&Hsim)".
      iExists _. iFrame. by iApply "Hsim".
  Qed.

  Lemma sim_gen_expr_handler_wand J1 J2 e os Φ :
    WP{ts} e @ ? os, J1 {{ Φ }} -∗
    subMH J1 J2 -∗
    WP{ts} e @ ? os, J2 {{ Φ }}.
  Proof.
    iIntros "HWP #Hwand".
    pose (F := (λ e os Φ, WP{ts} e @ ? os, J2 {{Φ}})%I).
    iAssert (WP{ts} e @ ? os, J1 {{Φ}} -∗ F e os Φ)%I as "Hgen"; last first.
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

  Definition direct_post (K : mectx Λ) (os : option (mstate Λ)) (Π : option EV → m_state Λ → iProp Σ) (e : mexpr Λ) : iProp Σ :=
    ∀ σ', ⌜mexpr_rel Λ σ' (mfill Λ K e)⌝ -∗ mstate_interp Λ σ' os -∗ σ' ≈{ts, Λ}≈> Π.

  (* Be careful when choosing Π when applying this rule, it must never change! *)
  Lemma sim_gen_expr_intro K e os Π σ :
    mexpr_rel Λ σ (mfill Λ K e) →
    mstate_interp Λ σ os -∗
    WP{ts} e @ ? os, directMH ts Π {{ direct_post K os Π }} -∗
    σ ≈{ts, Λ}≈> Π.
  Proof.
    iIntros (?) "Hσ Hsim".
    pose (F := (λ e os' Ψ, ∀ σ, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ ⌜os' = os⌝ -∗ mstate_interp Λ σ os -∗
       (∀ e', Ψ e' -∗ direct_post K os Π e') -∗
       σ ≈{ ts, Λ }≈> Π)%I).
    iAssert (∀ e Φ, WP{ts} e @ ? os, directMH ts Π {{Φ}} -∗ F e os Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim [//] [//] Hσ"). iIntros (?) "$". }
    iIntros (??) "Hsim".
    iApply (sim_gen_expr_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (???) "Hsim". iIntros (???) "Hσ HΦ". subst.
    iApply fupd_sim_gen.
    iDestruct ("Hsim" with "[//] Hσ") as ">[[% [% [Hσ Hsim]]]|Hsim]"; iModIntro.
    { by iApply ("HΦ" with "Hsim [//] Hσ"). }
    iApply (sim_gen_wand with "Hsim"). iIntros (κ σ1) "Hhandler".
    iApply "Hhandler". iIntros (?) "[%e'[%[? HF]]]". iApply ("HF" with "[//] [//] [$] [$]").
  Qed.

  Lemma sim_gen_expr_ctx e J os Φ :
    (ord_later_ctx -∗ WP{ts} e @ ? os, J {{ Φ }}) -∗
    WP{ts} e @ ? os, J {{ Φ }}.
  Proof. Admitted.

  Lemma fupd_sim_gen_expr e os J Φ :
    (|={∅}=> WP{ts} e @ ? os, J {{ Φ }}) -∗
    WP{ts} e @ ? os, J {{ Φ }}.
  Proof. iIntros "Hsim". rewrite sim_gen_expr_unfold. by iMod "Hsim". Qed.

  Lemma sim_gen_expr_end e J os Φ :
    Φ e -∗ WP{ts} e @ ? os , J {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite sim_gen_expr_unfold. iIntros (??) "HF ?".
    iModIntro. iLeft. iExists _. iSplit; [done|]. iFrame.
  Qed.

  Lemma sim_gen_expr_steps e os J Φ :
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os -∗
          σ ≈{ ts, Λ }≈> (λ κ σ', imodhandle J κ σ' (λ σ'',
             ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' os ∗ WP{ts} e' @ ? os , J {{Φ}}))) -∗
    WP{ts} e @ ? os , J {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite sim_gen_expr_unfold. iIntros (???) "? !>". iRight.
    iApply (sim_gen_wand with "[-]"). { by iApply "HΦ". } by iIntros (??) "?".
  Qed.

  Lemma sim_gen_expr_None e os J Φ :
    (∀ σ K, ⌜mexpr_rel Λ σ (mfill Λ K e)⌝ -∗ mstate_interp Λ σ os -∗
          imodhandle J None σ (λ σ'',
             ∃ e', ⌜mexpr_rel Λ σ'' (mfill Λ K e')⌝ ∗ mstate_interp Λ σ'' os ∗ WP{ts} e' @ ? os , J {{Φ}})) -∗
    WP{ts} e @ ? os , J {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply sim_gen_expr_steps. iIntros (???) "?".
    iApply sim_gen_stop. by iApply "HΦ".
  Qed.
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
