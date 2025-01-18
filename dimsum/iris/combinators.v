From dimsum.core Require Import product seq_product state_transform prepost link.
From dimsum.core.iris Require Import sat.
From dimsum.core.iris Require Export sim.
Set Default Proof Using "Type".

(** * map_mod *)

Section map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (f : map_mod_fn EV1 EV2 S).

  Lemma sim_tgt_map m f σ σf Π :
    (σ ≈{m}≈>ₜ λ κ σ',
      ∀ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ -∗
         Π κ' (σ', (σf', ok))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m }≈>ₜ X)%I).
    iApply (sim_gen_include (map_trans _ _) (λ σ, (σ, (σf, true))) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "HΠ".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[HP| Hs]". {
      iModIntro. iApply (sim_gen_stop with "[-]"). by iApply ("HΠ" with "HP").
    }
    iModIntro. iApply (sim_gen_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    all: iMod ("Hs" with "[//]") as (??) "Hs"; iModIntro; iExists (_, _); iSplit!; [done|].
    all: iModIntro; iMod "Hs"; iModIntro.
    - do 2 case_match; simplify_eq/=. iRight. iSplit!. by iApply "Hs".
    - iLeft. by iApply ("HΠ" with "Hs").
  Qed.

  Lemma sim_src_map m f σ σf Π `{!VisNoAng m} :
    (σ ≈{m}≈>ₛ λ κ σ',
      ∃ κ' σf' ok, ⌜if κ is Some e then f σf e κ' σf' ok else κ' = None ∧ σf' = σf ∧ ok = true⌝ ∗
         Π κ' (σ', (σf', ok))) -∗
    (σ, (σf, true)) ≈{map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m }≈>ₛ X)%I).
    iApply (sim_gen_include (map_trans _ _) (λ σ, (σ, (σf, true))) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[?| [%κ [% [% Hs]]] ]". {
      iModIntro. iApply (sim_gen_stop with "[-]").
      iDestruct ("Hc" with "[$]") as (???[?[??]]) "Hc". by simplify_eq.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σ'' ?].
      iMod ("Hs" with "[%]") as ">Hs"; [naive_solver|]. iModIntro.
      iDestruct ("Hc" with "[$]") as (????) "Hs". simplify_eq/=.
      iApply (sim_gen_step_end with "[-]"). iExists _, _ => /=. iSplit; [iPureIntro|].
      { econs. { apply: ProductStepBoth; [done|]. by econs. } done. }
      iModIntro. iIntros ([σ' ?] [??]) "!>". have ? : σ' = σ'' by naive_solver. by simplify_eq.
    - iModIntro. iApply (sim_gen_step with "[-]"). iExists _, _ => /=. iSplit; [iPureIntro|].
      { econs; [by econs|done]. }
      iModIntro. iIntros ([??][??]). simplify_eq. iMod ("Hs" with "[//]") as ">HF". iModIntro.
      iRight. iSplit!. by iApply "HF".
  Qed.

  Lemma sim_src_map_ub m f σ σf Π `{!VisNoAng m} :
    ⊢ (σ, (σf, false)) ≈{map_trans m f}≈>ₛ Π.
  Proof.
    iStartProof. iApply sim_gen_step. iExists _, _. iSplit; [iPureIntro|].
    { econs. { by apply: ProductStepR; econs. } done. }
    iIntros "!>" ([??] [??]). done.
  Qed.
End map.

(** * seq_product *)

Section seq_product.
  Context {Σ : gFunctors} {EV1 EV2 : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_seq_product_None (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (∀ p, ▷ₒ Π (Some (SPENone p)) (p, σ1, σ2)) -∗
    (None, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply (sim_gen_step_end with "[-]"). iIntros (???). inv_all/= @m_step. iSpecialize ("HΠ" $! _).
    iModIntro. iSplit!. do 2 iModIntro. done.
  Qed.

  Lemma sim_tgt_seq_product_left (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (σ1 ≈{m1}≈>ₜ λ κ σ',
      ∀ s', ⌜if κ is None then s' = Some SPLeft else True⌝ -∗
         Π ((λ e, SPELeft e s') <$> κ) (s', σ', σ2)) -∗
    (Some SPLeft, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m1 }≈>ₜ X)%I).
    iApply (sim_gen_include (seq_product_trans m1 m2) (λ σ1, (Some SPLeft, σ1, σ2)) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[HP| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      by iApply (sim_gen_stop with "[-]").
    }
    iModIntro. iApply (sim_gen_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    iMod ("Hs" with "[//]") as (??) "Hs"; iModIntro.
    iExists (_, _, _). iSplit!; [done|]. iModIntro.
    iMod "Hs". iModIntro. case_match; simplify_eq/=.
    - iLeft. by iApply ("Hc" with "Hs").
    - iRight. iSplit!. iApply ("Hs" with "Hc").
  Qed.

  Lemma sim_tgt_seq_product_right (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    (σ2 ≈{m2}≈>ₜ λ κ σ',
      ∀ s', ⌜if κ is None then s' = Some SPRight else True⌝ -∗
         Π ((λ e, SPERight e s') <$> κ) (s', σ1, σ')) -∗
    (Some SPRight, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m2 }≈>ₜ X)%I).
    iApply (sim_gen_include (seq_product_trans m1 m2) (λ σ2, (Some SPRight, σ1, σ2)) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[HP| Hs ]". {
      iModIntro. iDestruct ("Hc" with "[$] [//]") as "Hc".
      by iApply (sim_gen_stop with "[-]").
    }
    iModIntro. iApply (sim_gen_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    iMod ("Hs" with "[//]") as (??) "Hs"; iModIntro.
    iExists (_, _, _). iSplit!; [done|]. iModIntro.
    iMod "Hs". iModIntro. case_match; simplify_eq/=.
    - iLeft. by iApply ("Hc" with "Hs").
    - iRight. iSplit!. iApply ("Hs" with "Hc").
  Qed.

  Lemma sim_src_seq_product_None p (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π :
    Π (Some (SPENone p)) (p, σ1, σ2) -∗
    (None, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "HΠ". iApply (sim_gen_step_end with "[-]"). iExists _,_.
    iSplit; [iPureIntro; by econs|].
    iIntros "!>" (??) "!>". by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_product_left (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π `{!VisNoAng m1} :
    (σ1 ≈{m1}≈>ₛ λ κ σ', ∃ s', ⌜if κ is None then s' = Some SPLeft else True⌝ ∗
       Π ((λ e, SPELeft e s') <$> κ) (s', σ', σ2)) -∗
    (Some SPLeft, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m1 }≈>ₛ X)%I).
    iApply (sim_gen_include (seq_product_trans m1 m2) (λ σ1, (Some SPLeft, σ1, σ2)) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[?| [%κ [% [% Hsim]]] ]". {
      iModIntro. iDestruct ("Hc" with "[$]") as (??) "Hc".
      iApply (sim_gen_stop with "[-]"). by simplify_eq/=.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σs1 ?].
      iMod ("Hsim" with "[%]") as ">Hsim"; [naive_solver|]. iModIntro => /=.
      iDestruct ("Hc" with "[$]") as (s ?) "?".
      iApply (sim_gen_step with "[-]"). iExists _, _. iSplit.
      { iPureIntro. by apply: (SPLeftS _ _ _ _ _ s). }
      iIntros "!>" ([[? σs2]?] [?[??]]) "!>". iLeft. have ? : σs1 = σs2 by naive_solver. by simplify_eq/=.
    - iModIntro. iApply (sim_gen_step with "[-]"). iExists _, _. iSplit.
      { iPureIntro. by econs. }
      iIntros "!>" ([[??] ?] [?[??]]). simplify_eq. iRight.
      iMod ("Hsim" with "[//]") as ">Hsim". iModIntro. simplify_eq/=. iSplit!. by iApply "Hsim".
  Qed.

  Lemma sim_src_seq_product_right (m1 : mod_trans EV1) (m2 : mod_trans EV2) σ1 σ2 Π `{!VisNoAng m2} :
    (σ2 ≈{m2}≈>ₛ λ κ σ', ∃ s', ⌜if κ is None then s' = Some SPRight else True⌝ ∗
       Π ((λ e, SPERight e s') <$> κ) (s', σ1, σ')) -∗
    (Some SPRight, σ1, σ2) ≈{seq_product_trans m1 m2}≈>ₛ Π.
  Proof.
    iIntros "Hsim".
    set Π' := (X in (_ ≈{ m2 }≈>ₛ X)%I).
    iApply (sim_gen_include (seq_product_trans m1 m2) (λ σ2, (Some SPRight, σ1, σ2)) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[?| [%κ [% [% Hsim]]] ]". {
      iModIntro. iDestruct ("Hc" with "[$]") as (??) "Hc".
      iApply (sim_gen_stop with "[-]"). by simplify_eq/=.
    }
    destruct κ.
    - exploit vis_no_all; [done|] => -[σs1 ?].
      iMod ("Hsim" with "[%]") as ">Hsim"; [naive_solver|]. iModIntro => /=.
      iDestruct ("Hc" with "[$]") as (s ?) "?".
      iApply (sim_gen_step with "[-]"). iExists _, _. iSplit.
      { iPureIntro. by apply: (SPRightS _ _ _ _ _ s). }
      iIntros "!>" ([[? ?]σs2] [?[??]]) "!>". iLeft. have ? : σs1 = σs2 by naive_solver. by simplify_eq/=.
    - iModIntro. iApply (sim_gen_step with "[-]"). iExists _, _. iSplit.
      { iPureIntro. by econs. }
      iIntros "!>" ([[??] ?] [?[??]]). simplify_eq. iRight.
      iMod ("Hsim" with "[//]") as ">Hsim". iModIntro. simplify_eq/=. iSplit!. by iApply "Hsim".
  Qed.
End seq_product.

(** * state_transform_mod *)

Section state_transform.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.

  Lemma sim_tgt_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π `{!StateTransformWf m R} :
   R σ σ' →
   (σ' ≈{m}≈>ₜ λ κ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
    σ ≈{state_transform_trans m R}≈>ₜ Π.
  Proof.
    destruct StateTransformWf0 as [Heq HRstep].
    iIntros (HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ σ'', Π' κ σ'' -∗ ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
                   σ ≈{state_transform_trans m R}≈>ₜ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₜ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[HP| Hs]". {
      iModIntro. iApply (sim_gen_stop with "[-]"). by iApply ("Hc" with "HP").
    }
    iModIntro. iApply (sim_gen_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    have ?: σ' = σ'0 by naive_solver. subst.
    iMod ("Hs" with "[//]") as (??) "Hs"; iModIntro; simplify_eq/=.
    exploit HRstep; [done..|] => -[??].
    iExists _. iSplit!; [|done|]; [done|].
    iMod "Hs". iMod "Hs". iModIntro.
    case_match.
    - iLeft. by iApply ("Hc" with "Hs").
    - iRight. iSplit!. by iApply ("Hs" with "[]").
  Qed.

  Lemma sim_src_state_transform (m : mod_trans EV) σ' (R : S → m.(m_state) → Prop) σ Π :
   R σ σ' →
   (σ' ≈{m}≈>ₛ λ κ σ'', ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
    σ ≈{state_transform_trans m R}≈>ₛ Π.
  Proof.
    iIntros (HR) "Hsim".
    pose (F := (λ σ' Π', ∀ σ,
                   ⌜R σ σ'⌝ -∗
                   (∀ κ σ'', Π' κ σ'' -∗ ∀ σ''', ⌜R σ''' σ''⌝ -∗ Π κ σ''') -∗
                   σ ≈{state_transform_trans m R}≈>ₛ Π)%I).
    iAssert (∀ Π, σ' ≈{ m }≈>ₛ Π -∗ F σ' Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"); [done|]. iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    clear σ' σ HR. iIntros "!>" (σ'?) "Hsim". iIntros (σ HR) "Hc".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim") as "[?| [% [% [% Hs]]] ]". {
      iModIntro. iApply (sim_gen_stop with "[-]"). by iApply ("Hc" with "[$]").
    }
    iModIntro. iApply (sim_gen_step with "[-]").
    iExists _, _. iSplit; [iPureIntro; by econs|].
    iIntros "!>" (? [?[??]]). iMod ("Hs" with "[//]") as ">Hs". iModIntro.
    case_match.
    - iLeft. by iApply ("Hc" with "Hs").
    - iRight. iSplit!. by iApply ("Hs" with "[//]").
  Qed.
End state_transform.

(** * seq_map *)

Section seq_map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} `{!dimsumGS Σ}.
  Implicit Types (f : mod_trans (sm_event EV1 EV2)).

  Lemma sim_tgt_seq_map_filter m f σ σf Π :
    (σf ≈{f}≈>ₜ λ κ x,
      match κ with
      | None => Π None (SMFilter, σ, x)
      | Some (SMEEmit e) => Π (Some e) (SMFilter, σ, x)
      | Some (SMEReturn e) => Π None (if e is Some e' then SMProgRecv e' else SMProg, σ, x)
      | _ => True
      end) -∗
    (SMFilter, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_right with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    all: by iIntros ([[??]?]?); simplify_eq.
  Qed.

  Lemma sim_tgt_seq_map_filter_recv m f σ σf e Π :
    (σf ≈{f}≈>ₜ λ κ x,
      if κ is Some e' then ⌜SMERecv e = e'⌝ -∗ Π None (SMFilter, σ, x)
      else Π None (SMFilterRecv e, σ, x)
      ) -∗
    (SMFilterRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_right with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    1: iSpecialize ("Hκ" with "[//]").
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_tgt_seq_map_prog m f σ σf Π :
    (σ ≈{m}≈>ₜ λ κ x,
      if κ is Some e' then Π None (SMFilterRecv e', x, σf)
      else Π None (SMProg, x, σf)
    ) -∗
    (SMProg, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_left with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_tgt_seq_map_prog_recv m f σ σf e Π :
    (σ ≈{m}≈>ₜ λ κ x,
      if κ is Some e' then ⌜e = e'⌝ -∗ Π None (SMProg, x, σf)
      else Π None (SMProgRecv e, x, σf)
      ) -∗
    (SMProgRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply (sim_tgt_seq_product_left with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ Pσ) "Hκ". iIntros (s' ? κ' ???).
    destruct κ; destruct!/=; [inv_all @seq_map_filter|].
    1: iSpecialize ("Hκ" with "[//]").
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_filter m f σ σf Π `{!VisNoAng m} `{!VisNoAng f} :
    (σf ≈{f}≈>ₛ λ κ σf',
      match κ with
      | None => Π None (SMFilter, σ, σf')
      | Some (SMEEmit e) => Π (Some e) (SMFilter, σ, σf')
      | Some (SMEReturn e) => Π None (if e is Some e' then SMProgRecv e' else SMProg, σ, σf')
      | _ => False
      end) -∗
    (SMFilter, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_right with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_filter_recv m f σ σf Π e `{!VisNoAng m} `{!VisNoAng f} :
    (σf ≈{f}≈>ₛ λ κ σf',
      if κ is Some e' then ⌜SMERecv e = e'⌝ ∗ Π None (SMFilter, σ, σf')
      else Π None (SMFilterRecv e, σ, σf')
    ) -∗
    (SMFilterRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_right with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; iDestruct!; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_prog m f σ σf Π `{!VisNoAng m} `{!VisNoAng f} :
    (σ ≈{m}≈>ₛ λ κ σ',
      if κ is Some e' then Π None (SMFilterRecv e', σ', σf)
      else Π None (SMProg, σ', σf)) -∗
    (SMProg, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_left with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.

  Lemma sim_src_seq_map_prog_recv m f σ σf Π e `{!VisNoAng m} `{!VisNoAng f} :
    (σ ≈{m}≈>ₛ λ κ σ',
      if κ is Some e' then ⌜e = e'⌝ ∗ Π None (SMProg, σ', σf)
      else Π None (SMProgRecv e, σ', σf)
    ) -∗
    (SMProgRecv e, σ, σf) ≈{seq_map_trans m f}≈>ₛ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_src_state_transform; [done|] => /=.
    iApply (sim_src_map with "[-]").
    iApply (sim_src_seq_product_left with "[-]").
    iApply (sim_gen_wand with "HΠ").
    iIntros (κ σ') "Hκ".
    repeat case_match => //; iDestruct!; simplify_eq.
    all: iSplit!; (once try econs).
    all: iIntros ([[??]?] ?); by simplify_eq/=.
  Qed.
End seq_map.

(** * prepost *)

Section prepost.
  Context {Σ : gFunctors} `{!dimsumGS Σ}.
  Context {EV1 EV2 S : Type}.
  Context {M : ucmra} `{!Shrink M} `{!satG Σ M} `{!CmraDiscrete M} `{!∀ x : M, CoreCancelable x}.
  Implicit Types (i : EV2 → S → prepost (EV1 * S) M) (o : EV1 → S → prepost (EV2 * S) M).

  Lemma sim_tgt_prepost_Outside i o m s σ x Π :
    (∀ e, ▷ₒ Π (Some e) (SMFilter, σ, (PPRecv1 e, s, x))) -∗
    (SMFilter, σ, (PPOutside, s, x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_gen_step_end with "[-]"). iIntros (???). inv_all/= @m_step. iSpecialize ("HΠ" $! _).
    iModIntro. iSplit!. by do 2 iModIntro.
  Qed.

  Lemma sim_tgt_prepost_Recv1 i o m s σ x Π e γ :
    (∃ r y, ⌜pp_to_ex (i e s) (λ r' y', r = r' ∧ y = y')⌝ ∗
        |==> sat_open γ ∗ sat γ (x ∗ y) ∗
           ∀ x', sat_closed γ false x' -∗ Π None (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x'))) -∗
    (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof using Type*.
    iIntros "HΠ".
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_gen_step with "[-]"). iIntros (???). inv_all/= @m_step.
    iDestruct "HΠ" as (???) ">[? [? HΠ]]".
    iDestruct (sat_close with "[$] [$]") as (??) "?".
    iModIntro. iSplit!. {
      apply: pp_to_ex_mono; [done|]. move => ?? [??]; simplify_eq. split!.
      by rewrite assoc uPred_expand_shrink.
    }
    do 2 iModIntro. iRight. iSplit!.
    iApply (sim_gen_step_end with "[-]"). iIntros (???). inv_all/= @m_step.
    iModIntro. iSplit!. do 2 iModIntro. by iApply "HΠ".
  Qed.

  Lemma sim_tgt_prepost_Inside i o m s σ x Π e γ b :
    (sat_closed γ b x ∗ ∀ r y x', ⌜pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y)⌝ -∗
       sat_open γ -∗ sat γ (if b then x ∗ y else y) -∗ sat γ x' -∗
        ▷ₒ Π (Some r.1) (SMFilter, σ, (PPOutside, r.2, uPred_shrink x'))) -∗
    (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₜ Π.
  Proof using Type*.
    iIntros "[Hclosed HΠ]".
    iApply (sim_gen_bind with "[-]").
    iApply (sim_tgt_seq_map_filter_recv with "[-]").
    iApply (sim_gen_step_end with "[-]"). iIntros (???). inv_all/= @m_step.
    iModIntro. iSplit!. iIntros "!>!>" (?). iRight. iSplit!.
    iApply (sim_tgt_seq_map_filter with "[-]").
    iApply (sim_gen_step with "[-]"). iIntros (???). inv_all/= @m_step.
    revert select (satisfiable _). rewrite uPred_expand_shrink assoc => ?.
    iMod ("Hclosed" with "[//]") as "[Ha Hsat]".
    iAssert (sat γ (if b then x ∗ y else y) ∗ sat γ x')%I with "[Hsat]" as "[??]".
    { destruct b; rewrite !sat_sep; iDestruct!; iFrame. }
    iSpecialize ("HΠ" with "[//] [$] [$] [$]").
    iModIntro. iSplit!. do 2 iModIntro. iRight. iSplit!.
    iApply (sim_gen_step with "[-]"). iIntros (???). inv_all/= @m_step.
    iModIntro. iSplit!. do 2 iModIntro. by iLeft.
  Qed.

  Lemma sim_src_prepost_Outside i o m s σ x Π `{!VisNoAng m}:
    (∃ e, Π (Some e) (SMFilter, σ, (PPRecv1 e, s, x))) -∗
    (SMFilter, σ, (PPOutside, s, x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof.
    iIntros "[% HΠ]".
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_gen_step_end with "[-]").
    iExists _, _. iSplit; [iPureIntro; by econs|].
    iIntros "!>" ([[??]?] ?). simplify_eq/=. by iModIntro.
  Qed.

  Lemma sim_src_prepost_Recv1 i o m s σ x Π e γ b `{!VisNoAng m}:
    (sat_closed γ b x ∗ ∀ r y x', ⌜pp_to_ex (i e s) (λ r' y', r' = r ∧ y' = y)⌝ -∗
           sat_open γ -∗ sat γ (if b then x ∗ y else y) -∗ sat γ x' -∗
           Π None (SMProgRecv r.1, σ, (PPInside, r.2, uPred_shrink x'))) -∗
    (SMFilter, σ, (PPRecv1 e, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof using Type*.
    iIntros "[Hclosed HΠ]".
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_gen_step with "[-]"). iExists _, _. iSplit; [iPureIntro; econs|].
    iIntros "!>" ([[??]?] [?[y[[x' [Hsat ?]]?]]]%pp_to_ex_exists). simplify_eq/=.
    rewrite uPred_expand_shrink in Hsat.
    iMod ("Hclosed" with "[%]") as "[Ha Hsat]". { by rewrite comm. }
    iAssert (sat γ (if b then x ∗ y else y) ∗ sat γ x')%I with "[Hsat]" as "[??]".
    { destruct b; rewrite !sat_sep; iDestruct!; iFrame. }
    iModIntro. iRight. iSplit!. iApply (sim_gen_step with "[-]").
    iExists _, _. iSplit; [iPureIntro; econs|]. simplify_eq/=.
    iIntros "!>" ([[??]?] ?). iModIntro. iLeft. simplify_eq/=.
    iApply ("HΠ" with "[//] [$] [$] [$]").
  Qed.

  Lemma sim_src_prepost_Inside i o m s σ x Π e γ `{!VisNoAng m} :
    (∃ r y, ⌜pp_to_ex (o e s) (λ r' y', r' = r ∧ y' = y)⌝ ∗
       |==> sat_open γ ∗ sat γ (x ∗ y) ∗
        ∀ x', sat_closed γ false x' -∗ Π (Some r.1) (SMFilter, σ, (PPOutside, r.2, uPred_shrink x'))) -∗
    (SMFilterRecv e, σ, (PPInside, s, uPred_shrink x)) ≈{prepost_trans i o m}≈>ₛ Π.
  Proof using Type*.
    iIntros "HΠ".
    iApply (sim_gen_bind with "[-]").
    iApply (sim_src_seq_map_filter_recv with "[-]").
    iApply (sim_gen_step_end with "[-]"). iExists _, _. iSplit; [iPureIntro; econs|].
    iIntros "!>" ([[??]?]?). simplify_eq/=.
    iDestruct "HΠ" as (???) ">[? [? HΠ]]".
    iDestruct (sat_close with "[$] [$]") as (? Hsat ) "?".
    iModIntro. iSplit!. iRight. iSplit!.
    iApply (sim_src_seq_map_filter with "[-]").
    iApply (sim_gen_step with "[-]"). iExists _, _. iSplit.
    { iPureIntro. econs; [|done]. by rewrite uPred_expand_shrink comm (comm _ _ x). }
    iIntros "!>" ([[??]?] ?). simplify_eq/=. iModIntro. iRight. iSplit!.
    iApply (sim_gen_step with "[-]"). iExists _, _. iSplit. { iPureIntro. econs. }
    iIntros "!>" ([[??]?] ?). simplify_eq/=. iModIntro. iLeft.
    iApply ("HΠ" with "[$]").
  Qed.
End prepost.

(** * link *)
(* TODO: Add rules for src *)

Section link.
  Context {Σ : gFunctors} {EV : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (R : seq_product_case → S → EV → seq_product_case → S → EV → bool → Prop).

  Lemma sim_tgt_link_None R m1 m2 s σ1 σ2 Π :
    ▷ₒ (∀ e p' s' e' ok,
        ⌜R None s e p' s' e' ok⌝ -∗
        Π (Some (Incoming, e')) (link_to_case ok p' e', s', σ1, σ2)) -∗
    (MLFRun None, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "HΠ".
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_None. iIntros (p) "!>". iIntros (????).
    inv_all @link_filter.
    iIntros ([[[??]?]?] ?); simplify_eq/=. repeat (case_match; simplify_eq/=).
    all: iApply ("HΠ" with "[//]").
  Qed.

  Definition link_tgt_leftP R {m1 m2 : mod_trans (io_event EV)}
    (Π : option (io_event EV) → link_case EV * S * m_state m1 * m_state m2 → iProp Σ)
    (s : S) (σ2 : m_state m2) : option (io_event EV) → m_state m1 → iProp Σ :=
    λ κ σ1', match κ with
             | None => Π None (MLFRun (Some SPLeft), s, σ1', σ2)
             | Some e => ∀ p' s' e' ok, ⌜R (Some SPLeft) s e.2 p' s' e' ok⌝ -∗ ⌜e.1 = Outgoing⌝ -∗
                 if p' is None then
                   Π (Some (Outgoing, e')) (link_to_case ok p' e', s', σ1', σ2)
                 else
                   (link_to_case ok p' e', s', σ1', σ2) ≈{link_trans R m1 m2}≈>ₜ Π
             end%I.

  Lemma sim_tgt_link_left R m1 m2 s σ1 σ2 Π :
    σ1 ≈{m1}≈>ₜ link_tgt_leftP R Π s σ2 -∗
    (MLFRun (Some SPLeft), s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_gen_bind with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_gen_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter. iSpecialize ("Hsim" $! s'). case_match.
      + iIntros ([[[??]?]?] ?). simplify_eq/=. iRight. iSplit!.
        repeat case_match => //; simplify_eq/=.
        all: iApply ("Hsim" with "[//] [//]").
      + iIntros ([[[??]?]?] ?). simplify_eq/=. iLeft.
        repeat case_match => //; simplify_eq/=.
        all: iApply ("Hsim" with "[//] [//]").
    - iIntros ([[[??]?]?] ?). simplify_eq/=. by iLeft.
  Qed.

  Lemma sim_tgt_link_left_recv R m1 m2 s σ1 σ2 Π e :
    (σ1 ≈{m1}≈>ₜ λ κ σ1',
      match κ with
      | None => Π None (MLFRecv SPLeft e, s, σ1', σ2)
      | Some e' => ⌜e' = (Incoming, e)⌝ -∗ (MLFRun (Some SPLeft), s, σ1', σ2) ≈{link_trans R m1 m2}≈>ₜ Π
      end%I) -∗
    (MLFRecv SPLeft e, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_gen_bind with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_left.
    iApply (sim_gen_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????).
    iIntros ([[[??]?]?]?). simplify_eq/=. destruct κ; destruct!/=.
    - inv_all @link_filter. iRight. iSplit!. by iApply "Hsim".
    - by iLeft.
  Qed.

  Definition link_tgt_rightP R {m1 m2 : mod_trans (io_event EV)}
    (Π : option (io_event EV) → link_case EV * S * m_state m1 * m_state m2 → iProp Σ)
    (s : S) (σ1 : m_state m1)
    : option (io_event EV) → m_state m2 → iProp Σ :=
    λ κ σ2',
      match κ with
      | None => Π None (MLFRun (Some SPRight), s, σ1, σ2')
      | Some e => ∀ p' s' e' ok, ⌜R (Some SPRight) s e.2 p' s' e' ok⌝ -∗ ⌜e.1 = Outgoing⌝ -∗
         if p' is None then
           Π (Some (Outgoing, e')) (link_to_case ok p' e', s', σ1, σ2')
         else
           (link_to_case ok p' e', s', σ1, σ2') ≈{link_trans R m1 m2}≈>ₜ Π
      end%I.

  Lemma sim_tgt_link_right R m1 m2 s σ1 σ2 Π :
    σ2 ≈{m2}≈>ₜ link_tgt_rightP R Π s σ1 -∗
    (MLFRun (Some SPRight), s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply (sim_gen_bind with "[-]").
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_right.
    iApply (sim_gen_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????). destruct κ; destruct!/=.
    - inv_all @link_filter. iSpecialize ("Hsim" $! s').
      case_match.
      + iIntros ([[[??]?]?] ?). simplify_eq/=. iRight. iSplit!.
        repeat case_match => //; simplify_eq/=.
        all: iApply ("Hsim" with "[//] [//]").
      + iIntros ([[[??]?]?] ?). simplify_eq/=. iLeft.
        repeat case_match => //; simplify_eq/=.
        all: iApply ("Hsim" with "[//] [//]").
    - iIntros ([[[??]?]?] ?). simplify_eq/=. by iLeft.
  Qed.

  Lemma sim_tgt_link_right_recv R m1 m2 s σ1 σ2 Π e :
    (σ2 ≈{m2}≈>ₜ λ κ σ2',
      match κ with
      | None => Π None (MLFRecv SPRight e, s, σ1, σ2')
      | Some e' => ⌜e' = (Incoming, e)⌝ -∗ (MLFRun (Some SPRight), s, σ1, σ2') ≈{link_trans R m1 m2}≈>ₜ Π
      end%I) -∗
    (MLFRecv SPRight e, s, σ1, σ2) ≈{link_trans R m1 m2}≈>ₜ Π.
  Proof.
    iIntros "Hsim".
    iApply sim_gen_bind.
    iApply sim_tgt_state_transform; [done|] => /=.
    iApply (sim_tgt_map with "[-]").
    iApply sim_tgt_seq_product_right.
    iApply (sim_gen_wand with "Hsim").
    iIntros (κ ?) "Hsim". iIntros (??????).
    iIntros ([[[??]?]?]?). simplify_eq/=. destruct κ; destruct!/=.
    - inv_all @link_filter. iRight. iSplit!. by iApply "Hsim".
    - by iLeft.
  Qed.
End link.
