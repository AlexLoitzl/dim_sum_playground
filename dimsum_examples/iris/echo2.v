From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Arguments subst_static _ !_ /.

(* TODO - Is this a more general notion we want to factor out somewhere? *)
Definition splittable {Σ A B} (P : A → iProp Σ) (PL : B → iProp Σ) : iProp Σ :=
  ∀ a,
  P a -∗
  ∃ b, PL b ∗ (PL b -∗ P a).

Definition overlapping {Σ} (P Q RP RQ : Z → iProp Σ) : iProp Σ :=
  (∀ v v', P v -∗ RQ v' ==∗ Q v' ∗ RP v) ∗ (∀ v v', Q v -∗ RP v' ==∗ P v' ∗ RQ v).

(* TODO *)
Definition overlapping' {Σ} (P Q : Z → iProp Σ) : iProp Σ :=
  (∀ v1 v1', P v1 -∗ (∀ v2, P v2 -∗ Q v1') -∗ Q v1' ∗ (∀ v2', Q v2' -∗ P v1)) ∗
  (∀ v1 v1', Q v1 -∗ (∀ v2, Q v2 -∗ P v1') -∗ P v1' ∗ (∀ v2', P v2' -∗ Q v1)).

Lemma overlapping_test {Σ A} (P Q : Z → iProp Σ) (S : A → iProp Σ) :
  splittable P S -∗
  splittable Q S -∗
  overlapping' P Q.
Proof.
  iIntros "HsplitP HSplitQ".
  iSplitL.
  - iIntros (??) "HP HmkQ".
    iSplitL "HmkQ HP".
    + by iApply "HmkQ".
    + iIntros (?) "HQ".
      iDestruct ("HSplitQ" with "HQ") as "[% [? ?]]".
      Abort.

(*** Programs *)
Definition echo_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := LetE "c" (rec.Call (Val (ValFn "getc")) []) $
             LetE "_" (rec.Call (Val (ValFn "putc")) [Var "c"]) $
             rec.Call (Val (ValFn "echo")) [];
  fd_static := I
|}.

Definition echo_prog : gmap string fndef :=
  <["echo" := echo_rec]> $ ∅.

Definition getc_spec : spec rec_event Z void :=
  Spec.forever(
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn (ValNum v) h)).

Definition echo_body_spec : spec rec_event Z void :=
  Spec.forever (v ← TGet;
  TPut (v + 1);;
  h ← TExist _;
  '(ret, h') ← TCallRet "putc" [(ValNum v)] h;
  TAssume (ret = ValNum 0);;
  TAssume (h = h')).

Definition echo_spec : spec rec_event Z void :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "echo");;
  TAssume (vs = []);;
  echo_body_spec.

(* *************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* *************************************************************************** *)
Section sim_getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_getc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ Π ({{ σ',
      ∃ v, ⌜f = "getc"⌝ ∗ ⌜es = []⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
    switch Π ({{ κ σ POST,
      ⌜κ = Some (Outgoing, ERReturn (ValNum v) h)⌝ ∗ spec_state (v + 1) ∗
    POST Tgt _ _ Π ({{σ',
      ⌜σ' = σ⌝ ∗ TGT getc_spec @ Π {{ Φ }}
    }})}})}})}}) -∗
    TGT getc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "HC".
    rewrite {2}/getc_spec unfold_forever /TReceive bind_bind -/getc_spec bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (?) "Hγ' !>".
    iIntros (??) "[-> [-> HΠ]]".
    iApply "HC" => /=. iSplit!. iIntros (?) => /=.
    iDestruct 1 as (?->->) "[Hγ [-> HC']]".
    iApply "HΠ". iFrame. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_gen_TGet with "[-]").
    iSplit;[done|iModIntro]. rewrite bind_bind.
    iApply (sim_gen_TPut with "[Hγ]");[done|].
    iIntros "Hγ !>".
    iApply (sim_gen_TVis with "[-]"). iIntros (?) "Hγ'".
    iDestruct (mstate_var_agree with "Hγ Hγ'") as "<-".
    iIntros "!> %% [-> [-> HΠ]]".
    iApply "HC'". iSplit!. iFrame.
    iIntros (?) "[-> ?]".
    iApply "HΠ". by iFrame.
  Qed.

  Definition getc_hoare (P : Z → iProp Σ) ts Π : iProp Σ :=
    rec_hoare ts Π "getc"
      (λ es RET, ∃ v, P v ∗ ⌜es = []⌝ ∗ RET v)%I
      (λ a v, ⌜v = a⌝ ∗ P (a + 1))%I.

  Lemma sim_getc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) σi :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    PL σi -∗
    ⌜σi.1 ≡ getc_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_link Tgt Π_l ({{σ_l POST,
      ∃ h v σg, PL σg ∗
    POST (ERCall "getc" [] h) (spec_trans _ Z) σg Π_r ({{σ_r,
    switch_link Tgt Π_r ({{σ_r' POST,
      ∃ h',
    POST (ERReturn (ValNum v) h') _ σ_l Π_l ({{_,
      PL σ_r'
    }})}})}})}}) -∗
    (* REVIEW - I usually seem to tend to linebreak after the operator with sep
         which I would otherwise not do :/ *)
    |==> ∃ P, P 0 ∗ □ getc_hoare P Tgt Π_l ∗ □ splittable P PL.
  Proof.
    iIntros "#? #? HPL %<- #HC".

    iMod (mstate_var_alloc Z) as (γ) "Hγ".
    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    set P := (λ (v : Z),
                ∃ σ Φg, PL σ ∗ spec_state v ∗
                        ({{σ', ⌜σ' = σ⌝ ∗ TGT getc_spec @ Π_r {{Φg}}}}) ⇒ₜ Π_r)%I.

    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Tgt () Π_r e).
      iFrame.
      iIntros (?) "[-> ?]".
      iApply (sim_gen_expr_intro with "[Hγ]") => //=.
    - iIntros "!> %% (% & (% & % & ? & ? & Hg) & -> & HΦ)".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#? ? !>".
      iIntros (??) "[-> [-> HΠr]] /=".
      iApply "HC". iFrame. iSplit!.
      iIntros (?) "[-> HC']".
      iApply "Hg". iSplit!.
      iApply sim_getc_spec.
      iIntros (??) "(% & % & % & -> & Hg)".
      iApply "HC'". iSplit!.
      iIntros (?) "[% [% HC']]". simplify_eq.
      iApply "Hg". iFrame. iSplit!.
      iIntros (??) "[-> [? Hg]]".
      iApply "HC'". iSplit!.
      iIntros (?) "[-> HC']".
      iApply sim_tgt_rec_Waiting_all_raw.
      iIntros (?) "!>". iApply "HC'". iSplit!. iIntros (?) "[-> [-> HQ]]".
      iApply "HΠr". iSplit!. iFrame.
      iApply "HΦ". by iFrame.
    - iIntros "!> % (% & % & ? & ?)".
      iFrame.
      iIntros "HPL".
      iFrame.
  Qed.

End sim_getc.

(* *************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo⟧_spec *)
(* *************************************************************************** *)

Section echo_getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition putc_hoare (P : Z → iProp Σ) ts Π : iProp Σ :=
    rec_hoare ts Π "putc"
      (λ es RET, ∃ v, P v ∗ ⌜es = [Val v]⌝ ∗ RET v)%I
      (λ a _, P (a + 1))%I.

  Lemma sim_echo_body (S: specGS) fns Π_t Π_s
      (PL : m_state (spec_trans rec_event Z) → iProp Σ)
      (σi : (m_state (spec_trans rec_event Z))) :
    rec_fn_auth fns -∗
    "putc" ↪ None -∗
    (S.(spec_state_name)) ⤳@{Z} - -∗
    PL σi -∗
    ⌜σi.1 ≡ echo_body_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_external Π_t ({{κ0 σ_t POST0,
        ∃ vs h σs, PL σs ∗ ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
      POST0 (spec_trans _ Z) σs Π_s ({{σ_s1',
        ∃ e : rec_ev,
      switch Π_s ({{ κ3 σ_s2 POST2,
        ⌜κ3 = Some (Incoming, e)⌝ ∗
      POST2 Src _ (spec_trans _ Z) Π_s ({{ σ_s2',
        ⌜σ_s2 = σ_s2'⌝ ∗
      switch Π_s ({{ κ4 σ_s3 POST3,
        ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
      POST3 Tgt _ _ Π_t ({{ σ_t1,
        ⌜σ_t1 = σ_t⌝ ∗
      switch Π_t ({{ κ5 σ_t2 POST4,
        ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
      POST4 Tgt rec_event rec_trans Π_t ({{ σ_t3,
        ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ PL σ_s3
    }})}})}})}})}})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ putc_hoare P Tgt Π_t ∗ □ splittable P PL.
  Proof.
    set γ := spec_state_name.
    iIntros "#? #? ? ? %<- #HC".
    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".

    set P := (λ (v : Z),
                ∃ σ Φg, PL σ ∗ spec_state v ∗
                  ({{σ', ⌜σ' = σ⌝ ∗ SRC echo_body_spec @ Π_s {{Φg}}}}) ⇒ₛ Π_s)%I.
    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Src () Π_s e).
      iFrame.
      iIntros (?) "[-> ?]".
      iApply (sim_gen_expr_intro with "[Hγ]") => //=.
    - iIntros "!> %% (% & (% & % & ? & ? & Hg) & -> & HΦ)".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#? ? !>".
      iIntros (??) "[-> [-> HΠ_t]]".
      iApply "HC". iFrame. iSplit!.
      iIntros (?) "[-> HC']".
      iApply "Hg". iSplit!.

      rewrite /echo_body_spec unfold_forever bind_bind -/echo_body_spec.
      iApply (sim_gen_TGet with "[-]"). iSplit;[done|]. rewrite bind_bind.
      iApply (sim_gen_TPut with "[$]"). iIntros "Hγ". rewrite bind_bind.
      iApply sim_src_TExist. rewrite bind_bind.
      iApply sim_src_TCallRet.
      iIntros (??) "(% & % & % & -> & -> & -> & -> & HΠ_s)".
      iApply "HC'". iSplit!.
      iIntros (?) "[-> [% HC']]".
      iApply "HΠ_s". iSplit!. iIntros (??) "[-> HΠ_s]".
      iApply "HC'". iSplit!. iIntros (?) "[-> HC']".
      iApply "HΠ_s". iSplit!. iIntros (?? ->). rewrite bind_bind.
      iApply sim_src_TAssume. iIntros "->".
      iApply sim_src_TAssume. iIntros "->".
      iApply sim_gen_expr_None.
      iIntros "/= % _ % ? %% /= [-> [-> H]]".
      iApply "HC'". iSplit!.
      iIntros (?) "/= [-> HC']".
      iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
      iApply "HC'". iSplit!. iIntros (?) "[-> [<- ?]]".
      iApply "HΠ_t". iSplit!. iFrame.
      iApply "HΦ".
      iFrame. iExists _.
      iIntros (?) "[-> ?]". iApply "H".
      by iFrame.
    - iIntros "!> % (% & % & ? & ?)".
      iExists _.
      iFrame.
      iIntros "?".
      iFrame.
  Qed.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).

  Lemma sim_echo Π (P Q RP RQ : Z → iProp Σ) v :
    "echo" ↪ Some echo_rec -∗
    □ getc_hoare P Tgt Π -∗
    □ putc_hoare Q Tgt Π -∗
    □ overlapping P Q RP RQ -∗
    P v -∗
    RQ v -∗
    rec_hoare Tgt Π "echo" (λ es _, ⌜es = []⌝) (λ (_ : unit) _, True).
  Proof.
    iIntros "#? #Hgetc #Hputc #[HRQ HRP] HP RQ %% ->".
    iApply sim_gen_expr_ctx. iIntros "#?".
    iRevert (Φ v) "HP RQ".

    iApply (ord_loeb with "[$] []").
    iIntros "!> #IH %% ? ?".

    iApply (sim_tgt_rec_Call_internal with "[$]"); [done|].
    iModIntro.
    iApply (sim_tgt_rec_AllocA); [done|].
    iIntros "% _ !>".
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]").

    iApply "Hgetc".
    iFrame. iSplit!. iIntros (?) "[-> ?]".
    iApply sim_tgt_rec_LetE. iModIntro.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iMod ("HRQ" with "[$] [$]") as "[? ?]".

    iApply "Hputc".
    iFrame. iSplit!.
    iIntros (?) "?".
    iApply sim_tgt_rec_LetE. iModIntro.

    iMod ("HRP" with "[$] [$]") as "[? ?]".
    iApply ("IH" with "[$] [$]").
  Qed.

  Lemma echo_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (MLFRun None, [], rec_init echo_prog, (getc_spec, 0)) ⪯{m_t,
      spec_trans rec_event Z} (echo_spec, 0).
  Proof.
    iIntros "[#Hfns ?] /=".

    (* Ghost variable for source, target, and event *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (m_state m_t)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's state *)
    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s 0 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    destruct!/=. case_match; destruct!/=.

    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt
             with "[Hγs_s] [-]"); [simpl; done..|].

    iEval (rewrite /echo_spec /TReceive bind_bind).
    iApply (sim_src_TExist (H := HSrcSpec) (_, _, _)). rewrite bind_bind .
    setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis (H := HSrcSpec)). iIntros "% Hγs_s %% [-> [-> HΠ_s]]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "->".
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "HΠ_s". iFrame.
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (->).
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (->).
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].
    iDestruct (mstate_var_merge with "Hγs_s' Hγs_s") as "[% Hγs_s]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* Target's spec module (Right linking case - getc) *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γσr_t) "Hγσr_t".
    (* Target's rec module (Left linking case - echo) *)
    iMod (mstate_var_alloc (m_state rec_trans)) as (γσl_t) "Hγσl_t".
    (* call stack of linking module  *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γq_t) "Hγq_t".
    (* Linking event *)
    iMod (mstate_var_alloc (option rec_ev)) as (γκ_t) "Hγκ_t".

    iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t with "[$] [$] [$] [$] [-]").
    iIntros "Hγq_t Hγσr_t Hγκ_t".

    iMod (heapUR_alloc_blocks _ (h_blocks h) with "[$]") as "[Hinv _]". { set_solver. }
    rewrite right_id_L heap_from_blocks_h_blocks.

    set (Π := tgt_link_left_constP _ _ _ _ _ _).
    set (Π_s := sim_src_constP γσ_t γκ (m_t := m_t) (m_s := spec_trans rec_event Z)).

    iApply (sim_gen_expr_intro _ [] with "[Hinv]"); [done|by iFrame|].
    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply sim_gen_expr_ctx. iIntros "#?".

    set PL := (λ (σ : spec rec_event Z void * Z),
                 γσr_t ⤳ σ ∗ γκ_t ⤳ @None rec_ev ∗ γq_t ⤳ [None : seq_product_case])%I.

    iDestruct (sim_getc _ Π _ PL (getc_spec, 0) with "[$] [] [$] [//] [//]") as "H".
    1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pg [HPg [#Hgetc #Hsplitg]]]".

    (* Prove that we can switch to the getc module *)
    {
      iIntros "!> %% (% & % & % & (Hγσr_t & ? & ?) & -> & HC)".
      (* REVIEW - How to do this better with done *)
      iApply (tgt_link_left_constP_run_elim with "[$] [Hγσr_t] [$]"); [done|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_right_constP_recv_elim with "[Hγq_t] [Hγσl_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (?). simplify_eq.
      iApply (sim_tgt_link_right_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".

      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_right_constP_run_elim with "[Hγq_t] [Hγσl_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????).
      destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.
      iApply (tgt_link_left_constP_recv_elim with "[Hγq_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitg" with "HPg") as "[%σt_r [HPL HPg]]".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γi) "Hγi".
    iMod (mstate_var_split γi σt_r with "[$]") as "[Hγi Hγi']".

    set PS1 := (λ (σ : spec rec_event Z void * Z), γσ_s ⤳ σ ∗ (∃ σ', γi ⤳ σ' ∗ PL σ'))%I.

    iDestruct (sim_echo_body _ _ Π Π_s PS1 σ
                with "[$] [] [$] [$Hγσ_s $HPL $Hγi' //] [//] [//]") as "H".
    1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pp [HPp [#Hputc #Hsplitp]]]".
    (* Prove that we can switch to the source with a call to putc *)
    {
      iIntros "!> %% (% & % & % & (Hγσ_s & % & ? & Hγσr_t & ? & ?) & -> & HC) /=".
      iApply (tgt_link_left_constP_run_elim with "[$] [Hγσr_t] [$]");[done|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????). destruct!/=. rewrite bool_decide_false //.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "[-> HC]".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "[-> HC]".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "(% & % & -> & -> & HC)".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_left_constP_recv_elim with "[Hγq_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %". simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"). 1-2: done.
      iIntros "???".

      iApply "HC". iSplit!. iFrame.
    }
    iDestruct ("Hsplitp" with "[$]") as "[% [[? [% [Hγi' ?]]] ?]]".
    iDestruct (mstate_var_merge with "Hγi Hγi'") as "[<- Hγi]".
    iDestruct ("HPg" with "[$]") as "HPg".

    set Rg := (λ v, ∃ σ, (PL σ -∗ Pg v) ∗ γi ⤳ σ)%I.
    set Rp := (λ v, ∃ σ, (PS1 σ -∗ Pp v) ∗ γσ_s ⤳ σ ∗
                           γi ⤳@{m_state (spec_trans rec_event Z)} -)%I.

    iApply (sim_echo _ Pg Pp Rg Rp with "[] Hgetc Hputc [] [$] [$]");
      [by iApply (rec_fn_intro with "[$]")| |done].
    iModIntro.
    iSplitR.
    - iIntros (??) "? [% [HPp [? ?]]]".
      iDestruct ("Hsplitg" with "[$]") as "[%σ_t [? ?]]". iFrame.
      iMod (mstate_var_split γi σ_t with "[$]") as "[Hγ Hγ']". iModIntro.
      iFrame.
      iApply "HPp".
      iFrame.
    - iIntros (??) "? [% [HPg Hγi]]".
      iDestruct ("Hsplitp" with "[$]") as "[% [[? [% [Hγi' ?]]] ?]]".
      iDestruct (mstate_var_merge with "Hγi Hγi'") as "[<- Hγi]".
      iFrame.
      by iApply "HPg".
   Qed.
End echo_getc.

(*** Linked putc *)

Definition putc_spec : spec rec_event Z void :=
  Spec.forever(
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "putc");;
    v ← TGet;
    TAssume (vs = [ValNum v]);;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn 0 h)).

Section sim_putc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_putc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ Π ({{ σ',
      ∃ v, ⌜f = "putc"⌝ ∗ ⌜es = [ValNum v]⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
    switch Π ({{ κ σ POST,
      ⌜κ = Some (Outgoing, ERReturn 0 h)⌝ ∗ spec_state (v + 1) ∗
    POST Tgt _ _ Π ({{σ',
      ⌜σ' = σ⌝ ∗ TGT putc_spec @ Π {{ Φ }}
    }})}})}})}}) -∗
    TGT putc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "HC".
    rewrite {2}/putc_spec unfold_forever /TReceive bind_bind -/putc_spec bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (?) "Hγ' !>".
    iIntros (??) "[-> [-> HΠ]]".
    iApply "HC". iSplit!. iIntros (?) "(% & -> & -> & Hγ & -> & HC')".
    iApply "HΠ". iFrame. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_gen_TGet with "[-]").
    iSplit; [done|iModIntro]. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_gen_TPut with "[Hγ]"); [done|].
    iIntros "Hγ !>".
    iApply (sim_gen_TVis with "[-]"). iIntros (?) "Hγ' !> %% [-> [-> HΠ]]".
    iApply "HC'". iSplit!. iFrame.
    iIntros (?) "[-> HC]".
    iApply "HΠ". by iFrame.
  Qed.

  Lemma sim_putc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) σi :
    rec_fn_auth fns -∗
    "putc" ↪ None -∗
    PL σi -∗
    ⌜σi.1 ≡ putc_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_link Tgt Π_l ({{σ_l POST,
        ∃ h v σg, PL σg ∗
      POST (ERCall "putc" [v] h) (spec_trans _ Z) σg Π_r ({{σ_r,
      switch_link Tgt Π_r ({{σ_r' POST,
        ∃ h',
      POST (ERReturn 0 h') _ σ_l Π_l ({{_, PL σ_r'}})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ putc_hoare P Tgt Π_l ∗ □ splittable P PL.
  Proof.
    iIntros "#? #? HPL % %Hσi_s  #HC".
    iMod (mstate_var_alloc Z) as (γ) "Hγ".
    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    set P := (λ (v : Z),
                ∃ σ Φg, PL σ ∗ spec_state v ∗
                        ({{σ', ⌜σ' = σ⌝ ∗ TGT putc_spec @ Π_r {{Φg}}}}) ⇒ₜ Π_r)%I.

    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Tgt () Π_r e). rewrite {2}Hσi_s.
      iFrame.
      iIntros (?) "[-> ?]".
      iApply (sim_gen_expr_intro with "[Hγ]") => //=.
    - iIntros "!> %% (% & (% & % & ? & ? & Hg) & -> & HΦ)".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#? ? !>".
      iIntros (??) "[-> [-> HΠr]]".
      iApply "HC". iFrame. iSplit!.
      iIntros (?) "[-> HC']".
      iApply "Hg". iSplit!.
      iApply sim_putc_spec.
      iIntros (??) "(% & % & % & -> & Hg)".
      iApply "HC'". iSplit!.
      iIntros (?) "[% [% HC']]". simplify_eq.
      iApply "Hg". iFrame. iSplit!.
      iIntros (??) "[-> [? Hg]]".
      iApply "HC'". iSplit!.
      iIntros (?) "[-> HC']".
      iApply sim_tgt_rec_Waiting_all_raw.
      iIntros (?) "!>". iApply "HC'". iSplit!. iIntros (?) "[-> [-> HQ]]".
      iApply "HΠr". iSplit!. iFrame.
      iApply "HΦ". by iFrame.
    - iIntros "!> % (% & % & ? & ?)".
      iFrame.
      iIntros "HPL".
      iFrame.
  Qed.

End sim_putc.

(* *************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⊕ ⟦putc⟧_spec ⪯ NB *)
(* *************************************************************************** *)

Definition echoNb_spec : spec rec_event unit void :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "echo");;
  TAssume (vs = []);;
  TNb.

Section SharedStateTarget.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Let m_t2 := rec_link_trans {["getc"]} {["putc"]} (spec_trans rec_event Z)
                (spec_trans rec_event Z).
  Let m_t := rec_link_trans {["echo"]} {["getc"; "putc"]} rec_trans m_t2.

  Lemma echoNb_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (MLFRun None, [], rec_init echo_prog, (MLFRun None, [], (getc_spec, 0), (putc_spec, 0)))
      ⪯{m_t, spec_trans rec_event ()} (echoNb_spec, ()).
  Proof.
    iIntros "[#Hfns ?] /=".

    (* Ghost variable for source, target, and event *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event ()))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (m_state m_t)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's state *)
    iMod (mstate_var_alloc ()) as (γs_s) "?".
    iMod (mstate_var_split γs_s tt with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    destruct!/=. case_match; destruct!/=.

    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt
             with "[Hγs_s] [-]"); [simpl; done..|].

    iEval (rewrite /echoNb_spec /TReceive bind_bind).
    iApply (sim_src_TExist (H := HSrcSpec) (_, _, _)). rewrite bind_bind .
    setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis (H := HSrcSpec)). iIntros "% Hγs_s %% [-> [-> HΠ_s]]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "->".
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    (* FIXME *)
    iApply "HΠ_s". iFrame.
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (->).
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (->).
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].
    iDestruct (mstate_var_merge with "Hγs_s' Hγs_s") as "[% Hγs_s]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* getc and putc modules *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γσl_tr) "Hγσl_tr".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γσr_tr) "Hγσr_tr".

    (* echo rec module *)
    iMod (mstate_var_alloc (m_state rec_trans)) as (γσl_t) "Hγσl_t".

    (* Inner linking module *)
    iMod (mstate_var_alloc (m_state m_t2)) as (γσr_t) "Hγσr_t".

    (* call stack of linking modules *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γq_t) "Hγq_t".
    iMod (mstate_var_alloc (list seq_product_case)) as (γq_t2) "Hγq_t2".

    (* Linking events to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γκ_t) "Hγκ_t".
    iMod (mstate_var_alloc (option rec_ev)) as (γκ_t2) "Hγκ_t2".

    iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t with "[$] [$] [$] [$] [-]").
    iIntros "Hγq_t Hγσr_t Hγκ_t".

    iMod (heapUR_alloc_blocks _ (h_blocks h) with "[$]") as "[Hinv _]". { set_solver. }
    rewrite right_id_L heap_from_blocks_h_blocks.

    set (Π_e := tgt_link_left_constP _ _ _ _ _ _).
    set (Π_s := sim_src_constP γσ_t γκ (m_t := m_t) (m_s := spec_trans rec_event ())).

    iApply (sim_gen_expr_intro _ [] with "[Hinv]"); [done|by iFrame|].
    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]").
    iApply sim_gen_expr_ctx. iIntros "#?".

    (* Variable for invariant of state of putc module *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γip) "Hγip".
    iMod (mstate_var_split γip (putc_spec, 0) with "[$]") as "[Hγip Hγip']".

    set PL := (γσl_tr ⤳@{m_state (spec_trans rec_event Z)} - ∗
               γσr_tr ⤳@{m_state (spec_trans rec_event Z)} - ∗
               γκ_t ⤳ @None rec_ev ∗ γq_t ⤳ [None : seq_product_case] ∗
               γκ_t2 ⤳@{option rec_ev} - ∗ γq_t2 ⤳@{list seq_product_case} -)%I.

    set PGL := (λ σ_g, PL ∗
                       ∃ σ_p, γip ⤳ σ_p ∗
                              γσr_t ⤳ ((MLFRun None, nil, σ_g, σ_p) : m_state m_t2))%I.

    iDestruct (sim_getc _ Π_e _ PGL (getc_spec, 0) with "[$] [] [$] [//] [//]") as "H".
    1: by iApply (rec_fn_intro with "[$]").

    iMod ("H" with "[]") as "[%Pg [HPg [#Hgetc #Hsplitg]]]".

    (* Prove that I can switch to the getc module *)
    {
      iIntros "!> %% (% & % & % &
        ((Hγσl_tr & Hγσr_tr & Hγκ_t & Hγq_t & ? & ?) & % & ? & Hγσr_t) & -> & HC) /=".

      iApply (tgt_link_left_constP_run_elim with "Hγq_t [Hγσr_t] Hγκ_t [-]"). done.
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".
      iApply (sim_tgt_link_None with "[-]").
      iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
      iApply (tgt_link_right_constP_recv_elim with "Hγq_t [Hγσl_t] Hγκ_t [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %". destruct!/=. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".
      iApply (sim_tgt_link_left_constP_recv γq_t2 γσl_tr γσr_tr γκ_t2
               with "[$] [Hγσl_tr] [Hγσr_tr] [$] [-]");[done..|].
      iIntros "Hγq_t2 Hγσr_tr Hγκ_t2".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_left_constP_recv_elim with "Hγq_t2 [Hγσr_tr] Hγκ_t2 [-]"); [done|].
      iIntros "Hγq_t2 Hγσl_tr Hγσr_tr Hγκ_t2 %". simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t2 γσl_tr γσr_tr γκ_t2
               with "[$] [Hγσl_tr] [Hγσr_tr] [$] [-]"); [done..|].
      iIntros "Hγq_t2 Hγσr_tr Hγκ_t2".

      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.
      iApply (tgt_link_left_constP_run_elim with "Hγq_t2 [Hγσr_tr] Hγκ_t2 [-]"); [done|].
      iIntros "Hγq_t2 Hγσl_tr Hγσr_tr Hγκ_t2" (??????). destruct!/=.
      iApply (tgt_link_right_constP_run_elim with "Hγq_t [Hγσl_t] Hγκ_t [-]"); [done|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (??????). destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".

      iApply (tgt_link_left_constP_recv_elim with "Hγq_t [Hγσr_t] Hγκ_t [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %". simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitg" with "HPg") as "[%σt_l [[HPL [% [Hγip' Hγσr_t]]] HPg]]".
    iDestruct (mstate_var_merge γip with "[$] [$]") as "[-> Hγip]".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γig) "Hγig".
    iMod (mstate_var_split γig σt_l with "[$]") as "[Hγig Hγig']".

    set PPL := (λ σ_p, PL ∗
                       ∃ σ_g, γig ⤳ σ_g ∗
                              γσr_t ⤳ ((MLFRun None, nil, σ_g, σ_p) : m_state m_t2))%I.

    iDestruct (sim_putc _ Π_e _ PPL (putc_spec, 0) with "[$] [] [$] [//] [//]") as "H".
    1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pp [HPp [#Hputc #Hsplitp]]]".
    {
      iIntros "!> %% (% & % & % & ((Hγσl_tr & Hγσr_tr & Hγκ_t & Hγq_t & ? & ?) & % & ? & Hγσr_t) & -> & HC) /=".
      iApply (tgt_link_left_constP_run_elim with "Hγq_t [Hγσr_t] Hγκ_t [-]"). done.
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".
      iApply (sim_tgt_link_None with "[-]").
      iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
      iApply (tgt_link_right_constP_recv_elim with "Hγq_t [Hγσl_t] Hγκ_t [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %".
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".
      iApply (sim_tgt_link_right_constP_recv γq_t2 γσl_tr γσr_tr γκ_t2
               with "[$] [Hγσl_tr] [Hγσr_tr] [$] [-]"); [done..|].
      iIntros "Hγq_t2 Hγσl_tr Hγκ_t2".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".

      iApply (tgt_link_right_constP_recv_elim with "Hγq_t2 [Hγσl_tr] Hγκ_t2 [-]"); [done..|].
      iIntros "Hγq_t2 Hγσl_tr Hγσr_tr Hγκ_t2 %". simplify_eq.
      iApply (sim_tgt_link_right_constP_run γq_t2 γσl_tr γσr_tr γκ_t2
               with "[$] [Hγσl_tr] [Hγσr_tr] [$] [-]"); [done..|].
      iIntros "Hγq_t2 Hγσl_tr Hγκ_t2".

      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_right_constP_run_elim with "Hγq_t2 [Hγσl_tr] Hγκ_t2 [-]"); [done..|].
      iIntros "Hγq_t2 Hγσl_tr Hγσr_tr Hγκ_t2" (??????). destruct!/=.
      iApply (tgt_link_right_constP_run_elim with "Hγq_t [Hγσl_t] Hγκ_t [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (??????). destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_left_constP_recv_elim with "Hγq_t [Hγσr_t] Hγκ_t [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %". simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitp" with "[$]") as "[%σt_r [[HPL [% [Hγig' ?]]] HPp]]".
    iDestruct (mstate_var_merge with "Hγig Hγig'") as "[<- Hγig]".
    iMod (mstate_var_split γip σt_r with "[$]") as "[Hγip Hγip']".
    iDestruct ("HPg" with "[$]") as "HPg".

    set Rg := (λ v, ∃ σ, (PGL σ -∗ Pg v) ∗ γig ⤳ σ ∗
                         γip ⤳@{m_state (spec_trans rec_event Z)} -)%I.
    set Rp := (λ v, ∃ σ, (PPL σ -∗ Pp v) ∗ γip ⤳ σ ∗
                         γig ⤳@{m_state (spec_trans rec_event Z)} -)%I.

    iApply (sim_echo _ Pg Pp Rg Rp with "[] Hgetc Hputc [] [$] [$]");
      [by iApply (rec_fn_intro with "[$]")| |done].
    iModIntro.
    iSplitR.
    - iIntros (??) "? [% [HPp [? ?]]]".
      iDestruct ("Hsplitg" with "[$]") as "[%σ_l [[? [% [? ?]]] ?]]". iFrame.
      iMod (mstate_var_split γig σ_l with "[$]") as "[Hγig Hγig']". iModIntro.
      iDestruct (mstate_var_merge γip with "[$] [$]") as "[<- Hγip]".
      iFrame.
      iApply "HPp".
      iFrame.
    - iIntros (??) "? [% [HPg [? ?]]]".
      iDestruct ("Hsplitp" with "[$]") as "[%σ_r [[? [% [? ?]]] ?]]". iFrame.
      iMod (mstate_var_split γip σ_r with "[$]") as "[Hγip Hγip']". iModIntro.
      iDestruct (mstate_var_merge γig with "[$] [$]") as "[<- Hγig]".
      iFrame.
      iApply "HPg".
      iFrame.
  Qed.

End SharedStateTarget.
