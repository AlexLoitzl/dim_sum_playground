From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Arguments subst_static _ !_ /.

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

(* Call with direct return *)
Definition TCallRet {S} (f : string) (vs : list val) (h : heap_state) :
  spec rec_event S (val * heap_state) :=
  TVis (Outgoing, ERCall f vs h);;
  e ← TExist _;
  TVis (Incoming, e);;
  if e is ERReturn v h' then
    TRet (v, h')
  else
    TUb.

Section TCallRet.

  Context `{!dimsumGS Σ} `{!specGS} {S : Type}.

  Lemma sim_src_TCallRet f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
      ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗ ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
    POST Src _ (spec_trans rec_event S) ({{σ' Π',
      ⌜σ = σ'⌝ ∗  ∃ e,
    switch Π' ({{κ σ POST,
      ⌜κ = Some (Incoming, e)⌝ ∗
    POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
      ⌜σ = σ''⌝ ∗ ⌜Π = Π''⌝ ∗ (∀ v h', ⌜e = ERReturn v h'⌝ -∗ (SRC (k (v, h')) @ Π'' {{ Φ }}))}})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "HC" => /=. rewrite /TCallRet bind_bind.
    iApply sim_gen_TVis. iIntros (s) "Hs". iIntros "% % /=". iIntros "[% [% HΠ]]". subst.
    iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]" => /=. subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|]. rewrite bind_bind.
    iApply (sim_src_TExist _). rewrite bind_bind.
    iApply sim_gen_TVis. iIntros (s') "Hs". iIntros (??) "[% [% HΠ']]" => /=.
    subst. iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]". destruct!/=.
    iApply "HΠ". iSplit!. iSplitL "Hs". 1: done.
    destruct e. iApply sim_src_TUb.
    rewrite bind_ret_l.
    by iApply "HC".
  Qed.

End TCallRet.

(* ********************************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* ********************************************************************************************** *)
Section sim_getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition getc_spec_body : spec rec_event Z unit :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn (ValNum v) h).

  Definition getc_spec : spec rec_event Z void :=
    Spec.forever(getc_spec_body).

  Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
    γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
    inv H0. by dimsum.core.axioms.simplify_K.
  Qed.

  Lemma sim_getc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ ({{ σ' Π',
      ∃ v, ⌜f = "getc"⌝ ∗ ⌜es = []⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
    switch Π' (λ κ (σ : m_state (spec_trans rec_event Z)) POST,
      ⌜κ = Some (Outgoing, ERReturn (ValNum v) h)⌝ ∗ spec_state (v + 1) ∗
    POST Tgt _ _ ({{σ' Π'',
      ⌜σ' = σ⌝ ∗ ⌜Π'' = Π⌝ ∗ TGT getc_spec @ Π {{ Φ }}
    }}))}})}}) -∗
    TGT getc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "Hs".
    rewrite {2}/getc_spec unfold_forever /TReceive bind_bind -/getc_spec bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v') "Hγ' !>".
    iIntros (??) "[% [% HΠ]]".
    subst.
    iApply "Hs" => /=. iSplit!. iIntros (??) => /=.
    iDestruct 1 as (???) "[Hγ [% Hs']]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hγ']"); simpl; [done..|]. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind.
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>". rewrite bind_bind.
    iApply (sim_gen_TPut with "[Hγ]"). 1: done.
    iIntros "Hγ". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hγ'".
    iDestruct (mstate_var_agree with "Hγ Hγ'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% HΠ']]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. iFrame.
    iIntros (??) "[-> [-> HC]]".
    iApply "HΠ" => /=. by iFrame.
  Qed.

  Definition getc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, P v ∗ ⌜es = []⌝ ∗ POST (λ ret, ⌜ret = v⌝ ∗ P (v + 1))%I.

  Definition splittable (P : Z → iProp Σ) (PL : m_state (spec_trans rec_event Z) → iProp Σ) : iProp Σ :=
    ∀ v,
    P v -∗
    ∃ σ, PL σ ∗ (PL σ -∗ P v).

  Lemma sim_getc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) (σi : (m_state (spec_trans rec_event Z))) :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    PL σi -∗
    ⌜σi.1 ≡ getc_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_link_fixed Tgt Π_l (spec_trans _ Z) Π_r ({{σ_l POST,
      ∃ h v σg, PL σg ∗
    POST (ERCall "getc" [] h) σg ({{σ_r Π_r',
    switch_link Tgt Π_r' ({{σ_r' POST,
      ∃ h',
    POST (ERReturn (ValNum v) h') _ σ_l ({{_ Π_l',
      ⌜Π_l' = Π_l⌝ ∗ PL σ_r'
    }})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Π_l "getc" (getc_fn_spec P) ∗ □ splittable P PL.
  Proof.
    iIntros "#? #? HPL %<-  #Hs".

    iMod (mstate_var_alloc Z) as (γ) "Hγ".
    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    set P := (λ (v : Z), ∃ σ Φg, PL σ ∗ spec_state v ∗
                           ⥥ₜ({{σ' Π, ⌜σ' = σ⌝ ∗ ⌜Π = Π_r⌝ ∗ TGT getc_spec @ Π {{Φg}}}}))%I.

    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Tgt () Π_r e).
      iFrame.
      iIntros (??) "[-> [-> H]]" => /=.
      iApply (sim_gen_expr_intro with "[Hγ]") => /= //.
    - iIntros "!> %% [% [[% [% [HPL [Hγ Hg]]]] [-> HΦ]]]".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#?Htoa !>".
      iIntros (? σr) "[-> [-> HΠr]]" => /=. subst.
      iApply "Hs" => /=. iFrame. iSplit!.
      iIntros (? Π'') "[-> [-> Hs']]" => /=.
      iApply "Hg". iSplit!.
      iApply sim_getc_spec.
      iIntros (??) "[% [% [% [-> Hg]]]]" => /=.
      iApply "Hs'" => /=. iSplit!.
      iIntros (? Πs') "[% [% Hs']]". simplify_eq.
      iApply "Hg". iFrame. iSplit!.
      iIntros (??) "[-> [? Hg]]" => /=.
      iApply "Hs'" => /=. iSplit!.
      iIntros (? Πr') "[-> Hs']".
      iApply sim_tgt_rec_Waiting_raw.
      iSplit. { iIntros. iModIntro. iApply "Hs'". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
      iIntros (???) "!>". iApply "Hs'" => /=. iSplit!. iIntros (??) "[% [% [% HQ]]]". simplify_eq.
      iApply "HΠr". iSplit!. iFrame.
      iApply "HΦ". iFrame. iSplit!.
      iIntros (??) "[-> [-> ?]]" => /=.
      iApply "Hg". by iSplit!.
    - iIntros "!> % [% [% [? ?]]]".
      iFrame.
      iIntros "HPL".
      iFrame.
  Qed.

End sim_getc.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)

Section echo_getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_body_spec : spec rec_event Z void :=
    Spec.forever (v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h')).

  Definition putc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, P v ∗ ⌜es = [Val v]⌝ ∗ POST (λ _, P (v + 1))%I.

  Lemma sim_echo_body (S: specGS) fns Π_t Π_s (PL : m_state (spec_trans rec_event Z) → iProp Σ) (σi : (m_state (spec_trans rec_event Z))) :
    rec_fn_auth fns -∗
    "putc" ↪ None -∗
    (S.(spec_state_name)) ⤳@{Z} - -∗
    PL σi -∗
    ⌜σi.1 ≡ echo_body_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_external_fixed Π_t (spec_trans _ Z) Π_s ({{κ0 σ_t POST0,
        ∃ vs h σs, PL σs ∗ ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
      POST0 σs ({{σ_s1' Π_s',
        ∃ e : rec_ev, ⌜Π_s' = Π_s⌝ ∗
      switch Π_s' ({{ κ3 σ_s2 POST2,
        ⌜κ3 = Some (Incoming, e)⌝ ∗
      POST2 Src _ (spec_trans _ Z) ({{ σ_s2' Π_s'',
        ⌜Π_s'' = Π_s'⌝ ∗ ⌜σ_s2 = σ_s2'⌝ ∗
      switch Π_s ({{ κ4 σ_s3 POST3,
        ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
      POST3 Tgt _ _ ({{ σ_t1 Π_t',
        ⌜σ_t1 = σ_t⌝ ∗ ⌜Π_t' = Π_t⌝ ∗
      switch Π_t ({{ κ5 σ_t2 POST4,
        ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
      POST4 Tgt rec_event rec_trans ({{ σ_t3 Π_t',
        ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π_t = Π_t'⌝ ∗ PL σ_s3
    }})}})}})}})}})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Π_t "putc" (putc_fn_spec P) ∗ □ splittable P PL.
  Proof.
    set γ := spec_state_name.
    iIntros "#? #? Hγs HPL %<- #Hs".

    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".


    set P := (λ (v : Z), ∃ σ Φg, PL σ ∗ spec_state v ∗
                           ⥥ₛ({{σ' Π, ⌜σ' = σ⌝ ∗ ⌜Π = Π_s⌝ ∗ SRC echo_body_spec @ Π {{Φg}}}}))%I.
    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Src () Π_s e).
      iFrame.
      iIntros (??) "[-> [-> H]]" => /=.
      iApply (sim_gen_expr_intro with "[Hγ]") => //=.
    - iIntros "!> %% [% [[% [% [HPL [Hγ Hg]]]] [-> HΦ]]]".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#?Htoa !>".
      iIntros (? σr) "[-> [-> HΠ_t]]" => /=. subst.
      iApply "Hs" => /=. iFrame. iSplit!.
      iIntros (? Π'') "[-> [-> Hs']]" => /=.
      iApply "Hg". iSplit!.

      rewrite /echo_body_spec unfold_forever bind_bind -/echo_body_spec.
      iApply (sim_gen_TGet with "[-]"). iSplit. 1: done. rewrite bind_bind.
      iApply (sim_gen_TPut with "[$]"). iIntros "Hγ". rewrite bind_bind.
      iApply sim_src_TExist. rewrite bind_bind.

      iApply sim_src_TCallRet.
      iIntros (? σ1) "[% [% [% [% [% [% [% Hσ1]]]]]]]" => /=. simplify_eq.
      iApply "Hs'". iSplit!.
      iIntros (??) "[% [% [% Hs']]]" => /=. subst.
      iApply "Hσ1". iSplit!. iIntros (? σ2) "[% Hσ2]".
      iApply "Hs'". iSplit!. iIntros (??) "[% [<- Hs']]". subst.
      iApply "Hσ2". iSplit!. iIntros (?? ->).
      iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_None => /=.
      iIntros (?) "_ % ? %% /= [-> [-> H]]".
      iApply "Hs'" => /=. iSplit!.
      iIntros (??) "/= [-> [-> Hs']]".
      iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
      iApply "Hs'". iSplit!. iIntros (??) "[% [% [% ?]]]" => /=. subst.
      iApply "HΠ_t" => /=. iSplit!. iFrame.
      iApply "HΦ".
      iFrame. iExists _.
      iIntros (??) "[-> [-> ?]]". iApply "H" => /=.
      by iFrame.
    - iIntros "!> % [% [% [? ?]]]".
      iExists _.
      iFrame.
      iIntros "?".
      iFrame.
  Qed.

  Definition echo_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    echo_body_spec.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).

  Definition overlapping (P Q RP RQ : Z → iProp Σ) : iProp Σ :=
    (∀ v v', P v -∗ RQ v' ==∗ Q v' ∗ RP v) ∗ (∀ v v', Q v -∗ RP v' ==∗ P v' ∗ RQ v).

  Lemma sim_echo Π (P Q RP RQ : Z → iProp Σ) v :
    "echo" ↪ Some echo_rec -∗
    □ rec_fn_spec_hoare Tgt Π "getc" (getc_fn_spec P) -∗
    □ rec_fn_spec_hoare Tgt Π "putc" (putc_fn_spec Q) -∗
    □ overlapping P Q RP RQ -∗
    P v -∗
    RQ v -∗
    rec_fn_spec_hoare Tgt Π "echo" (λ es POST, ⌜es = []⌝).
  Proof.
    iIntros "#? #Hgetc #Hputc #[HRQ HRP] HP RQ %% ->".
    iApply sim_gen_expr_ctx. iIntros "#?".
    iAssert (∀ Φ v, P v -∗ RQ v -∗ TGT Call (Val (ValFn "echo")) [] @ Π {{ Φ }})%I as "H".
    {
      iApply (ord_loeb with "[$] []").
      iIntros "!>". iIntros "#IH %% ? ?".

      iApply (sim_tgt_rec_Call_internal with "[$]") => //.
      iModIntro => /=.
      iApply (sim_tgt_rec_AllocA); [done|].
      iIntros "% _ !>" => /=.
      iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.

      iApply "Hgetc".
      iFrame. iSplit! => /=. iIntros (?) "[-> ?]".

      iApply sim_tgt_rec_LetE. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
      iMod ("HRQ" with "[$] [$]") as "[? ?]".

      iApply "Hputc".
      iFrame. iSplit!.
      iIntros (?) "?".
      iApply sim_tgt_rec_LetE. iModIntro => /=.

      iMod ("HRP" with "[$] [$]") as "[? ?]".

      iApply ("IH" with "[$] [$]").
    }

    iApply ("H" with "[$] [$]").
  Qed.

  Lemma echo_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (MLFRun None, [], rec_init echo_prog, (getc_spec, 0)) ⪯{m_t,
      spec_trans rec_event Z} (echo_spec, 0).
  Proof.
    iIntros "[#Hfns Hh] /=".

    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γs) "Hγs".
    iMod (mstate_var_alloc (m_state m_t)) as (γt) "Hγt".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's spec state *)
    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s 0 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    destruct!/=. case_match; destruct!/=.

    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iEval (unfold echo_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec) (_, _, _)). rewrite bind_bind .
    setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis (H := HSrcSpec)). iIntros "% Hγs_s %% [-> [-> _ ]]".

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "->".

    iIntros "Hγs". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?).
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].
    iDestruct (mstate_var_merge with "Hγs_s' Hγs_s") as "[% Hγs_s]".

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iIntros "Hγs".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* Target's spec module (Right linking case - getc) *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt_r) "Hγt_r".

    (* Target's rec module (Left linking case - echo) *)
    iMod (mstate_var_alloc (m_state rec_trans)) as (γt_l) "Hγt_l".

    (* call stack of linking module  *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γt_q) "Hγt_q".

    (* Linking event to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γt_oe) "Hγt_oe".

    iApply (sim_tgt_link_left_const_run γt_q γt_l γt_r γt_oe with "[$] [$] [$] [$] [-]").
    iIntros "Hγt_q Hγt_r Hγt_oe".

    iMod (heapUR_alloc_blocks _ (h_blocks h) with "Hh") as "[Hh _]". { set_solver. }
    rewrite right_id_L heap_from_blocks_h_blocks.

    set (Π := tgt_link_left_constP _ _ _ _ _ _).
    set (Π_s := sim_src_constP γt γκ (EV := rec_event) (m_t := m_t) (m_s := spec_trans rec_event Z)).

    iApply (sim_gen_expr_intro _ [] with "[Hh]"). { done. } { by iFrame. }

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.

    iApply sim_gen_expr_ctx. iIntros "#?".

    set PL := (λ (σ : spec rec_event Z void * Z),
                 γt_r ⤳ σ ∗ γt_oe ⤳ @None rec_ev ∗ γt_q ⤳ [None : seq_product_case])%I.
    iDestruct (sim_getc _ Π _ PL (getc_spec, 0) with "[$] [] [$] [//] [//]") as "H".
    { by iApply (rec_fn_intro with "[$]"). }
    iMod ("H" with "[]") as "[%Pg [HPg [#Hgetc #Hsplitg]]]".

    (* Prove that I can switch to the getc module *)
    {
      iIntros "!> %% [% [% [% [[Hγt_r [Hγt_oe Hγt_q]] [% HC]]]]]" => /=. subst.

      iApply (tgt_link_left_constP_elim_run with "[$] [Hγt_r] [$]"). 1: done.
      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe".

      iIntros (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.

      iApply (sim_tgt_link_right_const_recv γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_l Hγt_oe".
      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]"=> /=.
      iApply (tgt_link_right_constP_elim_recv with "[Hγt_q] [Hγt_l] [$] [-]"). 1-2: done.

      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe" (?). simplify_eq.

      iApply (sim_tgt_link_right_const_run γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_l Hγt_oe".
      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]". simpl.

      iApply (tgt_link_right_constP_elim_run with "[Hγt_q] [Hγt_l] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe".

      iIntros (??????).
      destruct!/=.

      iApply (sim_tgt_link_left_const_recv γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.

      iApply (tgt_link_left_constP_elim_recv with "[Hγt_q] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe".

      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_const_run γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitg" with "HPg") as "[% [HPL HPg]]".

    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γi) "Hγi".
    iMod (mstate_var_split γi σ0 with "[$]") as "[Hγi Hγi']".

    set PS1 := (λ (σ : spec rec_event Z void * Z), γs ⤳ σ ∗ (∃ σ', γi ⤳ σ' ∗ PL σ'))%I.

    iDestruct (sim_echo_body _ _ Π Π_s PS1 σ with "[$] [] [$] [$Hγs $HPL $Hγi' //] [//] [//]") as "H". 1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pp [HPp [#Hputc #Hsplitp]]]".

    (* Prove that I can switch to the source with a call to putc *)
    {
      iIntros "!> %% [% [% [% [[Hγs [% [Hγi [Hγt_r [Hγt_oe Hγt_q]]]]] [% HC]]]]]" => /=.
      subst.

      iApply (tgt_link_left_constP_elim_run with "[$] [Hγt_r] [$]"). 1: done.
      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe".

      iIntros (??????). destruct!/=. rewrite bool_decide_false //.

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (->) "HC".
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??) "[% HC]". simplify_eq.
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs". iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (?? -> ->) "HC".
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs". destruct!/=.
      iApply (sim_tgt_link_left_const_recv γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC".

      iApply (tgt_link_left_constP_elim_recv with "[Hγt_q] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe" (?). simplify_eq.

      iApply (sim_tgt_link_left_const_run γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]"). 1-2: done.
      iIntros "???".

      iApply "HC". iSplit!. iFrame.
    }
    iDestruct ("Hsplitp" with "[$]") as "[% [[? [% [Hγi' ?]]] ?]]".
    iDestruct (mstate_var_merge with "Hγi Hγi'") as "[<- Hγi]".
    iDestruct ("HPg" with "[$]") as "HPg".


    set Rg := (λ v, ∃ σ, (PL σ -∗ Pg v) ∗ γi ⤳ σ)%I.
    set Rp := (λ v, ∃ σ, (PS1 σ -∗ Pp v) ∗ γs ⤳ σ ∗ γi ⤳@{m_state (spec_trans rec_event Z)} -)%I.

    iApply (sim_echo _ Pg Pp Rg Rp with "[] Hgetc Hputc [] [$] [$]") => //. 1: by iApply (rec_fn_intro with "[$]").
    iModIntro.
    iSplitR.
    - iIntros (??) "? [% [HPp [? ?]]]". iDestruct ("Hsplitg" with "[$]") as "[% [? ?]]". iFrame.
      iMod (mstate_var_split γi σ3 with "[$]") as "[Hγ Hγ']". iModIntro.
      iFrame.
      iApply "HPp".
      iFrame.
    - iIntros (??) "? [% [HPg Hγi]]". iDestruct ("Hsplitp" with "[$]") as "[% [[? [% [Hγi' ?]]] ?]]".
      iDestruct (mstate_var_merge with "Hγi Hγi'") as "[<- Hγi]".
      iFrame.
      by iApply "HPg".
Qed.
End echo_getc.
