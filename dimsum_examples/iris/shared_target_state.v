From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint_mono.
From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Arguments subst_static _ !_ /.

Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
  γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
Proof.
  iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
  inv H0. by dimsum.core.axioms.simplify_K.
Qed.

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

Definition splittable {Σ} (P : Z → iProp Σ) (PL : m_state (spec_trans rec_event Z) → iProp Σ) : iProp Σ :=
  ∀ v,
  P v -∗
  ∃ σ, PL σ ∗ (PL σ -∗ P v).

Definition overlapping {Σ} (P Q RP RQ : Z → iProp Σ) : iProp Σ :=
  (∀ v v', P v -∗ RQ v' ==∗ Q v' ∗ RP v) ∗ (∀ v v', Q v -∗ RP v' ==∗ P v' ∗ RQ v).

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

Section sim_putc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition putc_spec_body : spec rec_event Z unit :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "putc");;
    v ← TGet;
    TAssume (vs = [ValNum v]);;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn 0 h).

  Definition putc_spec : spec rec_event Z void :=
    Spec.forever(putc_spec_body).

  Lemma sim_putc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ ({{ σ' Π',
      ∃ v, ⌜f = "putc"⌝ ∗ ⌜es = [ValNum v]⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
    switch Π' (λ κ (σ : m_state (spec_trans rec_event Z)) POST,
      ⌜κ = Some (Outgoing, ERReturn 0 h)⌝ ∗ spec_state (v + 1) ∗
    POST Tgt _ _ ({{σ' Π'',
      ⌜σ' = σ⌝ ∗ ⌜Π'' = Π⌝ ∗ TGT putc_spec @ Π {{ Φ }}
    }}))}})}}) -∗
    TGT putc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "Hs".
    rewrite {2}/putc_spec unfold_forever /TReceive bind_bind -/putc_spec bind_bind.
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
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done. iModIntro. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iModIntro. rewrite bind_bind.
    iApply (sim_gen_TPut with "[Hγ]"); [done|].
    iIntros "Hγ". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hγ'".
    iIntros "!> /=".
    iIntros (??) "[% [% HΠ']]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. iFrame.
    iIntros (??) "[-> [-> HC]]".
    iApply "HΠ" => /=. by iFrame.
  Qed.

  Definition putc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, P v ∗ ⌜es = [Val v]⌝ ∗ POST (λ ret, ⌜ret = 0⌝ ∗ P (v + 1))%I.

  Lemma sim_putc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) (σi : (m_state (spec_trans rec_event Z))) :
    rec_fn_auth fns -∗
    "putc" ↪ None -∗
    PL σi -∗
    ⌜σi.1 ≡ putc_spec⌝ -∗
    ⌜σi.2 = 0⌝ -∗
    □ switch_link_fixed Tgt Π_l (spec_trans _ Z) Π_r ({{σ_l POST,
        ∃ h v σg, PL σg ∗
      POST (ERCall "putc" [v] h) σg ({{σ_r Π_r',
      switch_link Tgt Π_r' ({{σ_r' POST,
        ∃ h',
      POST (ERReturn 0 h') _ σ_l ({{_ Π_l',
        ⌜Π_l' = Π_l⌝ ∗ PL σ_r'
    }})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Π_l "putc" (putc_fn_spec P) ∗ □ splittable P PL.
  Proof.
    iIntros "#? #? HPL % %Hσi_s  #Hs".

    iMod (mstate_var_alloc Z) as (γ) "Hγ".
    iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    set P := (λ (v : Z), ∃ σ Φg, PL σ ∗ spec_state v ∗
                           ⥥ₜ({{σ' Π, ⌜σ' = σ⌝ ∗ ⌜Π = Π_r⌝ ∗ TGT putc_spec @ Π {{Φg}}}}))%I.

    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Tgt () Π_r e). rewrite {2}Hσi_s.
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
      iApply sim_putc_spec.
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

End sim_putc.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⊕ ⟦putc⟧_spec ⪯ NB *)
(* ********************************************************************************************** *)

Section Sharing.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_spec : spec rec_event unit void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    TNb.

  (* Maybe first do a simple example where putc can be called with arbitrary value *)
  (* Maybe factor out a file with the specs for some programs - e.g. getc, and new 2 versions of putc (old is for echo not putc (Or maybe it is source?)) *)
  Let m_t2 := rec_link_trans {["getc"]} {["putc"]} (spec_trans rec_event Z) (spec_trans rec_event Z).
  Let m_t := rec_link_trans {["echo"]} {["getc"; "putc"]} rec_trans m_t2.

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
      iIntros (?) "[-> ?]".
      iApply sim_tgt_rec_LetE. iModIntro => /=.

      iMod ("HRP" with "[$] [$]") as "[? ?]".

      iApply ("IH" with "[$] [$]").
    }

    iApply ("H" with "[$] [$]").
  Qed.


  Lemma echo_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (MLFRun None, [], rec_init echo_prog, (MLFRun None, [], (getc_spec, 0), (putc_spec, 0))) ⪯{m_t,
      spec_trans rec_event ()} (echo_spec, ()).
  Proof.
    iIntros "[#Hfns Hh] /=".

    iMod (mstate_var_alloc (m_state (spec_trans rec_event ()))) as (γs) "Hγs".
    iMod (mstate_var_alloc (m_state m_t)) as (γt) "Hγt".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's spec state *)
    iMod (mstate_var_alloc ()) as (γs_s) "?".
    iMod (mstate_var_split γs_s tt with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    destruct!/=. case_match; destruct!/=.

    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".
    iApply (sim_gen_expr_intro _ tt with "[Hγs_s] [-]"); [simpl; done..|].

    iEval (unfold echo_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)). rewrite bind_bind.
    setoid_rewrite bind_ret_l.
    iApply sim_gen_TVis. iIntros "% Hγs_s %% [-> [-> _ ]]".

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iIntros "Hγs". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".

    iApply (sim_gen_expr_intro _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iIntros "Hγs". iDestruct (mstate_var_merge with "Hγs_s Hγs_s'") as "[_ Hγs_s]".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* getc and putc modules *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt2_g) "Hγt2_g".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt2_p) "Hγt2_p".

    (* echo rec module *)
    iMod (mstate_var_alloc (m_state rec_trans)) as (γt_e) "Hγt_e".

    (* Inner linking module *)
    iMod (mstate_var_alloc (m_state m_t2)) as (γt2) "Hγt2".

    (* call stack of linking modules *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γt_q) "Hγt_q".
    iMod (mstate_var_alloc (list seq_product_case)) as (γt2_q) "Hγt2_q".

    (* Linking events to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γt_oe) "Hγt_oe".
    iMod (mstate_var_alloc (option rec_ev)) as (γt2_oe) "Hγt2_oe".

    iApply (sim_tgt_link_left_const_run γt_q γt_e γt2 γt_oe with "[$] [$] [$] [$] [-]").
    iIntros "Hγt_q Hγt2 Hγt_oe".

    iMod (heapUR_alloc_blocks _ (h_blocks h) with "Hh") as "[Hh _]". { set_solver. }
    rewrite right_id_L heap_from_blocks_h_blocks.

    set (Π_e := tgt_link_left_constP _ _ _ _ _ _).
    set (Π_s := sim_src_constP γt γκ (m_t := m_t) (m_s := spec_trans rec_event ())).

    iApply (sim_gen_expr_intro _ [] with "[Hh]"). { done. } { by iFrame. }

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.

    iApply sim_gen_expr_ctx. iIntros "#?".

    (* Variable for invariant of state of putc module *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γip) "Hγip".
    iMod (mstate_var_split γip (putc_spec, 0) with "[$]") as "[Hγip Hγip']".

    set PL := (γt2_g ⤳@{m_state (spec_trans rec_event Z)} - ∗
               γt2_p ⤳@{m_state (spec_trans rec_event Z)} - ∗
               γt_oe ⤳ @None rec_ev ∗ γt_q ⤳ [None : seq_product_case] ∗
               γt2_oe ⤳@{option rec_ev} - ∗ γt2_q ⤳@{list seq_product_case} -)%I.

    set PGL := (λ σ_g, PL ∗ ∃ σ_p, γip ⤳ σ_p ∗ γt2 ⤳ ((MLFRun None, nil, σ_g, σ_p) : m_state m_t2))%I.

    iDestruct (sim_getc _ Π_e _ PGL (getc_spec, 0) with "[$] [] [$] [//] [//]") as "H". 1: by iApply (rec_fn_intro with "[$]").

    iMod ("H" with "[]") as "[%Pg [HPg [#Hgetc #Hsplitg]]]".

    (* Prove that I can switch to the getc module *)
    {
      iIntros "!> %% [% [% [% [[[Hγt2_g [Hγt2_p [Hγt_oe [Hγt_q [Hγt2_oe Hγt2_q]]]]] [% [Hγip Hγt2]]] [% HC]]]]]" => /=. subst.
      iIntros (???) "Hγt_q' Hγt_e Hγt2' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt2 Hγt2'") as "[<- Hγt2]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".

      iIntros (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.

      iApply (sim_tgt_link_right_const_recv γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_e Hγt_oe".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
      iIntros (???) "Hγt_q' Hγt_e' Hγt2 Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_e Hγt_e'") as "[<- Hγt_e]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]" => /=.
      iIntros (?).
      destruct!/=. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_const_run γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_e Hγt_oe".

      iApply (sim_tgt_link_left_const_recv γt2_q γt2_g γt2_p γt2_oe with "[$] [Hγt2_g] [Hγt2_p] [$] [-]"). 1-2: done.
      iIntros "Hγt2_q Hγt2_p Hγt2_oe".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]"=> /=.
      iIntros (???) "Hγt2_q' Hγt2_g Hγt2_p' Hγt2_oe'".

      iDestruct (mstate_var_merge with "Hγt2_p Hγt2_p'") as "[<- Hγt2_p]".
      iDestruct (mstate_var_merge with "Hγt2_oe Hγt2_oe'") as "[<- Hγt2_oe]".
      iDestruct (mstate_var_merge with "Hγt2_q Hγt2_q'") as "[<- Hγt2_q]".
      iIntros (?). simplify_eq.

      iApply (sim_tgt_link_left_const_run γt2_q γt2_g γt2_p γt2_oe with "[$] [Hγt2_g] [Hγt2_p] [$] [-]"). 1-2: done.
      iIntros "Hγt2_q Hγt2_p Hγt2_oe".
      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.
      iIntros (???) "Hγt2_q' Hγt2_g Hγt2_p' Hγt2_oe'".

      iDestruct (mstate_var_merge with "Hγt2_p Hγt2_p'") as "[<- Hγt2_p]".
      iDestruct (mstate_var_merge with "Hγt2_oe Hγt2_oe'") as "[<- Hγt2_oe]".
      iDestruct (mstate_var_merge with "Hγt2_q Hγt2_q'") as "[<- Hγt2_q]".

      iIntros (??????). destruct!/=.
      iIntros (???) "Hγt_q' Hγt_e' Hγt2 Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_e Hγt_e'") as "[<- Hγt_e]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".

      iIntros (??????). destruct!/=.

      iApply (sim_tgt_link_left_const_recv γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt2 Hγt_oe".
      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.

      iIntros (?) "%% Hγt_q' Hγt_e Hγt2' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iDestruct (mstate_var_merge with "Hγt2 Hγt2'") as "[<- Hγt2]".

      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_const_run γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt2 Hγt_oe".
      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitg" with "HPg") as "[% [[HPL [% [Hγip' Hγt2]]] HPg]]".
    iDestruct (mstate_var_merge γip with "[$] [$]") as "[-> Hγip]".

    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γig) "Hγig".
    iMod (mstate_var_split γig σ0 with "[$]") as "[Hγig Hγig']".

    set PPL := (λ σ_p, PL ∗ ∃ σ_g, γig ⤳ σ_g ∗ γt2 ⤳ ((MLFRun None, nil, σ_g, σ_p) : m_state m_t2))%I.

    iDestruct (sim_putc _ Π_e _ PPL (putc_spec, 0) with "[$] [] [$] [//] [//]") as "H". 1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pp [HPp [#Hputc #Hsplitp]]]".

    {
      iIntros "!> %% [% [% [% [[[Hγt2_g [Hγt2_p [Hγt_oe [Hγt_q [Hγt2_oe Hγt2_q]]]]] [% [Hγig Hγt2]]] [% HC]]]]]" => /=. subst.
      iIntros (???) "Hγt_q' Hγt_e Hγt2' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt2 Hγt2'") as "[<- Hγt2]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".

      iIntros (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.

      iApply (sim_tgt_link_right_const_recv γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_e Hγt_oe".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
      iIntros (???) "Hγt_q' Hγt_e' Hγt2 Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_e Hγt_e'") as "[<- Hγt_e]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]" => /=.
      iIntros (?).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_const_run γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt_e Hγt_oe".

      iApply (sim_tgt_link_right_const_recv γt2_q γt2_g γt2_p γt2_oe with "[$] [Hγt2_g] [Hγt2_p] [$] [-]"). 1-2: done.
      iIntros "Hγt2_q Hγt2_g Hγt2_oe".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]"=> /=.
      iIntros (???) "Hγt2_q' Hγt2_g' Hγt2_p Hγt2_oe'".

      iDestruct (mstate_var_merge with "Hγt2_g Hγt2_g'") as "[<- Hγt2_g]".
      iDestruct (mstate_var_merge with "Hγt2_oe Hγt2_oe'") as "[<- Hγt2_oe]".
      iDestruct (mstate_var_merge with "Hγt2_q Hγt2_q'") as "[<- Hγt2_q]".
      iIntros (?). simplify_eq.

      iApply (sim_tgt_link_right_const_run γt2_q γt2_g γt2_p γt2_oe with "[$] [Hγt2_g] [Hγt2_p] [$] [-]"). 1-2: done.
      iIntros "Hγt2_q Hγt2_g Hγt2_oe".
      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.
      iIntros (???) "Hγt2_q' Hγt2_g' Hγt2_p Hγt2_oe'".

      iDestruct (mstate_var_merge with "Hγt2_g Hγt2_g'") as "[<- Hγt2_g]".
      iDestruct (mstate_var_merge with "Hγt2_oe Hγt2_oe'") as "[<- Hγt2_oe]".
      iDestruct (mstate_var_merge with "Hγt2_q Hγt2_q'") as "[<- Hγt2_q]".

      iIntros (??????). destruct!/=.
      iIntros (???) "Hγt_q' Hγt_e' Hγt2 Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_e Hγt_e'") as "[<- Hγt_e]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".

      iIntros (??????). destruct!/=.

      iApply (sim_tgt_link_left_const_recv γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt2 Hγt_oe".
      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.

      iIntros (?) "%% Hγt_q' Hγt_e Hγt2' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iDestruct (mstate_var_merge with "Hγt2 Hγt2'") as "[<- Hγt2]".

      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_const_run γt_q γt_e γt2 γt_oe with "[$] [Hγt_e] [Hγt2] [$] [-]"). 1-2: done.
      iIntros "Hγt_q Hγt2 Hγt_oe".
      iApply "HC". iSplit!. iFrame.
    }

    iDestruct ("Hsplitp" with "[$]") as "[% [[HPL [% [Hγig' ?]]] HPp]]".
    iDestruct (mstate_var_merge with "Hγig Hγig'") as "[<- Hγig]".
    iMod (mstate_var_split γip σ1 with "[$]") as "[Hγip Hγip']".
    iDestruct ("HPg" with "[$]") as "HPg".

    set Rg := (λ v, ∃ σ, (PGL σ -∗ Pg v) ∗ γig ⤳ σ ∗ γip ⤳@{m_state (spec_trans rec_event Z)} -)%I.
    set Rp := (λ v, ∃ σ, (PPL σ -∗ Pp v) ∗ γip ⤳ σ ∗ γig ⤳@{m_state (spec_trans rec_event Z)} -)%I.

    iApply (sim_echo _ Pg Pp Rg Rp with "[] Hgetc Hputc [] [$] [$]") => //. 1: by iApply (rec_fn_intro with "[$]").
    iModIntro.
    iSplitR.
    - iIntros (??) "? [% [HPp [? ?]]]". iDestruct ("Hsplitg" with "[$]") as "[% [[? [% [? ?]]] ?]]". iFrame.
      iMod (mstate_var_split γig σ3 with "[$]") as "[Hγig Hγig']". iModIntro.
      iDestruct (mstate_var_merge γip with "[$] [$]") as "[<- Hγip]".
      iFrame.
      iApply "HPp".
      iFrame.
    - iIntros (??) "? [% [HPg [? ?]]]". iDestruct ("Hsplitp" with "[$]") as "[% [[? [% [? ?]]] ?]]". iFrame.
      iMod (mstate_var_split γip σ3 with "[$]") as "[Hγip Hγip']". iModIntro.
      iDestruct (mstate_var_merge γig with "[$] [$]") as "[<- Hγig]".
      iFrame.
      iApply "HPg".
      iFrame.
Qed.

End Sharing.
