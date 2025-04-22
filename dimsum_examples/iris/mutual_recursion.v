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

Definition ping_spec_body : spec rec_event Z unit :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "ping");;
  v ← TGet;
  TAssume (vs = [ValNum v]);;
  TPut (v + 1);;
  TVis (Outgoing, ERCall "pong" [ValNum v] h).

Definition ping_spec : spec rec_event Z void :=
  Spec.forever(ping_spec_body).

Definition pong_spec_body : spec rec_event Z unit :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "pong");;
  v ← TGet;
  TAssume (vs = [ValNum v]);;
  TPut (v + 1);;
  TVis (Outgoing, ERCall "ping" [ValNum (v + 1)] h).

Definition pong_spec : spec rec_event Z void :=
  Spec.forever(pong_spec_body).

Section sim_ping.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  (* Lemma sim_ping_spec `{!specGS} Π Φ : *)
  (*   switch Π ({{ κ σ1 POST, *)
  (*     ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗ *)
  (*   POST Tgt _ _ ({{ σ' Π', *)
  (*     ∃ v, ⌜f = "ping"⌝ ∗ ⌜es = [ValNum v]⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗ *)
  (*   switch Π' (λ κ (σ : m_state (spec_trans rec_event Z)) POST, *)
  (*     ⌜κ = Some (Outgoing, ERCall "pong" [ValNum v] h)⌝ ∗ spec_state (v + 1) ∗ *)
  (*   POST Tgt _ _ ({{σ' Π'', *)
  (*     ⌜σ' = σ⌝ ∗ ⌜Π'' = Π⌝ ∗ TGT pong_spec @ Π {{ Φ }} *)
  (*   }}))}})}}) -∗ *)
  (*   TGT ping_spec @ Π {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hs". *)
  (*   rewrite /ping_spec unfold_forever /TReceive bind_bind -/ping_spec bind_bind. *)
  (*   iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>". *)
  (*   rewrite bind_bind. setoid_rewrite bind_ret_l. *)
  (*   iApply (sim_gen_TVis with "[-]"). *)
  (*   iIntros (v') "Hγ' !>". *)
  (*   iIntros (??) "[% [% HΠ]]". *)
  (*   subst. *)
  (*   iApply "Hs" => /=. iSplit!. iIntros (??) => /=. *)
  (*   iDestruct 1 as (???) "[Hγ [% Hs']]". subst. *)
  (*   iApply (sim_gen_expr_intro _ tt with "[Hγ']"); simpl; [done..|]. rewrite bind_bind. *)
  (*   iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_gen_TGet with "[-]"). iSplit. 1: done. iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_gen_TPut with "[Hγ]"). 1: done. *)
  (*   iIntros "Hγ !>". *)
  (*   iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hγ'". *)
  (*   iDestruct (mstate_var_agree with "Hγ Hγ'") as "<-". *)
  (*   iIntros "!> /=". *)
  (*   iIntros (??) "[% [% HΠ']]" => /=. simplify_eq. *)
  (*   iApply "Hs'". iSplit!. iFrame. *)
  (*   iIntros (??) "[-> [-> HC]]". *)
  (*   iApply "HΠ" => /=. by iFrame. *)
  (* Qed. *)

  (* Definition getc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ := *)
  (*   ∃ v, P v ∗ ⌜es = []⌝ ∗ POST (λ ret, ⌜ret = v⌝ ∗ P (v + 1))%I. *)

  (* Lemma sim_getc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) (σi : (m_state (spec_trans rec_event Z))) : *)
  (*   rec_fn_auth fns -∗ *)
  (*   "getc" ↪ None -∗ *)
  (*   PL σi -∗ *)
  (*   ⌜σi.1 ≡ getc_spec⌝ -∗ *)
  (*   ⌜σi.2 = 0⌝ -∗ *)
  (*   □ switch_link_fixed Tgt Π_l (spec_trans _ Z) Π_r ({{σ_l POST, *)
  (*     ∃ h v σg, PL σg ∗ *)
  (*   POST (ERCall "getc" [] h) σg ({{σ_r Π_r', *)
  (*   switch_link Tgt Π_r' ({{σ_r' POST, *)
  (*     ∃ h', *)
  (*   POST (ERReturn (ValNum v) h') _ σ_l ({{_ Π_l', *)
  (*     ⌜Π_l' = Π_l⌝ ∗ PL σ_r' *)
  (*   }})}})}})}}) -∗ *)
  (*   |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Π_l "getc" (getc_fn_spec P) ∗ □ splittable P PL. *)
  (* Proof. *)
  (*   iIntros "#? #? HPL %<-  #Hs". *)

  (*   iMod (mstate_var_alloc Z) as (γ) "Hγ". *)
  (*   iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']". *)
  (*   pose (HS := SpecGS γ). *)

  (*   set P := (λ (v : Z), ∃ σ Φg, PL σ ∗ spec_state v ∗ *)
  (*                          ⥥ₜ({{σ' Π, ⌜σ' = σ⌝ ∗ ⌜Π = Π_r⌝ ∗ TGT getc_spec @ Π {{Φg}}}}))%I. *)

  (*   iExists P. *)
  (*   iModIntro. iSplit!. *)
  (*   - iExists _, (λ e, sim_post Tgt () Π_r e). *)
  (*     iFrame. *)
  (*     iIntros (??) "[-> [-> H]]" => /=. *)
  (*     iApply (sim_gen_expr_intro with "[Hγ]") => /= //. *)
  (*   - iIntros "!> %% [% [[% [% [HPL [Hγ Hg]]]] [-> HΦ]]]". *)
  (*     iApply (sim_tgt_rec_Call_external with "[$]"). *)
  (*     iIntros (???) "#?Htoa !>". *)
  (*     iIntros (? σr) "[-> [-> HΠr]]" => /=. subst. *)
  (*     iApply "Hs" => /=. iFrame. iSplit!. *)
  (*     iIntros (? Π'') "[-> [-> Hs']]" => /=. *)
  (*     iApply "Hg". iSplit!. *)
  (*     iApply sim_getc_spec. *)
  (*     iIntros (??) "[% [% [% [-> Hg]]]]" => /=. *)
  (*     iApply "Hs'" => /=. iSplit!. *)
  (*     iIntros (? Πs') "[% [% Hs']]". simplify_eq. *)
  (*     iApply "Hg". iFrame. iSplit!. *)
  (*     iIntros (??) "[-> [? Hg]]" => /=. *)
  (*     iApply "Hs'" => /=. iSplit!. *)
  (*     iIntros (? Πr') "[-> Hs']". *)
  (*     iApply sim_tgt_rec_Waiting_raw. *)
  (*     iSplit. { iIntros. iModIntro. iApply "Hs'". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. } *)
  (*     iIntros (???) "!>". iApply "Hs'" => /=. iSplit!. iIntros (??) "[% [% [% HQ]]]". simplify_eq. *)
  (*     iApply "HΠr". iSplit!. iFrame. *)
  (*     iApply "HΦ". iFrame. iSplit!. *)
  (*     iIntros (??) "[-> [-> ?]]" => /=. *)
  (*     iApply "Hg". by iSplit!. *)
  (*   - iIntros "!> % [% [% [? ?]]]". *)
  (*     iFrame. *)
  (*     iIntros "HPL". *)
  (*     iFrame. *)
  (* Qed. *)

End sim_ping.

Section sim_pong.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  (* Lemma sim_getc_spec `{!specGS} Π Φ : *)
  (*   switch Π ({{ κ σ1 POST, *)
  (*     ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗ *)
  (*   POST Tgt _ _ ({{ σ' Π', *)
  (*     ∃ v, ⌜f = "getc"⌝ ∗ ⌜es = []⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗ *)
  (*   switch Π' (λ κ (σ : m_state (spec_trans rec_event Z)) POST, *)
  (*     ⌜κ = Some (Outgoing, ERReturn (ValNum v) h)⌝ ∗ spec_state (v + 1) ∗ *)
  (*   POST Tgt _ _ ({{σ' Π'', *)
  (*     ⌜σ' = σ⌝ ∗ ⌜Π'' = Π⌝ ∗ TGT getc_spec @ Π {{ Φ }} *)
  (*   }}))}})}}) -∗ *)
  (*   TGT getc_spec @ Π {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hs". *)
  (*   rewrite {2}/getc_spec unfold_forever /TReceive bind_bind -/getc_spec bind_bind. *)
  (*   iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>". *)
  (*   rewrite bind_bind. setoid_rewrite bind_ret_l. *)
  (*   iApply (sim_gen_TVis with "[-]"). *)
  (*   iIntros (v') "Hγ' !>". *)
  (*   iIntros (??) "[% [% HΠ]]". *)
  (*   subst. *)
  (*   iApply "Hs" => /=. iSplit!. iIntros (??) => /=. *)
  (*   iDestruct 1 as (???) "[Hγ [% Hs']]". subst. *)
  (*   iApply (sim_gen_expr_intro _ tt with "[Hγ']"); simpl; [done..|]. rewrite bind_bind. *)
  (*   iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_gen_TGet with "[-]"). *)
  (*   iSplit. 1: done. *)
  (*   iIntros "!>". rewrite bind_bind. *)
  (*   iApply (sim_gen_TPut with "[Hγ]"). 1: done. *)
  (*   iIntros "Hγ". iIntros "!>". *)
  (*   iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hγ'". *)
  (*   iDestruct (mstate_var_agree with "Hγ Hγ'") as "<-". *)
  (*   iIntros "!> /=". *)
  (*   iIntros (??) "[% [% HΠ']]" => /=. simplify_eq. *)
  (*   iApply "Hs'". iSplit!. iFrame. *)
  (*   iIntros (??) "[-> [-> HC]]". *)
  (*   iApply "HΠ" => /=. by iFrame. *)
  (* Qed. *)

  (* Definition getc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ := *)
  (*   ∃ v, P v ∗ ⌜es = []⌝ ∗ POST (λ ret, ⌜ret = v⌝ ∗ P (v + 1))%I. *)

  (* Lemma sim_getc fns Π_l Π_r (PL : m_state (spec_trans rec_event Z) → iProp Σ) (σi : (m_state (spec_trans rec_event Z))) : *)
  (*   rec_fn_auth fns -∗ *)
  (*   "getc" ↪ None -∗ *)
  (*   PL σi -∗ *)
  (*   ⌜σi.1 ≡ getc_spec⌝ -∗ *)
  (*   ⌜σi.2 = 0⌝ -∗ *)
  (*   □ switch_link_fixed Tgt Π_l (spec_trans _ Z) Π_r ({{σ_l POST, *)
  (*     ∃ h v σg, PL σg ∗ *)
  (*   POST (ERCall "getc" [] h) σg ({{σ_r Π_r', *)
  (*   switch_link Tgt Π_r' ({{σ_r' POST, *)
  (*     ∃ h', *)
  (*   POST (ERReturn (ValNum v) h') _ σ_l ({{_ Π_l', *)
  (*     ⌜Π_l' = Π_l⌝ ∗ PL σ_r' *)
  (*   }})}})}})}}) -∗ *)
  (*   |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Π_l "getc" (getc_fn_spec P) ∗ □ splittable P PL. *)
  (* Proof. *)
  (*   iIntros "#? #? HPL %<-  #Hs". *)

  (*   iMod (mstate_var_alloc Z) as (γ) "Hγ". *)
  (*   iMod (mstate_var_split γ σi.2 with "[$]") as "[Hγ Hγ']". *)
  (*   pose (HS := SpecGS γ). *)

  (*   set P := (λ (v : Z), ∃ σ Φg, PL σ ∗ spec_state v ∗ *)
  (*                          ⥥ₜ({{σ' Π, ⌜σ' = σ⌝ ∗ ⌜Π = Π_r⌝ ∗ TGT getc_spec @ Π {{Φg}}}}))%I. *)

  (*   iExists P. *)
  (*   iModIntro. iSplit!. *)
  (*   - iExists _, (λ e, sim_post Tgt () Π_r e). *)
  (*     iFrame. *)
  (*     iIntros (??) "[-> [-> H]]" => /=. *)
  (*     iApply (sim_gen_expr_intro with "[Hγ]") => /= //. *)
  (*   - iIntros "!> %% [% [[% [% [HPL [Hγ Hg]]]] [-> HΦ]]]". *)
  (*     iApply (sim_tgt_rec_Call_external with "[$]"). *)
  (*     iIntros (???) "#?Htoa !>". *)
  (*     iIntros (? σr) "[-> [-> HΠr]]" => /=. subst. *)
  (*     iApply "Hs" => /=. iFrame. iSplit!. *)
  (*     iIntros (? Π'') "[-> [-> Hs']]" => /=. *)
  (*     iApply "Hg". iSplit!. *)
  (*     iApply sim_getc_spec. *)
  (*     iIntros (??) "[% [% [% [-> Hg]]]]" => /=. *)
  (*     iApply "Hs'" => /=. iSplit!. *)
  (*     iIntros (? Πs') "[% [% Hs']]". simplify_eq. *)
  (*     iApply "Hg". iFrame. iSplit!. *)
  (*     iIntros (??) "[-> [? Hg]]" => /=. *)
  (*     iApply "Hs'" => /=. iSplit!. *)
  (*     iIntros (? Πr') "[-> Hs']". *)
  (*     iApply sim_tgt_rec_Waiting_raw. *)
  (*     iSplit. { iIntros. iModIntro. iApply "Hs'". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. } *)
  (*     iIntros (???) "!>". iApply "Hs'" => /=. iSplit!. iIntros (??) "[% [% [% HQ]]]". simplify_eq. *)
  (*     iApply "HΠr". iSplit!. iFrame. *)
  (*     iApply "HΦ". iFrame. iSplit!. *)
  (*     iIntros (??) "[-> [-> ?]]" => /=. *)
  (*     iApply "Hg". by iSplit!. *)
  (*   - iIntros "!> % [% [% [? ?]]]". *)
  (*     iFrame. *)
  (*     iIntros "HPL". *)
  (*     iFrame. *)
  (* Qed. *)

End sim_pong.

Section Mutual.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition mutual_spec : spec rec_event unit void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "ping");;
    TAssume (vs = [ValNum 0]);;
    TNb.

  Let m_t := rec_link_trans {["ping"]} {["pong"]} (spec_trans rec_event Z) (spec_trans rec_event Z).

  (* Lemma sim_echo Π (P Q RP RQ : Z → iProp Σ) v : *)
  (*   "echo" ↪ Some echo_rec -∗ *)
  (*   □ rec_fn_spec_hoare Tgt Π "getc" (getc_fn_spec P) -∗ *)
  (*   □ rec_fn_spec_hoare Tgt Π "putc" (putc_fn_spec Q) -∗ *)
  (*   □ overlapping P Q RP RQ -∗ *)
  (*   P v -∗ *)
  (*   RQ v -∗ *)
  (*   rec_fn_spec_hoare Tgt Π "echo" (λ es POST, ⌜es = []⌝). *)
  (* Proof. *)
  (*   iIntros "#? #Hgetc #Hputc #[HRQ HRP] HP RQ %% ->". *)
  (*   iApply sim_gen_expr_ctx. iIntros "#?". *)
  (*   iAssert (∀ Φ v, P v -∗ RQ v -∗ TGT Call (Val (ValFn "echo")) [] @ Π {{ Φ }})%I as "H". *)
  (*   { *)
  (*     iApply (ord_loeb with "[$] []"). *)
  (*     iIntros "!>". iIntros "#IH %% ? ?". *)

  (*     iApply (sim_tgt_rec_Call_internal with "[$]") => //. *)
  (*     iModIntro => /=. *)
  (*     iApply (sim_tgt_rec_AllocA); [done|]. *)
  (*     iIntros "% _ !>" => /=. *)
  (*     iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=. *)

  (*     iApply "Hgetc". *)
  (*     iFrame. iSplit! => /=. iIntros (?) "[-> ?]". *)

  (*     iApply sim_tgt_rec_LetE. iModIntro => /=. *)
  (*     iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=. *)
  (*     iMod ("HRQ" with "[$] [$]") as "[? ?]". *)

  (*     iApply "Hputc". *)
  (*     iFrame. iSplit!. *)
  (*     iIntros (?) "[-> ?]". *)
  (*     iApply sim_tgt_rec_LetE. iModIntro => /=. *)

  (*     iMod ("HRP" with "[$] [$]") as "[? ?]". *)

  (*     iApply ("IH" with "[$] [$]"). *)
  (*   } *)

  (*   iApply ("H" with "[$] [$]"). *)
  (* Qed. *)

  Lemma mutual_sim :
    bi_emp_valid ((MLFRun None, [], (ping_spec, 0), (pong_spec, 0)) ⪯{m_t,
      spec_trans rec_event ()} (mutual_spec, ())).
  Proof.
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

    iEval (unfold mutual_spec). rewrite /TReceive bind_bind.
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

    (* ping and pong modules *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt_l) "Hγt_l".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt_r) "Hγt_r".

    (* call stack of linking modules *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γt_q) "Hγt_q".

    (* Linking events to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γt_oe) "Hγt_oe".

    iApply (sim_tgt_link_left_const_recv with "Hγt_q Hγt_l [$] [$]"). iIntros " Hγt_q Hγt_r Hγt_oe".

    (* Left and right spec state *)
    iMod (mstate_var_alloc Z) as (γtl_s) "Hγtl_s".
    iMod (mstate_var_alloc Z) as (γtr_s) "Hγtr_s".
    pose (HpingSpec := SpecGS γtl_s).
    pose (HpongSpec := SpecGS γtr_s).
    iMod (mstate_var_split γtl_s 0 with "[$]") as "[Hγtl_s Hγtl_s']".
    (* iMod (mstate_var_split γtr_s 0 with "[$]") as "[Hγtr_s Hγtr_s']". *)

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HpingSpec) _ _ )_ tt with "[Hγtl_s]") => //=.

    iApply sim_gen_expr_ctx. iIntros "#?".

    set Π := (tgt_link_left_constP _ _ _ _ _ _).


    iAssert (∀ Φ (σ : m_state (spec_trans rec_event ())) (q : list seq_product_case) (v : Z), γs ⤳ σ -∗ γs_s ⤳ - -∗ γt_q ⤳ q -∗ γt_r ⤳ (pong_spec, v) -∗
                        γt_oe ⤳ Some (ERCall "ping" [ValNum v] h) -∗ γtr_s ⤳ - -∗ γtl_s ⤳ v -∗
                    TGT ping_spec @ Π {{ Φ }})%I as "H".
    {
      iApply (ord_loeb with "[$] []").
      iIntros "!>". iIntros "#IH % % % % Hγs Hγs_s Hγt_q Hγt_r Hγt_oe Hγtr_s Hγtl_s".
      admit. }

    (* iEval (rewrite /ping_spec unfold_forever -/ping_spec /ping_spec_body bind_bind bind_bind). *)

    (* iApply (sim_tgt_TExist (H := HpingSpec) with "[-]"). iIntros ([[??]?]) "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TVis (H := HpingSpec) with "[-]"). iIntros (v1) "Hγtl_s !>". *)
    (* iIntros (??) "/= [% [% _]]". simplify_eq. *)

    (* iApply (tgt_link_left_constP_elim_recv with "Hγt_q [Hγt_r] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe /= %". simplify_eq. *)

    (* iApply (sim_tgt_link_left_const_run γt_q γt_l with "[$] [Hγt_l] [Hγt_r] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_r Hγt_oe". *)

    (* iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HpingSpec) _ _ )_ tt with "[Hγtl_s]") => //=. *)

    (* setoid_rewrite bind_ret_l. rewrite bind_bind. *)
    (* iApply (sim_tgt_TAssume (H := HpingSpec) with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TGet (H := HpingSpec) with "[-]"). iSplit => //. iModIntro. rewrite bind_bind. *)
    (* iApply (sim_tgt_TAssume (H := HpingSpec) with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TPut (H := HpingSpec) with "[Hγtl_s']"); [done|]. iIntros "Hγtl_s !>". *)
    (* iApply (sim_gen_TVis (H := HpingSpec) with "[-]"). iIntros (v2) "Hγtl_s' !>". *)

    (* iIntros (??) "/= [% [% _]]". simplify_eq. *)

    (* iApply (tgt_link_left_constP_elim_run with "Hγt_q [Hγt_r] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe /= %%%%%%". *)
    (* destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //. *)

    (* iDestruct (mstate_var_agree with "Hγtl_s Hγtl_s'") as "<-". *)

    (* iApply (sim_tgt_link_right_const_recv γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]");[done..|]. *)
    (* iIntros "Hγt_q Hγt_l Hγt_oe". *)

    (* iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HpongSpec) _ _ )_ tt with "[Hγtr_s]") => //=. *)

    (* iEval (rewrite /pong_spec unfold_forever -/pong_spec /pong_spec_body bind_bind bind_bind). *)

    (* iApply (sim_tgt_TExist (H := HpongSpec) with "[-]"). iIntros ([[??]?]) "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TVis (H := HpongSpec) with "[-]"). iIntros (v3) "Hγtr_s !>". *)
    (* iIntros (??) "/= [% [% _]]". simplify_eq. *)

    (* iApply (tgt_link_right_constP_elim_recv with "Hγt_q [Hγt_l] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe /= %". simplify_eq. *)

    (* iApply (sim_tgt_link_right_const_run γt_q γt_l with "[$] [Hγt_l] [Hγt_r] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_l Hγt_oe". *)

    (* iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HpongSpec) _ _ ) _ tt with "[Hγtr_s]") => //=. *)
    (* setoid_rewrite bind_ret_l. rewrite bind_bind. *)
    (* iApply (sim_tgt_TAssume (H := HpongSpec) with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TGet (H := HpongSpec) with "[-]"). iSplit => //. iModIntro. rewrite bind_bind. *)
    (* iApply (sim_tgt_TAssume (H := HpongSpec) with "[-]"); [done|]. iIntros "!>". rewrite bind_bind. *)
    (* iApply (sim_gen_TPut (H := HpongSpec) with "[Hγtr_s']"); [done|]. iIntros "Hγtr_s !>". *)
    (* iApply (sim_gen_TVis (H := HpongSpec) with "[-]"). iIntros (v4) "Hγtr_s' !>". *)

    (* iIntros (??) "/= [% [% _]]". simplify_eq. *)

    (* iApply (tgt_link_right_constP_elim_run with "Hγt_q [Hγt_l] [$] [-]") => //. *)
    (* iIntros "Hγt_q Hγt_l Hγt_r Hγt_oe /= %%%%%%". *)
    (* destruct!/=. rewrite bool_decide_true //. *)

    (* iDestruct (mstate_var_merge with "Hγtr_s Hγtr_s'") as "[<- Hγtr_s]". *)

    (* iApply (sim_tgt_link_left_const_recv γt_q γt_l γt_r γt_oe with "[$] [Hγt_l] [Hγt_r] [$] [-]");[done..|]. *)
    (* iIntros "Hγt_q Hγt_r Hγt_oe". *)

    (* iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HpingSpec) _ _ )_ tt with "[Hγtl_s]") => //=. *)
    iDestruct ("H" $! _ σ _ 0%Z with "[$] [$] [$] [Hγt_r] [$] [$] [Hγtl_s']") as "Hdone". 1-2: done.

    iClear "H".
    Set Printing All.
    rewrite sim_gen_expr_unfold.
    unfold sim_gen_expr.
    Set Printin

    iApply sim_gen_expr_stop. iApply "Hdone".
    { done. Set Printing Coercions.  Set Printing All.  }
    iApply "Hγt_r".

Qed.

End Mutual.
