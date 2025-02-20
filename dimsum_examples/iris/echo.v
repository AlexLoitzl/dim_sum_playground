From iris.bi.lib Require Import fixpoint.
From iris.proofmode Require Import proofmode.

Section bi_loop.
  Context {PROP : bi} {A : Type} (body : (A → PROP) → (A → PROP)).

  Definition bi_loop_pre (bi_loop : leibnizO A -d> PROP) :
    leibnizO A -d> PROP := λ a,
    (∀ Φ, □ (∀ x, bi_loop x -∗ Φ x) -∗ body Φ a)%I.

  Global Instance bi_loop_pre_ne n:
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) bi_loop_pre.
  Proof.
    move => ?? Hsim ?? ->. rewrite /bi_loop_pre.
    repeat (f_equiv || eapply Hsim || reflexivity).
  Qed.

  Lemma bi_loop_pre_mono loop1 loop2:
    ⊢ □ (∀ a, loop1 a -∗ loop2 a)
    → ∀ a , bi_loop_pre loop1 a -∗ bi_loop_pre loop2 a.
  Proof.
    iIntros "#Hinner" (a) "Hsim". iIntros (?) "#HC".
    iApply "Hsim". iIntros "!>" (?) "?". iApply "HC". by iApply "Hinner".
  Qed.

  Local Instance bi_loop_pre_monotone :
    BiMonoPred bi_loop_pre.
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros (?) "Hsim" => /=. iApply bi_loop_pre_mono; [|done].
      iIntros "!>" (?) "HΠ". by iApply ("Hinner" $! _).
    - move => bi_loop Hsim n a1 a2 /= ?.
      apply bi_loop_pre_ne; eauto. move => ??? /=. by apply: Hsim.
  Qed.
End bi_loop.

Definition bi_loop {PROP : bi} {A} (body : (A → PROP) → (A → PROP)) (a : A) :=
  bi_greatest_fixpoint (bi_loop_pre body) a.

Section bi_loop.
  Context {PROP : bi} {A : Type} (body : (A → PROP) → (A → PROP)).

  Local Existing Instance bi_loop_pre_monotone.
  Lemma bi_loop_eq a:
    bi_loop body a ⊣⊢ bi_loop_pre body (bi_loop body) a.
  Proof. rewrite /bi_loop. apply: greatest_fixpoint_unfold. Qed.

  Lemma bi_loop_step a:
    (∀ Φ, □ (∀ a, bi_loop body a -∗ Φ a) -∗ body Φ a) ⊢ bi_loop body a.
  Proof. by rewrite bi_loop_eq. Qed.

  Lemma bi_loop_unfold a:
    bi_loop body a ⊢ body (bi_loop body) a.
  Proof. rewrite bi_loop_eq. iIntros "Hl". iApply "Hl". iIntros "!>" (?) "$". Qed.
End bi_loop.

From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO: upstream? *)
Arguments subst_static _ !_ /.

(*
echo() = let c := getc(); putc(c); echo()

getc_rec() = local l [1]; read(l, 1); return l[0]

read_asm := mov R8, __NR_READ; syscall; ret

putc_spec(c) = buffer += [c]; if * then write(buffer, len(buffer)); buffer = []


One refinement:
echo_spec (src) -> read -> getc_rec -> echo -> putc_spec -> echo_spec (src)

Another refinement
(src) -> read -> getc_rec -> dispatcher -> handler -> putc_spec -> (src)

where dispatcher is an assembly implementation of a callback dispatcher that reads
new input using getc and then dispatches it to all registered handlers.
The handlers can then register new handlers or remove existing handlers,
leading to some form of mutual recusion.
The dispatcher needs to be implemented in asm such that it can use equality to compare function pointers (necessary for removing).
Property to prove:
- Safety monitor on input, i.e. checks that a certain string is never emitted / stops processing after that?
  - might even prove a higher-order property where one gets a function pointer from the env at the beginning and then sanitises its input?
*)


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

Section echo.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_echo Π :
    "echo" ↪ Some echo_rec -∗
    rec_fn_spec_hoare Tgt Π "echo" ({{ es POST0, ⌜es = []⌝ ∗
      bi_loop ({{ LOOP _,
        rec_fn_spec_hoare Tgt Π "getc" ({{ es POST,
          ⌜es = []⌝ ∗
        POST ({{ c,
        rec_fn_spec_hoare Tgt Π "putc" ({{ es POST,
          ⌜es = [Val c]⌝ ∗
        POST ({{ _,
          LOOP tt
        }})}})}})}})}}) tt}}).
  Proof.
    iIntros "#?". iApply rec_fn_spec_hoare_ctx. iIntros "#?".
    set BODY := (X in bi_loop X).
    iApply ord_loeb; [done|]. iIntros "!> #IH".
    iIntros (es Φ). iDestruct 1 as (->) "HΦ".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "?".
    destruct ls as [|] => //=. iModIntro.
    iDestruct (bi_loop_unfold with "HΦ") as "HΦ".
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply "HΦ". iSplit!. iIntros (?) "HΦ".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply "HΦ". iSplit!. iIntros (?) "HΦ".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply "IH". iSplit!.
  Qed.

End echo.

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
(* Canonical Structure spec_mod_lang. *)

(* NOTE - In src position we only need to ensure `Outgoing Call` and any incoming event *)
(* This cannot be quite true, in case it's not undefined, I'll have to refine it ? *)

(* The statement holds, assuming the following restriction on Π.
   ...
 *)

  (* TODO : Are these two Lemmas incomparable??? - Yes! *)
  Lemma sim_src_TCallRet4 f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
        ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗
        ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
        POST Src _ (spec_trans rec_event S) ({{σ' Π',
          ⌜σ = σ'⌝ ∗  ∃ e,
          switch Π' ({{κ σ POST,
            ⌜κ = Some (Incoming, e)⌝ ∗
            (* TODO: Obligation? *)
            POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
              (* TODO - Here I don't care which Π, but I throw out Φ *)
              ⌜σ = σ''⌝ ∗
              (∀ v h', ⌜e = ERReturn v h'⌝ -∗
                       ⌜σ''.1 ≡ k (v, h')⌝ -∗
                       spec_state σ''.2 -∗
                       σ'' ≈{(spec_trans rec_event S)}≈>ₛ Π'')}})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "HC" => /=. rewrite /TCallRet bind_bind.
    iApply sim_gen_TVis. iIntros (s) "Hs". rewrite /switch_id. iIntros "% % /=". iIntros "[% [% ?]]". subst.
    iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]" => /=. subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_src_TExist _).
    rewrite bind_bind. iApply sim_gen_TVis. iIntros (s') "Hs". iIntros (??) "[% [% _]]" => /=.
    subst. iApply "HC" => /=. iSplit!.
    iIntros (??) "[% HC]". subst.
    destruct e.
    { iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|]. iApply sim_src_TUb. }
    iApply ("HC" $! ret h0 with "[//] [] [$]").
    by rewrite bind_ret_l.
  Qed.

  Lemma sim_src_TCallRet3 f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
        ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗
        ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
        POST Src _ (spec_trans rec_event S) ({{σ' Π',
          ⌜σ = σ'⌝ ∗  ∃ e,
          switch Π' ({{κ σ POST,
            ⌜κ = Some (Incoming, e)⌝ ∗
            POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
              ⌜σ = σ''⌝ ∗
              ⌜Π = Π''⌝ ∗
              (∀ v h', ⌜e = ERReturn v h'⌝ -∗ Φ (k (v, h'))) }})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "HC" => /=. rewrite /TCallRet bind_bind.
    iApply sim_gen_TVis. iIntros (s) "Hs". iIntros "% % /=". iIntros "[% [% HΠ]]". subst.
    iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]" => /=. subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_src_TExist _).
    rewrite bind_bind. iApply sim_gen_TVis. iIntros (s') "Hs". iIntros (??) "[% [% HΠ']]" => /=.
    subst. iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]". destruct!/=.
    iApply "HΠ". iSplit!. iSplitL "Hs". 1: done.
    destruct e. iApply sim_src_TUb.
    rewrite bind_ret_l.
    iApply sim_gen_expr_stop.
    by iApply "HC".
  Qed.

  Lemma switch_mono `{!dimsumGS Σ} {S' EV} (Π : option EV → S' → iProp Σ)
    (K1 K2 : option EV → S' → (tgt_src → ∀ EV2, ∀ m : mod_trans EV2, _ → iProp Σ) → iProp Σ) :
    switch Π K1 -∗
    (∀ κ σ P1 P2, K2 κ σ P1 -∗
                  (∀ ts (m : mod_trans EV) (Q1 Q2 : (m_state m → (option EV → m_state m → iProp Σ) → iProp Σ)),
                    P1 ts EV m Q1 -∗ (∀ σ Π, Q2 σ Π -∗ Q1 σ Π) -∗ P2 ts EV m Q2) -∗ K1 κ σ P2) -∗
    switch Π K2.
  Proof.
    iIntros "Hs Hmono" (??) "HK2". iApply "Hs".
    iApply ("Hmono" with "HK2").
    iIntros (????) "HQ Hmono". iIntros (??) "?". iApply "HQ". by iApply "Hmono".
  Qed.

  Lemma sim_src_TCallRet3' f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
        ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗
        ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
        POST Src _ (spec_trans rec_event S) ({{σ' Π',
          ⌜σ = σ'⌝ ∗  ∃ e,
          switch Π' ({{κ σ POST,
            ⌜κ = Some (Incoming, e)⌝ ∗
            (* TODO: Obligation? *)
            POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
              ⌜σ = σ''⌝ ∗
              ⌜Π = Π''⌝ ∗
              (∀ v h', ⌜e = ERReturn v h'⌝ -∗ SRC (k (v, h')) @ Π {{ Φ }})}})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "H". iApply sim_src_TCallRet4.
    iApply (switch_mono with "H") => /=.
    iIntros (????) "[% [% [% [% [% [% [% H1]]]]]]]".
    iIntros "H2". iSplit!. destruct!/=.
    (* set Q1 := (X in P1 _ _ _ X). *)
    (* set Q2 := (X in P2 _ _ _ X). *)
    iApply ("H2" $! Src (spec_trans rec_event S) with "H1").
    iIntros (??) "[% [% H]]" => /=. iSplit!.
    iApply (switch_mono with "H") => /=.
    iIntros (????) "[% H1]".
    iIntros "H2". iSplit!.
    iApply ("H2" with "H1").
    iIntros (??) "[% [% H]]" => /=. simplify_eq.
    iSplit!.
    iIntros.
    Admitted.

  Lemma sim_src_TCallRet4' f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
        ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗
        ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
        POST Src _ (spec_trans rec_event S) ({{σ' Π',
          ⌜σ = σ'⌝ ∗  ∃ e,
          switch Π' ({{κ σ POST,
            ⌜κ = Some (Incoming, e)⌝ ∗
            (* TODO: Obligation? *)
            POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
              ⌜σ = σ''⌝ ∗
              (∀ v h', ⌜e = ERReturn v h'⌝ -∗
                       ⌜σ''.1 ≡ k (v, h')⌝ -∗
                       spec_state σ''.2 -∗
                       σ'' ≈{(spec_trans rec_event S)}≈>ₛ Π'')}})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "H". iApply sim_src_TCallRet3.
    iApply (switch_mono with "H") => /=.
    iIntros (????) "[% [% [% [% [% [% [% H1]]]]]]]".
    iIntros "H2". iSplit!. destruct!/=.
    (* set Q1 := (X in P1 _ _ _ X). *)
    (* set Q2 := (X in P2 _ _ _ X). *)
    iApply ("H2" $! Src (spec_trans rec_event S) with "H1").
    iIntros (??) "[% [% H]]" => /=. iSplit!.
    iApply (switch_mono with "H") => /=.
    iIntros (????) "[% H1]".
    iIntros "H2". iSplit!.
    iApply ("H2" with "H1").
    iIntros (??) "[% H]" => /=. simplify_eq.
  Admitted.

End TCallRet.

Definition echo_spec_body : spec rec_event unit unit :=
  h ← TExist _;
  '(c, h') ← TCallRet "getc" [] h;
  TAssume (h = h');;
  h ← TExist _;
  '(_, h') ← TCallRet "putc" [c] h;
  TAssume (h = h');;
  TRet tt.

Definition echo_spec : spec rec_event unit void :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "echo");;
  TAssume (vs = []);;
  Spec.forever echo_spec_body.

Lemma echo_refines_echo_spec_direct :
  trefines (rec_mod echo_prog) (spec_mod echo_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  (* TODO: proof with tstep_i / go_s *)
Abort.

Section echo.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition switch_external' `{!dimsumGS Σ} {S EV} (Π : option EV → S → iProp Σ)
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

  Lemma sim_echo_spec Π Πs γσ_s (σ : m_state (spec_trans _ unit)) :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γσ_s ⤳ σ -∗
    ⌜σ.1 ≡ Spec.forever echo_spec_body⌝ -∗
    □ switch_external' Π (spec_trans _ unit) Πs ({{ _ σ POST,
        ∃ σ_s, γσ_s ⤳ σ_s ∗
      POST σ_s ({{ _ Π',
      ⌜Π' = Πs⌝ ∗
      switch Π' ({{ κ σ_s' POST,
       ⌜κ = None⌝ ∗
      POST Tgt _ _ ({{ σ' Π', ⌜σ' = σ⌝ ∗ ⌜Π' = Π⌝ ∗ γσ_s ⤳ σ_s'}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "echo" ({{ es _, ⌜es = []⌝}}).
  Proof.
    iIntros "#?#?#? Hγσ_s Hσ_s #Hswitch". iApply rec_fn_spec_hoare_ctx. iIntros "#?".
    iIntros (es Φ). iDestruct 1 as %->. iApply sim_echo; [done|]. iSplit!.
    set BODY := (X in bi_loop X).
    (* set EXT := (X in switch_external Π X). *)
    iRevert (σ) "Hγσ_s Hσ_s". iApply ord_loeb; [done|]. iIntros "!> #IH".
    iIntros (σ) "Hγσ_s %". iApply bi_loop_step. iIntros (?) "#HLOOP".
    iIntros (es ?). iDestruct 1 as (->) "HΦ".

    iMod (mstate_var_alloc unit) as (γ) "?".
    iMod (mstate_var_split γ σ.2 with "[$]") as "[Hγ ?]".
    pose (Hspec := SpecGS γ).

    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hswitch". iFrame. iSplit!.
    iIntros (??). iDestruct 1 as (->) "[% Hs]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite ->unfold_forever. rewrite {2}/echo_spec_body.
    rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    rewrite bind_bind.

    iApply sim_src_TCallRet3.
    iIntros (??) "(% & % & % & % & % & % & % & HC)"=> /=. simplify_eq.
    iApply "Hs". iSplit!.
    iIntros (??) "[% [% Hs]]" => /=. simplify_eq.
    iApply sim_gen_stop.
    iApply "Hs". iSplit!.
    iIntros (??) "[% [% ?]]" => /=. simplify_eq.

    iApply (sim_tgt_rec_Waiting_all_raw with "[-]").
    iIntros (?) "!>". iApply "Hswitch" => /=. iFrame. iSplit!. iIntros (??) "[<- [% Hs]]".
    iApply "HC". iSplit!. iIntros (??) => /=. iIntros "[% Hm]". iApply "Hs".
    simpl. iSplit!. iIntros (? Πroblem) "[% [% Hs]]" => /=. subst. iApply "Hm" => /=.
    iSplit!. rewrite /sim_post =>/=.
    iIntros (?????) "Hγ". simplify_eq.
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply sim_src_TAssume.
    iIntros (<-). iApply sim_gen_expr_None => /=.
    iIntros (? [] ?) "Hγ".  iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> [-> ?]]".
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ".
    iIntros (es ?). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns'' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hswitch". iFrame. iSplit!.
    iIntros (??). iDestruct 1 as (->) "[% Hs]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    rewrite bind_bind.

    iApply sim_src_TCallRet3.
    iIntros (??) "(% & % & % & % & % & % & % & HC)"=> /=. simplify_eq.
    iApply "Hs". iSplit!.
    iIntros (??) "[% [% Hs]]" => /=. simplify_eq.
    iApply sim_gen_stop.
    iApply "Hs". iSplit!.
    iIntros (??) "[% [% ?]]" => /=. simplify_eq.

    iApply (sim_tgt_rec_Waiting_all_raw with "[-]").
    iIntros (?) "!>". iApply "Hswitch" => /=. iFrame. iSplit!. iIntros (??) "[<- [% Hs]]".
    iApply "HC". iSplit!. iIntros (??) => /=. iIntros "[% Hm]". iApply "Hs".
    simpl. iSplit!. iIntros (? Πroblem) "[% [% Hs]]" => /=. subst. iApply "Hm" => /=.
    iSplit!. rewrite /sim_post =>/=.
    iIntros (?????) "Hγ". simplify_eq.
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply sim_src_TAssume.
    iIntros (<-). rewrite bind_ret_l. iApply sim_gen_expr_None => /=.
    iIntros (? [] ?) "Hγ".  iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> [-> Hγσ_s]]".
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ".
    iApply "HLOOP". by iApply ("IH" with "Hγσ_s").
  Qed.

  Lemma echo_spec_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (rec_init echo_prog) ⪯{rec_trans, spec_trans rec_event ()} (echo_spec, ()).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=".
    iMod (mstate_var_alloc (m_state (spec_trans rec_event ()))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (m_state rec_trans)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    iMod (mstate_var_alloc unit) as (γs) "?".
    iMod (mstate_var_split γs tt with "[$]") as "[Hγs ?]".
    pose (Hspec := SpecGS γs).

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".

    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (f fn vs h ?) "!>".
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".

    iApply (sim_gen_expr_intro _ tt with "[Hγs] [-]"); [simpl; done..|].
    unfold echo_spec, TReceive.
    rewrite bind_bind. iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind.
    iApply sim_gen_TVis. iIntros ([]) "Hγs". iIntros (??) "[-> [-> _]]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt with "[Hγs] [-]"); [simpl; done..|].
    rewrite bind_ret_l.
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs".
    iIntros (??) "[-> [-> _]]".

    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".

    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }

    iApply (sim_gen_expr_intro _ [] with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }
    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply (sim_echo_spec with "[] [] [] Hγσ_s [//]").
    1-3: by iApply (rec_fn_intro with "[$]").
    - iIntros "!>" (??) => /=. iDestruct 1 as (?) "[Hγσ_s HC]" => /=.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (->) "HC".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s".
      iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iSplit!. iIntros (??) "[-> HC]".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s".
      iApply "HC". iSplit!.
    - done.
  Qed.

End echo.

Lemma echo_refines_echo_spec :
  trefines (rec_mod echo_prog) (spec_mod echo_spec tt).
Proof.
  eapply (sim_adequacy #[dimsumΣ; recΣ]); [eapply _..|].
  iIntros (??) "!>". simpl.
  iMod recgs_alloc as (?) "[?[??]]".
  iApply echo_spec_sim. iFrame.
Qed.

(*
  [echo]_rec <= [echo_spec]_spec

  [echo]_rec + [getc]_rec <= ...

getc() = local l [1]; read(l, 1); return l[0]

  [echo]_rec + [putc]_spec <= ...

putc(c) = buffer += [c]; if * then write(buffer, len(buffer)); buffer = []

  ⌜[echo]_rec⌝_r<->a + [getc, putc]_asm <= ...

sales pitch:
  binary separation logic for multi-language
  interesting: reuse one spec for many different linking scenarios
  usuallu in separation logic you are proud that everything is modular,
   but then there is the assumption that it is implemented in the same language
   here you can actually swap out the specification for other programs
  higher-order encoding often uses explicitly that the code is in the same language e.g. with ∀ f, {P} f {Q}

switching:
  - no obvious that one can do at all
  - write some notes outside of Coq to explain what it means
    - with more intuition and less detail
  -
 *)



Definition getc_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [("l", 1)];
  fd_body := LetE "c" (rec.Call (Val (ValFn "read")) [Var "l"; Val 1]) $
             Load (Var "l");
  fd_static := I
|}.
Definition getc_prog : gmap string fndef :=
  <["getc" := getc_rec]> $ ∅.

Section getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_getc Π :
    "getc" ↪ Some getc_rec -∗
    rec_fn_spec_hoare Tgt Π "getc" ({{ es POST0, ⌜es = []⌝ ∗
      rec_fn_spec_hoare Tgt Π "read" ({{ es POST,
        ∃ l v, ⌜es = [Val $ ValLoc l; Val $ 1]⌝ ∗ l ↦ v ∗
      POST ({{ _,
        ∃ c, l ↦ (ValNum c) ∗ POST0 ({{ vr, ⌜vr = ValNum c⌝}})}})}})}}).
  Proof.
    iIntros "#?".
    iIntros (es Φ). iDestruct 1 as (->) "HΦ".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hl".
    destruct ls as [|? []] => //=. 2: iDestruct!. iModIntro.
    rewrite offset_loc_0. iDestruct "Hl" as "[[Hl _] _]".
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply "HΦ". iSplit!. iFrame. iIntros (?) "[% [Hl HΦ]]".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_tgt_rec_Load with "Hl"). iIntros "Hl !>" => /=. iSplit!.
    iFrame. by iApply "HΦ".
  Qed.

End getc.

Definition read_mem_rec : fndef := {|
  fd_args := ["l"; "c"];
  fd_static_vars := [("pos", 1)];
  fd_vars := [];
  fd_body :=
(*
global pos = 0;
read (l, c) {
  if (c <= 0) {
    return 0;
  } else {
    l <- pos;
    pos <- *pos + 1;
    ret = read(l + 1, c + (-1));
    return ret + 1;
  }
}
*)

    If (BinOp (Var "c") LeOp (Val 0))
      (Val 0)
      (LetE "_" (Store (Var "l") (Load (Var "pos"))) $
       LetE "_" (Store (Var "pos") (BinOp (Load (Var "pos")) AddOp (Val 1))) $
       LetE "ret" (rec.Call (Val (ValFn "read")) [
                       BinOp (Var "l") OffsetOp (Val 1);
                       BinOp (Var "c") AddOp (Val (-1))]) $
       (BinOp (Var "ret") AddOp (Val 1)));
  fd_static := I
|}.
Definition read_mem_prog : gmap string fndef :=
  <["read" := read_mem_rec]> $ ∅.

Section read_mem.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_read_mem Π (lpos : loc) :
    lpos = (ProvStatic "read" 0, 0) →
    "read" ↪ Some read_mem_rec -∗
    rec_fn_spec_hoare Tgt Π "read" ({{ es POST0, ∃ l vs (pos : Z),
      ⌜es = [Val (ValLoc l); Val (length vs)]⌝ ∗
      lpos ↦ pos ∗
      ([∗ map] l↦v∈array l vs, l ↦ v) ∗
      POST0 ({{ vret,
        ⌜vret = ValNum (length vs)⌝ ∗
        lpos ↦ (pos + length vs) ∗
        ([∗ map] l↦v∈array l (ValNum <$> seqZ pos (length vs)), l ↦ v)
      }})}}).
  Proof.
    iIntros (Hlpos) "#?".
    (* TODO: proof *)
  Abort.

End read_mem.

(* TODO: compose sim_getc and sim_read_mem *)


Definition __NR_READ : Z := 0.
Definition read_addr : Z := 500.
Definition read_asm : gmap Z asm_instr :=
  deep_to_asm_instrs read_addr [
      Amov "R8" __NR_READ;
      Asyscall;
      Aret
    ].

Section read.
  Context `{!dimsumGS Σ} `{!asmGS Σ}.

  Lemma sim_read Π :
    ↪ₐ∗ read_asm -∗
    asm_spec Tgt Π ({{ POST0,
      ∃ ret r0 r8, "PC" ↦ᵣ read_addr ∗ "R30" ↦ᵣ ret ∗ "R0" ↦ᵣ r0 ∗ "R8" ↦ᵣ r8 ∗
      switch Π ({{ κ σ POST,
        ∃ args mem, ⌜κ = Some (Outgoing, EASyscallCall args mem)⌝ ∗
        ⌜args !! 8%nat = Some __NR_READ⌝ ∗ ⌜args !! 0%nat = Some r0⌝ ∗
      POST Tgt _ asm_trans ({{ σ' Π',
        ⌜σ' = σ⌝ ∗
      switch Π' ({{ κ σ POST,
        ∃ r mem', ⌜κ = Some (Incoming, EASyscallRet r mem')⌝ ∗
      POST Tgt _ asm_trans ({{ σ' Π',
        ⌜σ' = σ⌝ ∗ ⌜Π' = Π⌝ ∗ ⌜mem' = mem⌝ ∗
    POST0 (∃ r8', "PC" ↦ᵣ ret ∗ "R30" ↦ᵣ ret ∗ "R0" ↦ᵣ r ∗ "R8" ↦ᵣ r8') }}) }}) }}) }}) }}).
  Proof.
    iIntros "#Hins" (?). iDestruct 1 as (???) "(HPC&HR30&HR0&HR8&Hret)".
    iApply (sim_Jump_internal with "HPC").
    { iApply (asm_instrs_big_lookup_deep 0 with "[$]"); [lia|simpl; done]. }
    iIntros "!> HPC" => /=.
    iApply sim_WriteReg. iSplit.
    { by iApply learn_regs_done. }
    iFrame. iIntros "!>" (_ _) "HR8".
    iApply sim_WriteReg. iSplit.
    { iApply (learn_regs_reg with "HPC").
      iApply learn_regs_done. }
    iFrame. iIntros "!>" (? [-> _]) "HPC".

    iApply (sim_Jump_internal with "HPC").
    { iApply (asm_instrs_big_lookup_deep 1 with "[$]"); [lia|simpl; done]. }
    iIntros "!> HPC" => /=.
    iApply sim_Syscall. iModIntro.
    iIntros (??). iDestruct 1 as (?? ->) "[? HC]". iApply "HC". iExists _. iSplit.
    { iApply (learn_regs_reg with "HR0").
      iApply (learn_regs_reg with "HR8").
      iApply learn_regs_done. }
    iIntros ([? [? _]]) "HC".
    iApply "Hret". iSplit!. iIntros (??) "[-> Hret]".
    iApply "HC". iSplit!. iFrame.
    iIntros (??). iDestruct 1 as (?? ->) "[HR0 HC]". iApply "Hret". iSplit!.
    iIntros (??) "[-> [-> [-> Hret]]]". iApply "HC". iSplit!. iFrame.
    iApply sim_WriteReg. iSplit.
    { iApply (learn_regs_reg with "HPC").
      iApply learn_regs_done. }
    iFrame. iIntros "!>" (? [-> _]) "HPC".

    iApply (sim_Jump_internal with "HPC").
    { iApply (asm_instrs_big_lookup_deep 2 with "[$]"); [lia|simpl; done]. }
    iIntros "!> HPC" => /=.
    iApply sim_WriteReg. iSplit.
    { iApply (learn_regs_reg with "HR30").
      iApply learn_regs_done. }
    iFrame. iIntros "!>" (? [-> _]) "HPC".
    iApply "Hret". iFrame.
  Qed.
End read.

Section getc_read.
  Context `{!dimsumGS Σ} `{!recGS Σ} `{!asmGS Σ}.

  Definition switch_r2a (mr : mod_trans rec_event) (ma : mod_trans asm_event) ts Πr K : iProp Σ :=
      switch Πr ({{ κr σr POST,
        (∃ f vs h, ⌜κr = Some (Outgoing, ERCall f vs h)⌝ ∗
        K f vs h ({{ a K2,
        (* replace this with f2i f a *) ⌜a = 1⌝ ∗
      POST ts _ ma ({{ σa Πa,
        K2 σa ({{ K3,

      switch Πa ({{ κa σa POST,
        ∃ regs mem, ⌜κa = Some (Incoming, EAJump regs mem)⌝ ∗
        K3 ({{ K4,
      POST ts _ ma ({{ σa Πa,
        K4 σa Πa ({{ K5,
      (* Permission to switch back *)
      switch Πa ({{ κa σa' POST,
        ∃ regs' mem', ⌜κa = Some (Outgoing, EAJump regs' mem')⌝ ∗
        ⌜regs' !!! "PC" = regs !!! "R30"⌝ ∗
        K5 ({{ K6,
      POST ts _ mr ({{ σr' Πr',
        ⌜Πr' = Πr⌝ ∗ K6 σr'
      }}) }}) }}) }}) }}) }}) }}) }}) }}) }}) )%I }}).

  Lemma sim_getc_read Π :
    "getc" ↪ Some getc_rec -∗
    "read" ↪ None -∗
    ↪ₐ∗ read_asm -∗
    rec_fn_spec_hoare Tgt Π "getc" ({{ es POST0, ⌜es = []⌝ ∗
      switch_r2a rec_trans asm_trans Tgt Π ({{ f vs h POST,
      POST read_addr ({{ σa ACCEPT,
        ⌜asm_cur_instr σa = AWaiting⌝ ∗

      ACCEPT ({{ POST,
      POST ({{ σa Πa RET,
      ⌜asm_cur_instr σa = ARunning []⌝ ∗
      (* TODO: the following should maybe come from switch_r2a? *)
        asm_state_interp σa ∗
      ∃ ret r0 r8, "PC" ↦ᵣ read_addr ∗ "R30" ↦ᵣ ret ∗ "R0" ↦ᵣ r0 ∗ "R8" ↦ᵣ r8 ∗

      (* TODO: define a switch syscall and use it here *)
      RET ({{ POST,
      POST ({{ σr', True
      }}) }}) }}) }}) }}) }}) }}).
  Proof.
    iIntros "#? #? #?".
    iIntros (es ?). iDestruct 1 as (->) "HC".
    iApply (sim_getc with "[//]") => /=. iSplit!.
    iIntros (es ?) => /=. iDestruct 1 as (?? ->) "[Hl HΦ]".
    iApply sim_tgt_rec_Call_external. { done. }
    iIntros (K h fns) "? ? ? !>".
    iIntros (??) => /=. iDestruct 1 as (??) "HR". simplify_eq.
    iApply "HC" => /=. iSplit!. { admit. }
    iIntros ([i regs0 mem0 instrs]?) "[% HC]"; simplify_eq/=.
    iApply sim_tgt_asm_Waiting.
    iIntros (????). iModIntro.
    iApply "HC" => /=. iSplit!. iIntros ([????] ?) "[% [? HC]]"; simplify_eq/=.
    iApply (sim_gen_expr_intro (Λ:=asm_mod_lang) with "[$]"). { done. }
    iApply sim_read; [done|] => /=.
    iDestruct "HC" as (???) "(?&?&?&?&HC)". iFrame.
  Admitted.

End getc_read.


Definition putc_buffer_prov : prov := ProvStatic "putc" 0.

Definition putc_spec : spec rec_event (list Z * gmap Z val) void :=
  Spec.forever (
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    c ← TAll _;
    TAssume (f = "putc");;
    TAssume (vs = [ValNum c]);;
    '(buffer, blk) ← TGet;
    TAssume (heap_preserved {[putc_buffer_prov := blk]} h);;
    blk' ← TExist _;
    (* TODO: use something like heap_update_block putc_buffer_prov blk' h *)
    let h := h in
    TPut (buffer ++ [c], blk');;
    b ← TExist bool;
    h' ← (if b then
       l ← TExist _;
       '(buffer, blk) ← TGet;
       TAssert (l.1 = putc_buffer_prov);;
       TAssert (array l (ValNum <$> (buffer :> list Z)) ⊆ h_heap h);;
       '(c, h') ← TCallRet "write" [ValLoc l; ValNum (length buffer)] h;
       TAssume (h_block h' putc_buffer_prov = blk);;
       blk' ← TExist _;
       (* TODO: use something like heap_update_block putc_buffer_prov blk' h *)
       let h := h in
       TPut ([], blk');;
       TRet h
     else TRet h
    );
    TVis (Outgoing, ERReturn 0 h')).

(* TODO: Can one implement a spec like this without copying the buffer
to a fresh allocation when it is passed to write? E.g. by making the
rec_to_rec wrapper more generic? *)
Definition putc_spec_alt : spec rec_event (list Z) void :=
  Spec.forever (
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    c ← TAll _;
    TAssume (f = "putc");;
    TAssume (vs = [ValNum c]);;
    buffer ← TGet;
    TPut (buffer ++ [c]);;
    b ← TExist bool;
    h' ← (if b then
       l ← TExist _;
       buffer ← TGet;
       (* TODO: add array l (ValNum <$> (buffer :> list Z)) to h *)
       let h := h in
       '(c, h) ← TCallRet "write" [ValLoc l; ValNum (length buffer)] h;
       (* TODO: Assume that everything except something is unchanged?
       Or not and rely on wrapper? *)
       (* TODO: Remove l from the heap? *)
       TPut [];;
       TRet h
     else TRet h
    );
    TVis (Outgoing, ERReturn 0 h')).
