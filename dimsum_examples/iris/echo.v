From iris.bi.lib Require Import fixpoint.
From iris.proofmode Require Import proofmode.

(* NOTE - BI the logic of "bunched implications" *)
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
  Proof. rewrite /bi_loop.
         apply: greatest_fixpoint_unfold.
  Qed.

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
(* NOTE
   Unfold function if it is applied to at least the arguments before "/". In this case all.
   Unfold function if arguments marked with "!" unfold to constructor *)
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


Definition retOne_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := Val 1;
  fd_static := I
|}.
Definition retOne_prog : gmap string fndef :=
  <["retOne" := retOne_rec]> $ ∅.

Definition retOne_spec : spec rec_event unit void :=
  Spec.forever(
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "retOne");;
  TAssume (vs = []);;
  TVis (Outgoing, ERReturn (ValNum 1) h)).

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma retOne_refines_retOne_spec_direct :
  trefines (rec_mod retOne_prog) (spec_mod retOne_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(Rec e _ f) (*σi*) '(t, _),
    t ≡ retOne_spec ∧
    e = Waiting false ∧
    f = retOne_prog). }
  { split!. } { done. }
  move => n _ Hloop [???] [??] [??] /=. destruct!/=.
  (* Step in implementation to introduce arguments *)
  tstep_i.
  split!. move => ???? H.
  tstep_s. rewrite -/retOne_spec. go.
  tstep_s. eexists (_, _, _). go.
  (* Unify evars *)
  tstep_s. split!. go.
  (* Here deal with assumptions *)
  tstep_s => ?. go.
  tstep_s => ?. go. destruct!.
  (* Now, step through implementation *)
  tstep_i. split!.
  move => ??. destruct!.
  rewrite /retOne_prog in H. simplify_map_eq. split!.
  (* Stack Frame *)
  tstep_i => ?? [-> ->]. split!.
  tstep_i. eexists. split!.
  tstep_i.
  tstep_s. split!. go.
  by apply Hloop.
Qed.

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
  (* TODO: Parse this syntactically:
    Π: What does it do?
   *)
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
    iIntros "#?". iApply rec_fn_spec_hoare_ctx.
    (* NOTE What's up with the ordinal later stuff - recursion *)
    iIntros "#?".
    set BODY := (X in bi_loop X).
    iApply ord_loeb. (*; [done|]*)
    { iAssumption. }
    iIntros "!> #IH".
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
  (* Handle the initial call from the environment *)
  tstep_i.
  split! => ???? H.
  tstep_s. eexists (_, _, _). go.
  tstep_s. split!. go.
  tstep_s => ?. go.
  tstep_s => ?. go. destruct!.
  (* Now prove the body by induction *)
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(Rec e _ f) '(t, _),
    (* TODO: How does Michael think about this, I guess typically I would phrase an induction hypothesis
      using an arbitrary kontext here *)
    exists K,
    t ≡ Spec.forever echo_spec_body ∧
    e = expr_fill K ((Call (Val (ValFn "echo"))) (Val <$> [])) ∧
    f = echo_prog). }
  { eexists [ReturnExtCtx false]. split!. } { done. }
  move => n _ Hloop [???] [??] [ctx[?[??]]] /=. destruct!/=.
  go_s.
  tstep_s. eexists. go.         (* NOTE: Introducing Heap *)
  tstep_i. split!.
  move => ??. destruct!/=.
  rewrite /echo_prog in H. simplify_map_eq. split!.
  (* NOTE: Start of getc *)
  tstep_i => ?? [??]. simplify_eq. split!.
  tstep_i. split!. move => ?.              (* NOTE - split between internal and external call *)
  (* NOTE: Here we now have `Waiting true` *)
  tstep_s. split!. go.
  tstep_i.
  split.
  { (* NOTE: Here I now am getting a call back from the external call, i.e., because of TCallRet immediate UB *)
    move => ?????.
    tstep_s. eexists. go.
    tstep_s. split!. go.
    by tstep_s. }
  move => ???.
  tstep_s. eexists. go.
  tstep_s. split!. go.
  tstep_s => ?. go.
  (* NOTE: Start of putc *)
  tstep_s. eexists. go.
  tstep_i. tstep_i. split!. move => ?.
  tstep_s. split!. go.
  tstep_i. split!.
  { (* NOTE: Here I now am getting a call back from the external call, i.e., because of TCallRet immediate UB *)
    move => ?????.
    tstep_s. eexists. go.
    tstep_s. split!. go.
    by tstep_s. }
  move => ???.
  tstep_s. eexists. go.
  tstep_s. split!. go.
  tstep_s => ?.
  rewrite bind_ret_l.
  go. simplify_eq.
  tstep_i.
  eapply Hloop. { done. }
  eexists ([FreeACtx []] ++ ctx).
  split!.
Qed.

Section echo.
  Context `{!dimsumGS Σ} `{!recGS Σ}.
  (* TODO: What's going on here? *)
  Lemma sim_echo_spec Π γσ_s (σ : m_state (spec_trans _ unit)) :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γσ_s ⤳ σ -∗
    ⌜σ.1 ≡ Spec.forever echo_spec_body⌝ -∗
    □ switch_external Π ({{ _ σ POST,
        ∃ σ_s, γσ_s ⤳ σ_s ∗
      POST (spec_trans _ unit) σ_s ({{ _ Π',
      switch Π' ({{ κ σ_s' POST,
       ⌜κ = None⌝ ∗
      POST Tgt _ _ ({{ σ' Π', ⌜σ' = σ⌝ ∗ ⌜Π' = Π⌝ ∗ γσ_s ⤳ σ_s'}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "echo" ({{ es _, ⌜es = []⌝}}).
  Proof.
    iIntros "#?#?#? Hγσ_s Hσ_s #Hswitch". iApply rec_fn_spec_hoare_ctx. iIntros "#?".
    iIntros (es Φ). iDestruct 1 as %->. iApply sim_echo; [done|]. iSplit!.
    set BODY := (X in bi_loop X).
    set EXT := (X in switch_external Π X).
    iRevert (σ) "Hγσ_s Hσ_s". iApply ord_loeb; [done|]. iIntros "!> #IH".
    iIntros (σ) "Hγσ_s %". iApply bi_loop_step. iIntros (?) "#HLOOP".
    iIntros (es ?). iDestruct 1 as (->) "HΦ".

    iMod (mstate_var_alloc unit) as (γ) "?".
    iMod (mstate_var_split γ σ.2 with "[$]") as "[Hγ ?]".
    pose (Hspec := SpecGS γ).

    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hswitch". iFrame. iSplit!.
    iIntros (??). iDestruct 1 as (->) "Hs".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite ->unfold_forever. rewrite {2}/echo_spec_body.
    rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    rewrite bind_bind.
    (* TODO: don't unfold TCallRet *)
    rewrite /TCallRet bind_bind.
    iApply sim_gen_TVis. iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> Hs]".
    iApply (sim_gen_stop with "[-]"). iApply "Hs". iSplit!.
    iIntros (??) "[-> [-> ?]]".
    iApply (sim_tgt_rec_Waiting_raw with "[-]"). iSplit.
    { iIntros. iModIntro. iApply "Hswitch". iFrame. iSplit!.
      iIntros (??) "[-> Hs]".
      iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
      rewrite bind_bind. iApply (sim_src_TExist with "[-]").
      rewrite bind_bind. iApply sim_gen_TVis.
      iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
      iApply "Hs". iSplit!. iIntros (??) "[-> _]".
      iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
      iApply sim_src_TUb. }
    iIntros. iModIntro. iApply "Hswitch". iFrame. iSplit!.
    iIntros (??) "[-> Hs]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    rewrite bind_bind. iApply sim_gen_TVis.
    iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> Hs]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_ret_l bind_bind. iApply (sim_src_TAssume with "[-]").
    iIntros (<-). iApply sim_gen_expr_None => /=.
    iIntros (? [] ?) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> [-> ?]]".
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ".

    iIntros (es ?). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns'' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hswitch". iFrame. iSplit!.
    iIntros (??). iDestruct 1 as (->) "Hs".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    rewrite bind_bind.
    (* TODO: don't unfold TCallRet *)
    setoid_rewrite bind_bind.
    iApply sim_gen_TVis. iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> Hs]".
    iApply (sim_gen_stop with "[-]"). iApply "Hs". iSplit!.
    iIntros (??) "[-> [-> ?]]".
    iApply (sim_tgt_rec_Waiting_raw with "[-]"). iSplit.
    { iIntros. iModIntro. iApply "Hswitch". iFrame. iSplit!.
      iIntros (??) "[-> Hs]".
      iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
      setoid_rewrite bind_bind. iApply (sim_src_TExist with "[-]").
      setoid_rewrite bind_bind. iApply sim_gen_TVis.
      iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
      iApply "Hs". iSplit!. iIntros (??) "[-> _]".
      iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
      iApply sim_src_TUb. }
    iIntros. iModIntro. iApply "Hswitch". iFrame. iSplit!.
    iIntros (??) "[-> Hs]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    setoid_rewrite bind_bind. iApply (sim_src_TExist with "[-]").
    setoid_rewrite bind_bind. iApply sim_gen_TVis.
    iIntros ([]) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> Hs]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_ret_l bind_bind. iApply (sim_src_TAssume with "[-]").
    iIntros (<-). rewrite bind_ret_l. iApply sim_gen_expr_None => /=.
    iIntros (? [] ?) "Hγ". iIntros (??) "[-> [-> _]]".
    iApply "Hs". iSplit!. iIntros (??) "[-> [-> ?]]".
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ". iApply "HLOOP".
    iApply ("IH" with "[$] [//]").
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
    - iIntros "!>" (??). iDestruct 1 as (?) "[Hγσ_s HC]" => /=.
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
  (* TODO: Does it make sense to think about it this way
    { args = [] * ({ ∃ l v, ⌜es = [Val $ ValLoc l; Val $ 1]⌝ ∗ l ↦ v } read { ∃ c, l ↦ c}) } getc { ~res~ = c } *)

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

(* Does returning the length make any sense? (In DimSum) *)
(* Read the sequence 0...c into l and return the length? *)
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
      (* NOTE: There is no sequencing *)
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
    (* Given a static/global variable *)
    lpos = (ProvStatic "read" 0, 0) →
    (* "read" points to the function (internal) *)
    "read" ↪ Some read_mem_rec -∗
    rec_fn_spec_hoare Tgt Π "read" ({{ es POST0, ∃ l vs (pos : Z),
      (* Arguments are a location and length of a list *)
      ⌜es = [Val (ValLoc l); Val (length vs)]⌝ ∗
      (* We own the global pointer *)
      lpos ↦ pos ∗
      (* We own the array [vs[0], vs[1], ... , vs[vs.length - 1]] *)
      ([∗ map] l↦v∈array l vs, l ↦ v) ∗
      POST0 ({{ vret,
        (* We return the length of the list *)
        ⌜vret = ValNum (length vs)⌝ ∗
        (* The global pointer has been increased by length of the list *)
        lpos ↦ (pos + length vs) ∗
        (* We own the array [pos + 0, pos +1, ..., pos + (vs.length - 1)] *)
        ([∗ map] l↦v∈array l (ValNum <$> seqZ pos (length vs)), l ↦ v)
      }})}}).
  Proof.
    iIntros "%Hlpos #?". iApply rec_fn_spec_hoare_ctx. iIntros "#?".
    iApply ord_loeb. { iAssumption. } iModIntro.
    iIntros "#IH %es %Φ HΦ/=".
    iDestruct "HΦ" as (? ? count) "[? [Hlpos [Hl H]]]".
    (* Base Case *)
    iDestruct!.
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    (* FIXME: Maybe I can use this to try fiddling with auto indentation *)
    iModIntro.
    iApply sim_tgt_rec_AllocA; [done|]. iIntros (lcl) "Hlcl /=".
    iModIntro.
    (* NOTE: Bind the BinOp *)
    iApply (sim_gen_expr_bind _ [IfCtx _ _]).
    iApply sim_tgt_rec_BinOp. { reflexivity. } iModIntro.
    iApply sim_tgt_rec_If. iModIntro.
    (* Split into base and recursive case *)
    destruct vs; simpl.
    - iApply sim_gen_expr_stop.
      iExists 0.
      iSplit; [done|].
      iSplitL "Hlcl".
      { by destruct lcl. }
      iApply "H". rewrite Z.add_0_r.
      iSplit!.
    - (* STORE 1 *)
      iApply (sim_gen_expr_bind _ [LetECtx _ _]).
      iApply (sim_gen_expr_bind _ [StoreRCtx _]).
      iApply (sim_tgt_rec_Load with "Hlpos"). iIntros "Hlpos". iModIntro => /=.
      (* NOTE: I need to unroll the separating conjunction and pass ownership of the first location *)
      (* FIXME Why can't I use iRewrite *)
      (* rewrite array_cons. iRewrite big_sepM_insert  in "Hl". *)
      rewrite array_cons big_sepM_insert. 2 : { rewrite array_lookup_None. naive_solver lia. }
      iDestruct "Hl" as "[Hl Hl']".
      iApply (sim_tgt_rec_Store with "Hl"). iIntros. iModIntro.
      iApply sim_tgt_rec_LetE. iModIntro. simpl.
      (* STORE 2 *)
      iApply (sim_gen_expr_bind _ [LetECtx _ _]).
      iApply (sim_gen_expr_bind _ [StoreRCtx _]).
      iApply (sim_gen_expr_bind _ [BinOpLCtx _ _]).
      iApply (sim_tgt_rec_Load with "Hlpos"). iIntros "Hlpos !> /=".
      iApply sim_tgt_rec_BinOp. { reflexivity. } iModIntro.
      iApply (sim_tgt_rec_Store with "Hlpos"). iIntros "Hlpos !>".
      iApply sim_tgt_rec_LetE. iModIntro. simpl.
      (* Call + RETURN *)
      iApply (sim_gen_expr_bind _ [LetECtx _ _]).
      (* Handle arguments *)
      iApply (sim_gen_expr_bind _ [CallCtx _ [] _]) => /=.
      iApply sim_tgt_rec_BinOp. { reflexivity. } iModIntro.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_] _]).
      iApply sim_tgt_rec_BinOp => /=.
      (* FIXME: Why is this so hard :/ *)
      { instantiate (1 := length vs). f_equal. rewrite Nat2Z.inj_succ.
        change (_ + -1) with (Z.pred (Z.succ (length vs))). rewrite Z.pred_succ. reflexivity. } iModIntro.
      (* Induction *)
      iApply "IH". simpl.
      (* TODO: That's a little awkward *)
      do 3 iExists (_).
      iSplit. { done. }
      iSplitL "Hlpos". iAssumption.
      iSplitL "Hl'". iAssumption.
      iIntros (v') "[-> [Hlpos ?]]".
      iApply sim_tgt_rec_LetE => /=. iModIntro.
      iApply (sim_tgt_rec_BinOp). { reflexivity. } iModIntro.
      iExists (_).
      iSplit. done.
      iSplitL "Hlcl". {by destruct lcl. }
      iApply "H".
      rewrite! Nat2Z.inj_succ.
      iSplit. { done. }
      iSplitL "Hlpos". { rewrite <-Z.add_assoc, Z.add_1_l. iApply "Hlpos". }
      (* TODO: Rewrite at doesn't work *)
      (* rewrite seqZ_cons at 2. *)
      rewrite (seqZ_cons _ (Z.succ _)) => /=. 2 : { lia. }
      rewrite array_cons.
      (* FIXME: Why does iRewrite not work? *)
      rewrite big_sepM_insert Z.pred_succ -Z.add_1_r. 2: { rewrite array_lookup_None. naive_solver lia. }
      iFrame.
  Qed.

End read_mem.

Definition combined_prog : gmap string fndef :=
  <["read" := read_mem_rec]> $ <["getc" := getc_rec]> $ ∅.

Section combined.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_combined Π (lpos : loc) :
    (* Given a static/global variable which holds the buffer (index into) *)
    lpos = (ProvStatic "read" 0, 0) →
    (* "read" points to the function we defined (internal) *)
    "read" ↪ Some read_mem_rec -∗
    "getc" ↪ Some getc_rec -∗
    rec_fn_spec_hoare Tgt Π "getc" ({{ es POST, ∃ (pos : Z),
      ⌜es = []⌝ ∗
      lpos ↦ pos ∗
      POST ({{ vr, ⌜vr = ValNum pos⌝ ∗ lpos ↦ (pos + 1)}})}}).
  Proof.
   iIntros "%Hlpos #Hread #Hgetc %args %Φ Hpre".
   iApply sim_getc => /=; [done|].
   iDestruct "Hpre" as "[%count [?[? HΦ]]]". iFrame.
   rewrite /rec_fn_spec_hoare /rec_fn_spec.
   iIntros "%args' %Φ' [%l [%v [Hargs' [Hl HΦ']]]]".
   iApply sim_read_mem => /=. 1-2: done.
   do 3 iExists (_). iFrame.
   iSplitL "Hargs'". { instantiate (1 := [v]). iExact "Hargs'". }
   iSplitL "Hl".
   { rewrite /array => /=.
     rewrite insert_empty kmap_singleton offset_loc_0 big_sepM_singleton. iAssumption. }
   iIntros (v') "[? [? Hl]]" => /=.
   iApply "HΦ'". iExists (_).
   iSplitL "Hl".
   { rewrite Z.add_0_l /array  => /=.
     rewrite insert_empty kmap_singleton offset_loc_0 big_sepM_singleton. iAssumption. }
   iIntros (v'') "?".
   iApply "HΦ". iFrame.
Qed.
End combined.

Section sim_spec.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  (* TODO 0a: Write a Spec for a program that increases a location *)

  Definition retOneMore_rec : fndef := {|
    fd_args := [];
    fd_static_vars := [("pos", 1)];
    fd_vars := [];
    fd_body := (LetE "ret" (Load (Var "pos")) $
                LetE "_" (Store (Var "pos") (BinOp (Var "ret") AddOp (Val 1))) $
                Var ("ret"));
    fd_static := I
  |}.

  Definition retOneMore_prog : gmap string fndef :=
    <["retOneMore" := retOneMore_rec]> $ ∅.

  Definition retOneMore_spec : spec rec_event unit void :=
    Spec.forever(
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "retOneMore");;
    TAssume (vs = []);;
    (* NOTE: Here I now want to express that my program returns the value stored at pos *)
    (* TODO: Is this too weak? *)
    v ← TAll Z;
    TAssume ((h_heap h) !! ((ProvStatic "retOneMore" 0), 0) = Some (ValNum v));;
    TVis (Outgoing, ERReturn (ValNum v) (heap_update h ((ProvStatic "retOneMore" 0), 0) (ValNum (v + 1))))).

  (* TODO 0b: Prove that this spec is satisfied *)

  Lemma retOne_refines_retOneMore_spec_direct :
    trefines (rec_mod retOneMore_prog) (spec_mod retOneMore_spec tt).
  Proof.
    apply: tsim_implies_trefines => n0 /=.
    unshelve eapply tsim_remember. { simpl. exact (λ _ '(Rec e _ f) '(t, _),
      t ≡ retOneMore_spec ∧
      e = Waiting false ∧
      f = retOneMore_prog). }
    { split!. } { done. }
    move => n _ Hloop [???] [??] [??] /=. destruct!/=.
    (* Step in implementation to introduce arguments *)
    tstep_i.
    split!. move => ? f ?? H.
    tstep_s. rewrite -/retOneMore_spec. go.
    tstep_s. eexists (_, _, _). go.
    (* Unify evars *)
    tstep_s. split!. go.
    (* Here deal with assumptions *)
    tstep_s => ?. go.
    tstep_s => ?. go. destruct!.
    tstep_s => ?. go.
    tstep_s => ?. go.
    (* Now, step through implementation *)
    tstep_i. split!.
    move => ??. destruct!.
    rewrite /retOneMore_prog in H. simplify_map_eq. split!.
    (* Stack Frame *)
    tstep_i => ?? [-> ?]. simplify_eq. split!.
    tstep_i. eexists. split!. { done. }
    tstep_i. tstep_i. tstep_i. split. { by rewrite /heap_alive. }
    tstep_i. tstep_i. eexists. split!.
    tstep_i. tstep_s. split!. go.
    by apply Hloop.
  Qed.

  (* TODO 1: Write a Spec Program for getc returning increasing numbers *)
  (* This Spec is quite specific, in order to reflect the combined program *)
  Definition getc_spec_heap : spec rec_event unit void :=
    Spec.forever(
    (* Incoming call of getc *)
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    (* There is a current position of the buffer *)
    v ← TAll Z;
    TAssume ((h_heap h) !! ((ProvStatic "read" 0), 0) = Some (ValNum v));;
    (* Return old position, update the location to old position, and the position is updated *)
    TVis (Outgoing, ERReturn (ValNum v) (heap_update h ((ProvStatic "read" 0), 0) (ValNum (v + 1))))).

  (* TODO 2: Prove a separation logic tuple for it - analogous to sim_locle_spec2 (in ./memmove) *)

  Lemma sim_getc_spec_heap_pure `{!specGS} Π Φ :
    (* Someone is switching to me *)
    switch Π ({{ κ σ POST,
      (* REVIEW: Here, think about do I have to prove this or do I get it *)
      ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
      (* Here, a bit of intuition is missing for why it goes into the POST *)
    POST Tgt _ (spec_trans _ unit) ({{ σ' Π',
      (* REVIEW: Here, think about do I have to prove this or do I get it *)
      ∃ v, ⌜σ' = σ⌝ ∗ ⌜f = "getc"⌝ ∗ ⌜vs = []⌝ ∗
           (* REVIEW: Put a points-to here instead? *)
           ⌜(h_heap h) !! ((ProvStatic "read" 0), 0) = Some (ValNum v)⌝ ∗
      (* Switch back *)
    switch Π' ({{ κ σ POST,
      (* This is optional event, REVIEW: is this related to Π *)
      ⌜κ = (Some (Outgoing, ERReturn (ValNum v) (heap_update h ((ProvStatic "read" 0), 0) (ValNum (v + 1)))))⌝ ∗
      (* So what does this mean? *)
      ⌜σ = (getc_spec_heap, tt)⌝ ∗
      (* Looks like ghost things *)
      spec_state ()
      }})}})}}) -∗
    (* REVIEW: This is an arbitrary Φ, because danger? *)
    TGT getc_spec_heap @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC".
    unfold getc_spec_heap at 2. rewrite unfold_forever -/getc_spec_heap.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    (* Introducing arbitrary state *)
    iIntros ([]) "Hs !>".
    iIntros (??) "[% [% _]]". subst.
    iApply "HC". iSplit!. iIntros (??).
    iDestruct 1 as (?????) "HC". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>".
    iIntros (??) "[% [% _]]". subst. iApply "HC". iSplit!.
  Qed.

  (* TODO 3 *)
  Definition getc_fn_spec_strong (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    let lpos := (ProvStatic "read" 0, 0) in
    ∃ (pos: Z), ⌜es = []⌝ ∗ lpos ↦ pos ∗
    POST (λ v, ⌜v = ValNum pos⌝ ∗ lpos ↦ (pos + 1)).

  Definition getc_fn_spec_weak (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    let lpos := (ProvStatic "read" 0, 0) in
    ∃ (pos: Z), ⌜es = []⌝ ∗ lpos ↦ pos ∗
    POST (λ v, ⌜v = ValNum pos⌝).

  Lemma sim_getc_heap_pure fns Π :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    switch_link Tgt Π ({{ σ0 POST,
      ∃ vs h',
    POST (ERCall "getc" vs h') (spec_trans _ _) (getc_spec_heap, tt) ({{ _ Πr,
    switch_link Tgt Πr ({{ σ POST,
      ∃ v h'', ⌜σ = (getc_spec_heap, tt)⌝ ∗
    POST (ERReturn v h'') _ σ0 ({{ _ Πx,
      ⌜Πx = Π⌝}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_strong.
  Proof.
    iIntros "#Hfns #Hf HΠ" (es Φ) "HΦ". iDestruct "HΦ" as (pos ->) "[Hlpos HΦ]".
    iApply (sim_tgt_rec_Call_external with "[$]").
    (* We relate the points to predicates to the heap *)
    iIntros (???) "#?Htoa Haa !>".
    iIntros (??) "[% [% Hσ]]". subst. iApply "HΠ" => /=. iSplit!. iIntros (??) "[-> HΠi]".

    (* Am I here splitting the heap? *)
    iMod (mstate_var_alloc unit) as (γ) "?".
    iMod (mstate_var_split γ tt with "[$]") as "[Hγ _]".
    pose (Hspec := SpecGS γ).

    iApply (sim_gen_expr_intro _ tt with "[Hγ]"); simpl; [done..|].
    iApply sim_getc_spec_heap_pure => /=. iIntros (??). iDestruct 1 as (????) "HC". subst.
    iApply "HΠi". iSplit!. iIntros (??) "[% [% HΠr]]". simplify_eq/=.
    iApply "HC".
    iExists (_).
    (* iDestruct (rec_mapsto_lookup with "Htoa Hlpos") as "%H". *)
    (* FIXME REVIEW: Why does iSplit! not duplicate the context *)
    iDestruct (rec_mapsto_lookup with "Htoa Hlpos") as "%".
    iSplit!; [done|].
    iIntros (??). iDestruct 1 as (??) "HC".
    iApply "HΠr". iSplit!. iIntros (??) "[% HΠf]". simplify_eq.
    (* TODO REVIEW: What Exactly needs to hold for this to work? *)
    iPoseProof ((rec_mapsto_update _ _ _ (pos + 1)) with "Htoa Hlpos") as ">[Htoa Hlpos]".
    (* Not exactly sure what this is *)
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HΠf". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
    iIntros (???) "!>". iApply "HΠf". iSplit!. iIntros (??[?[??]]). simplify_eq.
    iApply "Hσ". iSplit!.
    iSplitL "Htoa". { done. }
    iSplitR "Hlpos HΦ" => /=. { by rewrite dom_alter_L. }
    iApply "HΦ". iSplit!.
Qed.

(* MEETING *)
(* TODO 4: Now do it with private state *)

  Definition getc_spec_priv : spec rec_event Z void :=
    Spec.forever(
    (* Incoming call of getc *)
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    (* There is a current position of the buffer *)
    v ← TGet;
    TPut (v + 1);;
    (* Return old position *)
    TVis (Outgoing, ERReturn (ValNum v) h)).

  (* TODO: Prove a separation logic tuple for it - analogous to sim_locle_spec2 (in ./memmove) *)

  Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
    γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
    inv H0. by dimsum.core.axioms.simplify_K.
  Qed.

  Lemma sim_getc_spec_heap_priv `{!specGS} Π Φ :
    switch Π ({{ κ σ POST,
      ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
      POST Tgt _ (spec_trans _ Z) ({{ σ' Π',
        ∃ v, ⌜σ' = σ⌝ ∗ ⌜f = "getc"⌝ ∗ ⌜vs = []⌝ ∗ (spec_state v) ∗
      switch Π' ({{ κ σ POST,
      ⌜κ = (Some (Outgoing, ERReturn (ValNum v) h))⌝ ∗
      ⌜σ = (getc_spec_priv, (v + 1)%Z)⌝ ∗
      spec_state (v + 1) ∗ spec_state (v + 1)
      }})}})}}) -∗
    (* REVIEW: This is an arbitrary Φ, because danger? *)
    TGT getc_spec_priv @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC".
    unfold getc_spec_priv at 2. rewrite unfold_forever -/getc_spec_priv.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v) "Hs !>". simpl.
    iIntros (??) "[% [% _]]". subst.
    iApply "HC". iSplit!. iIntros (??).
    iDestruct 1 as (????) "[Hs' HC]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_gen_TGet with "[-]").
    iSplit. { done. }
    iIntros "!>".
    rewrite bind_bind. iApply (sim_gen_TPut with "[Hs']"). { done. }
    iIntros "Hs". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v') "Hs'".
    iDestruct (mstate_var_agree with "Hs Hs'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% H2]]".
    subst. iApply "HC".
    iSplit!. iFrame.
  Qed.

  (* TODO 3 *)
  Definition getc_fn_spec_priv `{!specGS} (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, ⌜es = []⌝ ∗ spec_state v ∗
    POST (λ v', (⌜v' = ValNum v⌝) ∗ spec_state (v + 1))%I.

  Lemma sim_getc_heap_priv `{!specGS} fns Π :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    switch_link Tgt Π ({{ σ0 POST,
      ∃ vs h' v,
    POST (ERCall "getc" vs h') (spec_trans _ Z) (getc_spec_priv, v) ({{ _ Πr,
    switch_link Tgt Πr ({{ σ POST,
      ∃ h'' v', ⌜σ = (getc_spec_priv, v')⌝ ∗
    POST (ERReturn v' h'') _ σ0 ({{ _ Πx,
      ⌜Πx = Π⌝}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_priv.
  Proof.
    iIntros "#Hfns #Hf HΠ" (es Φ) "HΦ". iDestruct "HΦ" as (v ->) "[Hs HΦ]".

    (* FIXME REVIEW *)
    iMod (mstate_var_alloc Z) as (γ) "?".
    iMod (mstate_var_split γ v with "[$]") as "[Hγ1 Hγ2]".
    pose (Hspec := SpecGS γ).

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#?Htoa Haa !>".
    iIntros (??) "[% [% Hσ]]". subst.
    iApply "HΠ" => /=. iSplit!. iIntros (??) "[-> HΠi]".

    (* FIXME REVIEW: Introduce a "name" to refer to this particular state *)
    (* Or here *)

    iApply (sim_gen_expr_intro _ tt with "[Hγ1]"); simpl; [done..|].
    iApply sim_getc_spec_heap_priv_weak' => /=. iIntros (??). iDestruct 1 as (????) "HC". subst.
    iApply "HΠi". iSplit!. iIntros (??) "[% [% HΠr]]". simplify_eq/=.
    iApply "HC".
    iExists (_).
    do 3 (iSplit; [done|]).
    iSplitL "Hγ2". { done. }
    iIntros (??). iDestruct 1 as (?) "%HC".
    iApply "HΠr". iSplit!. iIntros (??) "[% HΠf]". simplify_eq.
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HΠf". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
    iIntros (???) "!>". iApply "HΠf". iSplit!. iIntros (??[?[??]]). simplify_eq.
    iApply "Hσ". iSplit!.
    iFrame.
    by iApply "HΦ".
  Qed.

End sim_spec.

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
