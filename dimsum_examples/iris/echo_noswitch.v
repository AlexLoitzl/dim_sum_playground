From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint.
From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO: upstream? *)
Arguments subst_static _ !_ /.

Definition echo_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := LetE "c" (rec.Call (Val (ValFn "getc")) []) $
             LetE "_" (rec.Call (Val (ValFn "putc")) [Var "c"]) $
             Val (ValNum 0);
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

(* ********************************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* ********************************************************************************************** *)
Section sim_spec.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition getc_spec: spec rec_event Z void :=
    (* Spec.forever( *)
    (* Incoming call of getc *)
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    (* There is a current position of the buffer *)
    v ← TGet;
    TPut (v + 1);;
    (* Return old position *)
    TVis (Outgoing, ERReturn (ValNum v) h);;
    TUb.

  Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
    γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
    inv H0. by dimsum.core.axioms.simplify_K.
  Qed.

  (* Lemma sim_getc_spec_heap_priv `{!specGS} Π Φ : *)
  (*   switch Π ({{ κ σ POST, *)
  (*     ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗ *)
  (*     POST Tgt _ (spec_trans _ Z) ({{ σ' Π', *)
  (*       ∃ v, ⌜σ' = σ⌝ ∗ ⌜f = "getc"⌝ ∗ ⌜vs = []⌝ ∗ (spec_state v) ∗ *)
  (*     switch Π' ({{ κ σ POST, *)
  (*     ⌜κ = (Some (Outgoing, ERReturn (ValNum v) h))⌝ ∗ *)
  (*     spec_state (v + 1) ∗ ⌜σ = (getc_spec_priv, (v + 1)%Z)⌝ *)
  (*     (* POST Tgt _ (spec_trans _ Z) ({{σ'' Π'', *) *)
  (*     (*   ⌜Π'' = Π⌝ ∗ *) *)
  (*     (*   ⌜σ'' = σ⌝ *) *)
  (*     (*   }}) *) *)
  (*     }})}})}}) -∗ *)
  (*   TGT getc_spec_priv @ Π {{ Φ }}. *)
  (* Proof. *)
  (*   iDestruct 1 as "HC". rewrite {2}/getc_spec_priv unfold_forever -/getc_spec_priv. *)
  (*   rewrite /TReceive bind_bind bind_bind. *)
  (*   iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>". *)
  (*   rewrite bind_bind. setoid_rewrite bind_ret_l. *)
  (*   iApply (sim_gen_TVis with "[-]"). *)
  (*   iIntros (v) "Hs !>". simpl. *)
  (*   iIntros (??) "[% [% HΠ]]". simpl. *)
  (*   subst. *)
  (*   iApply "HC". simpl. iSplit!. iIntros (??). *)
  (*   iDestruct 1 as (????) "[Hs' HC]". subst. *)
  (*   iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|]. *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_gen_TGet with "[-]"). *)
  (*   iSplit. 1: done. *)
  (*   iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_gen_TPut with "[Hs']"). 1: done. *)
  (*   iIntros "Hs". iIntros "!>". *)
  (*   iApply (sim_gen_TVis with "[-]"). iIntros (v') "Hs'". *)
  (*   iDestruct (mstate_var_agree with "Hs Hs'") as "<-". *)
  (*   iIntros "!> /=". *)
  (*   iIntros (??) "[% [% HΠ']]" => /=. simplify_eq. *)
  (*   iApply "HC". simpl. *)
  (*   iSplit!. *)
  (* Qed. *)

  (* Definition switch_link' `{!dimsumGS Σ} {S EV} (ts : tgt_src) (Π : option (io_event EV) → S → iProp Σ) *)
  (*   (m : mod_trans (io_event EV)) (Π' : option (io_event EV) → m_state m → iProp Σ) (K : _) : iProp Σ := *)
  (*   switch Π ({{ κ σ0 POST, *)
  (*     K σ0 ({{ e σ2 K2, ⌜κ = Some (Outgoing, e)⌝ ∗ *)
  (*   POST ts _ m ({{ σi Πi, *)
  (*     ⌜σi = σ2⌝ ∗ ⌜Πi = Π'⌝ ∗ *)
  (*   switch Πi ({{ κ' σ POST, *)
  (*     ∃ e', ⌜κ' = Some (Incoming, e')⌝ ∗ *)
  (*   POST ts _ m ({{ σr Πr, *)
  (*     ⌜σr = σ⌝ ∗ ⌜e' = e⌝ ∗ K2 σ Πr}})}})}})}})}})%I. *)

  (* Definition getc_fn_spec_priv (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ := *)
  (*   ∃ v, ⌜es = []⌝ ∗ P v ∗ *)
  (*   POST (λ v', (⌜v' = ValNum v⌝) ∗ P (v + 1))%I. *)

  (* Lemma sim_getc_heap_priv Q fns Πr Πs : *)
  (*   rec_fn_auth fns -∗ *)
  (*   "getc" ↪ None -∗ *)
  (*   Q (Spec.forever getc_spec_priv, 0) -∗ (* NOTE: Q needs to hold for the initial state of the module? - Am I okay with giving up Q? *) *)
  (*   □ switch_link' Tgt Πr (spec_trans _ Z) Πs ({{ σr POST, *)
  (*     ∃ vs h' σs, *)
  (*     Q σs ∗ *)
  (*     POST (ERCall "getc" vs h') σs ({{ _ Πs, *)
  (*       switch_link Tgt Πs ({{ σs' POST, *)
  (*         ∃ h'' v', *)
  (*           POST (ERReturn v' h'') _ σr ({{ _ Πr', *)
  (*             ⌜Πr' = Πr⌝ ∗ Q σs' }})}})}})}}) -∗ *)
  (*   |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Πr "getc" (getc_fn_spec_priv P). *)
  (* Proof. *)
  (*   iIntros "#Hfns #Hf HQ #Hl /=". *)
  (*   iMod (mstate_var_alloc Z) as (γ) "Hγ". *)
  (*   iMod (mstate_var_split γ 0 with "[$]") as "[Hγ Hγ']". *)
  (*   pose (HS := SpecGS γ). *)

  (*   (* have Π' : option (io_type * rec_ev) → m_state (spec_trans (io_type * rec_ev) Z) → iProp Σ. admit. *) *)
  (*   set (P := (λ (v : Z), (∃ σs, spec_state v ∗ Q σs ∗ (TGT (Spec.forever getc_spec_priv) @ Πs {{ e', sim_post Tgt () Πs e' }} -∗ σs ≈{spec_trans rec_event Z}≈>ₜ Πs))%I)). *)
  (*   iExists P. *)
  (*   iModIntro. iSplit. *)
  (*   - iExists (_, 0). *)
  (*     iFrame. *)
  (*     iIntros "?". *)
  (*     iApply (sim_gen_expr_intro with "[Hγ]") => /= //. *)
  (*   - iIntros "!> % % [% [-> [[% [Hs [HQ Hσs]]] HΦ]]]". *)
  (*     iApply (sim_tgt_rec_Call_external with "[$]"). *)
  (*     iIntros (???) "#?Htoa Haa !>". *)
  (*     iIntros (? σr) "[% [% HΠr]]" => /=. subst. *)
  (*     iApply "Hl" => /=. iSplit!. iFrame. iSplit!. *)
  (*     iIntros (? Π'') "[-> [-> HΠs]]" => /=. *)
  (*     (* Here now I need to be talking about this specific Π - Should I pass this as parameter to the lemma? *) *)
  (*     (* assert (HProblem : Π'' = Π') by admit. subst. *) *)
  (*     iApply "Hσs". rewrite unfold_forever. *)
  (*     iApply sim_getc_spec_heap_priv. *)
  (*     iIntros (??) "[% [% [% [% Hσ]]]]" => /=. *)
  (*     iApply "HΠs" => /=. subst. iSplit!. *)
  (*     (* Π''' probably same as Πs, but I don't care *) *)
  (*     iIntros (? Πs') "[% [% HΠs']]". simplify_eq. *)
  (*     iApply "Hσ". iSplit!. iFrame. *)
  (*     iIntros (??) "[% [? HΠs]]" => /=. *)
  (*     iApply "HΠs'" => /=. subst. iSplit!. *)
  (*     iIntros (? HΠr') "[% HΠr']". subst. *)
  (*     iApply sim_tgt_rec_Waiting_raw. *)
  (*     iSplit. { iIntros. iModIntro. iApply "HΠr'". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. } *)
  (*     iIntros (???) "!>". iApply "HΠr'" => /=. iSplit!. iIntros (??) "[% [% [% HQ]]]". simplify_eq. *)
  (*     iApply "HΠr". iSplit!. iFrame. *)
  (*     iApply "HΦ". iSplit!. iFrame. *)
  (*     iIntros "Hspec". *)
  (*     iApply "HΠs". iSplit!. *)
  (* Qed. *)


End sim_spec.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.

  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_getc_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h');;
    TUb.

  Lemma sim_echo `{!specGS} Π :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    switch Π ({{ κ σ POST0,
      ∃ args h,
      ⌜args = []⌝ ∗
      ⌜κ = Some (Outgoing, ERCall "getc" args h)⌝
      (* ∗ *)
      (* POST0 Tgt _ (spec_trans _ Z) (λ _ Πs, *)
      (*   switch Πs ({{ κs σ' POST1, *)
      (*     ∃ v h', *)
      (*     ⌜κs = Some (Incoming, ERReturn v h)⌝ ∗ *)
      (*     ⌜h' = h⌝ *)
      (*     }})) *)
      }}) -∗
    (* rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_priv -∗ *)
    rec_fn_spec_hoare Tgt Π "echo" ({{ es POST_e, ⌜es = []⌝ }}).
  Proof.
    iIntros "#Hecho #Hgetc HC".
    iIntros (??->).
    iApply (sim_tgt_rec_Call_internal with "Hecho"); [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_AllocA); [done|].
    iIntros "% _ !>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_tgt_rec_Call_external with "Hgetc").
    iIntros (???) "#? Hma Haa !>".
    (* NOTE: Here I am throwing out way back in *)
    iIntros (??) "[% [% _]]" => /=. subst.
    iApply "HC" => /=.
    iSplit!.
  Admitted.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).

  Lemma echo_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (* TODO: Not exactly sure what the list is *)
    (MLFRun None, [], rec_init echo_prog, (getc_spec, 0)) ⪯{m_t,
      spec_trans rec_event Z} (echo_getc_spec, 0).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=".

    (* REVIEW: Am I saying here that I have r/w over the modules, and when I step through one *)
    (* I ensure I cannot change the other by splitting the var? *)
    (* Entire Source Module *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γs) "Hγs".
    (* Entire Target Module *)
    iMod (mstate_var_alloc (m_state m_t)) as (γt) "Hγt".
    (* Event *)
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's spec state *)
    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s 0 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
    (* NOTE: I am fixing here the state of the spec in the source *)
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    (* NOTE: Case splitting on the linking case, which can only be a call because of the empty list  *)
    (* TODO: What is the empty list here, is it previous events? *)
    destruct!/=. case_match; destruct!/=.

    (* NOTE: Changing to source module *)
    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".
    (* NOTE: Now, going into module local reasoning - Giving up one half of the state *)
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iEval (unfold echo_getc_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec) (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis (H := HSrcSpec)). iIntros "% Hγs_s %% [-> [-> _ ]]".

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    (* NOTE: I unify here *)
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "->".

    iIntros "Hγs". iApply sim_gen_stop.
    (* NOTE: I am here going right back into the src module, to get the function name from the assume *)
    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?).
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".

    (* iDestruct (mstate_var_merge with "Hγs_s Hγs_s'") as "[<- Hγs_s]". *)

    iIntros (??) "[-> [-> _]]".
    (* NOTE: The source module here is in a good spot for induction. In target the recursion is on the echo, but
       this is an internal call? So where do I start the recursion? *)

    (* NOTE: Changing into target *)
    rewrite bool_decide_true; [|done].
    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iIntros "Hγs".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* Target's spec module (Right linking case - getc) *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt_r) "Hγt_r".

    (* Target's right spec state*)
    iMod (mstate_var_alloc Z) as (γt_r_s) "Hγt_r_s".
    iMod (mstate_var_split γt_r_s 0 with "[$]") as "[Hγt_r_s Hγt_r_s']".
    pose (HTgtSpec := SpecGS γt_r_s).

    (* TODO: "queue" for linking?  *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γt_q) "Hγt_q".

    (* (* Linking event to pass around *) *)
    iMod (mstate_var_alloc (option rec_ev)) as (γt_oe) "Hγt_oe".

    iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [$] [$] [-]").
    iIntros "Hγt_q Hγt_r Hγt_oe".

    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }

    iApply (sim_gen_expr_intro _ [] with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (Π := tgt_link_left_constP _ _ _ _ _).

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.

    rewrite /echo_prog in Hin. simplify_map_eq.
    (* NOTE: Here, first attempt of proving it with no intermediate lemmas *)
    iApply (sim_tgt_rec_Call_internal); [ | by iApply (rec_fn_intro with "[$]") |]. { done. }
    iModIntro => /=.
    iApply (sim_tgt_rec_AllocA); [done|].
    iIntros "% _ !>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply sim_tgt_rec_Call_external;[by iApply (rec_fn_intro with "[$]")|].
    iIntros (???) "_ Hma Haa !>".

    (* NOTE: Here I am throwing out way back in *)
    iIntros (??) "[% [% HΠ]]" => /=. subst.
    iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'".

    iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
    iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
    iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".

    iIntros (??????).
    destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
    iApply (sim_tgt_link_recv_right with "[-]").
    iApply (sim_gen_expr_intro _ tt with "[Hγt_r_s]"); simpl; [done..|].
    unfold getc_spec. rewrite /TReceive bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    (* NOTE: Throwing out more stuff *)
    iIntros (v) "Hγt_r_s !>". iIntros (??) "[% [% _]]". subst.
    iIntros (?). simplify_eq.

    iDestruct (mstate_var_agree with "Hγt_r_s Hγt_r_s'") as "->".

    iApply (sim_tgt_link_run_right with "[-]").
    iApply (sim_gen_expr_intro _ tt with "[Hγt_r_s]"); simpl; [done..|].
    iApply sim_tgt_TAssume; [done|]. iModIntro.
    iApply sim_tgt_TAssume; [done|]. iModIntro.
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>".
    iApply (sim_gen_TPut with "[Hγt_r_s']"). 1: done.
    iIntros "Hγt_r_s' !>" => /=.
    iApply (sim_gen_TVis with "[-]"). iIntros (?) "Hγt_r_s !>".

    iDestruct (mstate_var_agree with "Hγt_r_s Hγt_r_s'") as "->".

    (* NOTE: Throwing out stuff again *)
    iIntros (??) "[% [% _]]" => /=. subst.
    iIntros (??????). destruct!/=.

    iApply (sim_tgt_link_left_const_recv γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
    iIntros "Hγt_q Hγt_r Hγt_oe".
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!> %%% Hγt_q' Hγt_r' Hγt_oe'".

    iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
    iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
    iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
    iIntros (?). simplify_eq.

    iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [$] [$] [-]").
    iIntros "Hγt_q Hγt_r Hγt_oe".
    (* NOTE - finally going back in *)
    iApply "HΠ". iSplit!. iFrame.

    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.

    iApply sim_tgt_rec_Call_external;[by iApply (rec_fn_intro with "[$]")|].
    iIntros (???) "_ ? ? !> %% [% [% HΠ]] %%% Hγt_q' Hγt_r' Hγt_oe'" => /=. subst.

    iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
    iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
    iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".

    iIntros (??????).
    destruct!/=. rewrite bool_decide_false //.
    iIntros (?) "Hγs' Hγκ Hγt".

    iDestruct (mstate_var_merge with "Hγs Hγs'") as "[<- Hγs]".

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].

    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s".
    iApply (sim_src_TExist (H := HSrcSpec)).
    rewrite bind_bind.
    iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s'".
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "<-".
    iIntros (??) "[% [% _]]" => /=. simplify_eq.
    iApply (sim_src_constP_elim with "[Hγt] [Hγκ //] [-]"). 1: done.
    iIntros "Hγt Hγκ". iSplit!.

    iApply (@sim_tgt_constP_intro _ _ _ m_t (spec_trans rec_event Z) γt γs γκ with "Hγt Hγs Hγκ").
    iIntros "Hγs".

    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).

    destruct!/=. case_match; destruct!/=.
    { (* Incoming Call *)
      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
      rewrite bind_bind.
      iApply (sim_src_TExist (H := HSrcSpec)).
      rewrite bind_bind.
      iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s".
      iIntros (??) "[% [% ?]]"=> /=.
      iApply (sim_src_constP_elim γt γκ with "[Hγt] [Hγκ] [-]"); [done..|].
      iIntros "Hγt Hγκ". iSplit!.

      (* TODO : This is quite annoying *)
      iApply (@sim_tgt_constP_intro _ _ _ m_t (spec_trans rec_event Z) γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
      iApply (sim_gen_stop). 

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|]. iIntros "Hγs Hγt Hγκ".
      subst.
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
      iApply (sim_src_TUb (H := HSrcSpec)). 
    }

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
      rewrite bind_bind.
      iApply (sim_src_TExist (H := HSrcSpec)).
      rewrite bind_bind.
      iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s".
      iIntros (??) "[% [% ?]]"=> /=.
      iApply (sim_src_constP_elim γt γκ with "[Hγt] [Hγκ] [-]"); [done..|].
      iIntros "Hγt Hγκ". iSplit!.

      (* TODO : This is quite annoying *)

      iApply (@sim_tgt_constP_intro _ _ _ m_t (spec_trans rec_event Z) γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
      iApply (sim_gen_stop).

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|]. iIntros "Hγs Hγt Hγκ".
      subst.
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
      setoid_rewrite bind_ret_l.
      iApply (sim_src_TAssume (H := HSrcSpec)). iIntros "->".
      iApply (sim_gen_expr_stop). iIntros (?) "/= % Hγs_s".
      iApply (sim_gen_stop).


      iApply (sim_src_constP_elim γt γκ with "[Hγt] [Hγκ] [-]"); [done..|].
      iIntros "Hγt Hγκ". iSplit!.

      iApply (@sim_tgt_constP_intro _ _ _ m_t (spec_trans rec_event Z) γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
      iApply (sim_tgt_link_left_const_recv γt_q γt_r γt_oe with "Hγt_q [Hγt_r] [Hγt_oe] [-]"); [done..|].
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!> %%% Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iIntros (?). simplify_eq.

      iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "Hγt_q [Hγt_r] [Hγt_oe] [-]"); [done..|].
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply "HΠ" => /=. iSplit!. iFrame.
      iApply sim_tgt_rec_LetE. iModIntro => /=.

      (* TODO: Here I am kind of done. *)
      iApply sim_gen_expr_None.
      iIntros (???) "/= ? %% /=".
      iIntros "[% [% _]] /=". subst. iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'" => /=.

      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
      iApply (sim_src_TUb_end (H := HSrcSpec)).
    Qed.

End echo_getc.
