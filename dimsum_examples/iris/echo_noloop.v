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
Section sim_getc.
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

  (* Lemma sim_getc_spec `{!specGS} Π Φ k : *)
  (*   switch Π ({{ κ σ POST, *)
  (*     ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗ *)
  (*     POST Tgt _ (spec_trans _ Z) ({{ σ' Π', *)
  (*       ∃ v, ⌜σ' = σ⌝ ∗ ⌜f = "getc"⌝ ∗ ⌜vs = []⌝ ∗ (spec_state v) ∗ *)
  (*     switch Π' ({{ κ σ POST, *)
  (*     ⌜κ = (Some (Outgoing, ERReturn (ValNum v) h))⌝ ∗ *)
  (*     spec_state (v + 1) ∗ *)
  (*     POST Tgt _ (spec_trans _ Z) ({{σ'' Π'', *)
  (*       ⌜Π'' = Π⌝ ∗ *)
  (*       ⌜σ'' = σ⌝ ∗ *)
  (*       TGT k tt @ Π {{ Φ }} *)
  (*       }}) *)
  (*     }})}})}}) -∗ *)
  (*   TGT Spec.bind getc_spec_priv k @ Π {{ Φ }}. *)
  (* Proof. Admitted. *)

  Lemma sim_getc `{!specGS} Π :
    "getc" ↪ None -∗
    rec_fn_spec_hoare Tgt Π "getc" ({{es POST, ⌜es = []⌝ ∗ POST ({{ v, ⌜v = 0⌝}}) }}).
  Proof. Admitted.

End sim_getc.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.

  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_getc_spec_body : spec rec_event Z unit :=
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h').

  Definition echo_getc_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    Spec.forever echo_getc_spec_body.


  Lemma sim_echo_full Π_t γs (σ_s : m_state (spec_trans _ Z)) :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γs ⤳ σ_s -∗
    ⌜σ_s.1 ≡ Spec.forever echo_getc_spec_body⌝ -∗
    ⌜σ_s.2 = 0⌝ -∗
    rec_fn_spec_hoare Tgt Π_t "echo" ({{ es POST_e,
      ⌜es = []⌝ ∗
      □ switch Π_t ({{κ1 σ_t POST1,
          ∃ vs h,
          ⌜κ1 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
        POST1 Src _ (spec_trans _ Z) ({{ σ_s1 Π_s,
          ⌜σ_s1 = σ_s⌝ ∗
        switch Π_s ({{κ2 σ_s2 POST2,
          ⌜κ1 = κ2⌝ ∗
        POST2 Tgt _ _ ({{ σ_t2 Π_t2,
          (* Maybe I don't need these *)
          ⌜σ_t2 = σ_t⌝ ∗ ⌜Π_t2 = Π_t⌝ ∗
        switch Π_t ({{κ2 σ_t3 POST3,
          ∃ e, ⌜κ2 = Some (Incoming, e)⌝ ∗
        POST3 Src _ _ ({{σ_s3 Π_s2,
          ⌜Π_s2 = Π_s⌝ ∗ ⌜σ_s3 = σ_s2⌝ ∗
        switch Π_s ({{κ3 σ_s4 POST4,
          ⌜κ3 = κ2⌝ ∗
        POST4 Src _ _ ({{σ_s5 Π_s3,
          ⌜σ_s5 = σ_s4⌝ ∗ ⌜Π_s3 = Π_s⌝ ∗
        switch Π_s ({{κ4 σ_s6 POST5,
          ⌜κ4 = None⌝ ∗
        POST5 Tgt _ _ ({{σ_t4 Π_t2,
          ⌜Π_t2 = Π_t⌝ ∗ ⌜σ_t4 = σ_t3⌝
      }})}})}})}})}})}})}})}})}})}})
    }}).
  Proof.
    iIntros "#?#?#? Hγs %%%% [-> #Hs]" => /=.
    set (X := switch _ _).

    iApply (sim_tgt_rec_Call_internal with "[$]"). done. iModIntro.
    iApply (sim_tgt_rec_AllocA); [done|].
    iIntros "% _ !>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_getc with "[$]"). iSplit!.
    iIntros (? ->).

    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst.
    iApply "Hs" => /=. iSplit!. iIntros (? Πs) "[% Hs']" => /=. subst.

    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s σ_s.2 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].

    rewrite unfold_forever. rewrite bind_bind.
    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. rewrite bind_bind.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". rewrite bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind bind_bind.

    (* Here TCallRet *) (* TODO: What do the things I am throwing out allow me to do? *)

    iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s'".
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "<-".
    iIntros (??) "[% [% _]]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. by rewrite H0.
    iIntros (??) "[% [% Hs']]" => /=. subst.
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs'" => /=. iSplit!.
    iIntros (??) "[% [% Hs']]". subst.

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    rewrite bind_bind. iApply sim_src_TExist. rewrite bind_bind.
    iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s".
    iIntros (??) "[% [% _]]" => /=.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??) "[% [% Hs']]" => /=. subst.
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    destruct e. { iApply sim_src_TUb.  }
    rewrite bind_ret_l. iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
    iIntros (?) "/= % Hγs_s". iApply sim_gen_stop.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??) "[% %]". subst.
    iApply "HΠ" => /=. iSplit!. iFrame.
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
