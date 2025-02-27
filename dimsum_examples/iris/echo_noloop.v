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

  (* Lemma sim_getc_spec_heap_priv `{!specGS} Π Φ : *)
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
  (* Proof. *)
  (*   iDestruct 1 as "HC". *)
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
  (*   iSplit!. iFrame. *)
  (*   (* Here I need strong assumptions *) *)
  (*   iIntros (??) "[% [% H]]". subst. *)
  (*   iApply "HΠ". by iFrame. *)
  (* Qed. *)

  Lemma sim_getc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ ({{ σ' Π',
      ∃ v, ⌜f = "getc"⌝ ∗ ⌜es = []⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
      ⌜Π' = Π⌝ ∗ (* I think this need not be true? - Check what it looks like - what's the difference between this and just requiring Π for the next switch *)
    switch Π ({{ κ σ POST,
      ⌜κ = Some (Outgoing, ERReturn (ValNum v) h)⌝ ∗ spec_state (v + 1)
    (* POST Tgt _ _ ({{ σ' Π', *)
    (*   ⌜σ' = σ⌝ ∗ ⌜Π' = Π⌝ ∗ spec_state (v + 1) }})*)
    }})}})}}) -∗
    TGT getc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "Hs".
    rewrite /getc_spec /TReceive bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v') "Hs' !>".
    iIntros (??) "[% [% HΠ]]".
    subst.
    iApply "Hs" => /=. iSplit!. iIntros (??) => /=.
    iDestruct 1 as (???) "[Hs [% [% HC]]]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs']"); simpl; [done..|].
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>".
    iApply (sim_gen_TPut with "[Hs]"). 1: done.
    iIntros "Hs". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hs'".
    iDestruct (mstate_var_agree with "Hs Hs'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% HΠ']]" => /=. simplify_eq.
    iApply "HC". simpl.
    iSplit!.
Qed.

  Definition getc_fn_spec v (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ⌜es = []⌝ ∗ POST (λ ret, ⌜ret = v⌝)%I.

  Lemma sim_getc fns Π v:
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    switch Π ({{κ σt POST,
      ∃ h, ⌜κ = Some (Outgoing, ERCall "getc" [] h)⌝ ∗
    POST Tgt _ (spec_trans _ Z) ({{σs Πs,
      ⌜σs = (getc_spec, v)⌝ ∗
    switch Πs ({{κ σs' POST,
      ∃ e, ⌜κ = Some (Incoming, e)⌝ ∗
    POST Tgt _ _ ({{σt' Πt',
      ⌜σt' = σt⌝ ∗ ⌜Πt' = Π⌝ ∗ ⌜e = (ERCall "getc" [] h)⌝ ∗
    switch Π ({{κ σt POST,
      ∃ e, ⌜κ = Some (Incoming, e)⌝ ∗
    POST Tgt _ _ ({{σs Πs',
      ⌜e = ERReturn v h⌝ ∗ ⌜Πs = Πs'⌝ ∗ ⌜σs = σs'⌝ ∗
    switch Πs ({{κ σ POST,
      ⌜κ = Some (Outgoing, ERReturn v h)⌝ ∗
      (* Hm *)
    POST Tgt _ _ ({{σt' Πt',
      ⌜σt' = σt⌝ ∗ ⌜Πt' = Π⌝
      }})
    }})}})}})}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "getc" (getc_fn_spec v).
  Proof.
    iIntros "#? ? Hs". iIntros (es Φ) "[-> HΦ]".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iIntros (??) "[% [% HΠ]]". subst. iApply "Hs". iSplit!. iIntros (??) "[-> Hs]".

    iMod (mstate_var_alloc Z) as (γ) "?".
    iMod (mstate_var_split γ v with "[$]") as "[Hγ Hγ']".
    pose (Hspec := SpecGS γ).

    iApply (sim_gen_expr_intro _ tt with "[Hγ]"); simpl; [done..|].
    unfold getc_spec.
    rewrite /TReceive bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v') "Hγ !>".
    iIntros (??) "[% [% _]]".
    subst.
    iApply "Hs" => /=. iSplit!. iIntros (??) => /=.
    iDestruct 1 as (???) "Hs". subst.

    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs" => /=. iSplit!.
    iIntros (??) "[% [% [% Hs]]]" => /=. simplify_eq.

    iApply (sim_gen_expr_intro _ tt with "[Hγ]"); simpl; [done..|].
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>".
    iApply (sim_gen_TPut with "[Hγ']"). 1: done.
    iIntros "Hγ". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hγ'".
    iDestruct (mstate_var_agree with "Hγ Hγ'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% _]]" => /=. simplify_eq.
    iApply "Hs" => /=. iSplit!. iIntros (??) "[% %]". subst.
    iApply "HΠ" => /=. iSplit!. iFrame. by iApply "HΦ".
  Qed.

End sim_getc.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.

  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_getc_spec_body : spec rec_event Z void :=
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h');;
    TUb.

  Definition echo_getc_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    echo_getc_spec_body.

  Lemma sim_echo Π :
    "echo" ↪ Some echo_rec -∗
    rec_fn_spec_hoare Tgt Π "getc" (getc_fn_spec 0) -∗
    rec_fn_spec_hoare Tgt Π "echo" (λ es POST, ⌜es = []⌝ ∗
      rec_fn_spec_hoare Tgt Π "putc" (λ es POST1, ⌜es = [Val 0]⌝ ∗ POST1 (λ _, POST (λ v, ⌜v = 0⌝)))).
  Proof.
    iIntros "#? Hf".
    iIntros (es Φ) => /=. iDestruct 1 as (->) "HΦ".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hoof !>".
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply "Hf". rewrite /getc_fn_spec. iSplit!. iIntros (?->).
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply "HΦ" => /=. iSplit!.
    iIntros "% HΦ".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply sim_gen_expr_stop. iSplit!.
    iSplitL "Hoof".
    { destruct ls; [by iApply big_sepL2_nil |done]. }
    by iApply "HΦ".
  Qed.

  Lemma sim_echo_full Π_t γs (σ_s : m_state (spec_trans _ Z)) :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γs ⤳ σ_s -∗
    ⌜σ_s.1 ≡ echo_getc_spec_body⌝ -∗
    ⌜σ_s.2 = 0⌝ -∗
    rec_fn_spec_hoare Tgt Π_t "echo" ({{ es POST_e,
      ⌜es = []⌝ ∗
      switch Π_t ({{ κ0 σ_t POST0,
        ∃ vs h (σs : m_state (spec_trans rec_event Z)),
         γs ⤳ σs ∗ ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
      POST0 Src _ (spec_trans _ Z) ({{ σ_s0 Π_s,
        ⌜σ_s0 = σs⌝ ∗
      switch Π_s ({{ κ1 σ_s1 POST1,
        ⌜κ1 = κ0⌝ ∗
      (* TODO: This is super counter-intuitive *)
      POST1 Src _ (spec_trans _ Z) ({{ σ_s1' Π_s',
        ⌜Π_s' = Π_s⌝ ∗ ⌜σ_s1 = σ_s1'⌝ ∗
        ∃ e : rec_ev,
      switch Π_s ({{ κ3 σ_s2 POST2,
        ⌜κ3 = Some (Incoming, e)⌝ ∗
      POST2 Src _ (spec_trans _ Z) ({{ σ_s2' Π_s',
        ⌜Π_s' = Π_s⌝ ∗ ⌜σ_s2 = σ_s2'⌝ ∗
      switch Π_s ({{ κ4 σ_s3 POST3,
        ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
      POST3 Tgt _ _ ({{ σ_t1 Π_t',
        ⌜σ_t1 = σ_t⌝ ∗ γs ⤳ σ_s3 ∗ ⌜Π_t' = Π_t⌝ ∗
      switch Π_t ({{ κ5 σ_t2 POST4,
        ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
      POST4 Tgt rec_event rec_trans ({{ σ_t3 Π_t',
        ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π_t = Π_t'⌝}}) }})}}) }})}}) }})}}) }})}}) }}) ∗
      POST_e (λ v, ⌜v = 0⌝)
    }}).
  Proof.
    iIntros "#?#?#? Hγs %%%% [-> [Hs Hend]]" => /=.

    iApply (sim_tgt_rec_Call_internal with "[$]"); [done |]. iModIntro.
    iApply (sim_tgt_rec_AllocA); [done|].
    iIntros "% Hoof !>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.

    iApply (sim_getc with "[$]").
    iSplit!.
    iIntros (? ->).

    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst.
    iApply "Hs" => /=. iSplit!. iFrame. iSplit!.
    iIntros (? Πs) "[% Hs']" => /=. subst.

    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s σ_s.2 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].

    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s".
    iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind.

    (* Here TCallRet *) (* TODO: What do the things I am throwing out allow me to do? *)

    iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s'".
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "<-".
    iIntros (??) "[% [% _]]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. by rewrite H0.
    iIntros (??) "[% [% [% Hs']]]" => /=. subst.

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    rewrite bind_bind. iApply sim_src_TExist. rewrite bind_bind.
    iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s".
    iIntros (??) "[% [% _]]" => /=. subst.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??) "[% [% Hs']]" => /=. subst.
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    destruct e. { iApply sim_src_TUb.  }
    rewrite bind_ret_l. iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
    iIntros (?) "/= % Hγs_s". iApply sim_gen_stop.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??)"[% [? [% Hs]]]". subst.
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs". iSplit!. iIntros (??) "[% [% %]]" => /=. subst.
    iApply "HΠ" => /=. iSplit!. iFrame.
    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply sim_gen_expr_stop. iSplit!.
    iSplitL "Hoof".
    { destruct ls; [by iApply big_sepL2_nil |done]. }
    by iApply "Hend".
  Qed.

  (* NOTE: I am creating here my own ghost variables for the spec state of the source module *)
  (* Lemma sim_echo_full Π_t γs (σ_s : m_state (spec_trans rec_event Z)) : *)
  (*   "echo" ↪ Some echo_rec -∗ *)
  (*   "getc" ↪ None -∗ *)
  (*   "putc" ↪ None -∗ *)
  (*   γs ⤳ σ_s -∗ *)
  (*   ⌜σ_s.1 ≡ echo_getc_spec_body⌝ -∗ *)
  (*   ⌜σ_s.2 = 0⌝ -∗ *)
  (*   rec_fn_spec_hoare Tgt Π_t "echo" ({{ es POST_e, *)
  (*     ⌜es = []⌝ ∗ *)
  (*       switch Π_t ({{κ1 σ_t POST1, *)
  (*         ∃ vs h (σs : m_state (spec_trans rec_event Z)), γs ⤳ σs ∗ *)
  (*         ⌜κ1 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗ *)
  (*       POST1 Src _ (spec_trans _ Z) ({{ σ_s1 Π_s, *)
  (*         ⌜σ_s1 = σs⌝ ∗ *)
  (*       switch Π_s ({{κ2 σ_s2 POST2, *)
  (*         ⌜κ1 = κ2⌝ ∗ *)
  (*       POST2 Tgt _ _ ({{ σ_t2 Π_t2, *)
  (*         (* Maybe I don't need these *) *)
  (*         ⌜σ_t2 = σ_t⌝ ∗ ⌜Π_t2 = Π_t⌝ ∗ *)
  (*       switch Π_t ({{κ2 σ_t3 POST3, *)
  (*         ∃ e, ⌜κ2 = Some (Incoming, e)⌝ ∗ *)
  (*       POST3 Src _ _ ({{σ_s3 Π_s2, *)
  (*         ⌜Π_s2 = Π_s⌝ ∗ ⌜σ_s3 = σ_s2⌝ ∗ *)
  (*       switch Π_s ({{κ3 σ_s4 POST4, *)
  (*         ⌜κ3 = κ2⌝ ∗ *)
  (*       POST4 Src _ _ ({{σ_s5 Π_s3, *)
  (*         ⌜σ_s5 = σ_s4⌝ ∗ ⌜Π_s3 = Π_s⌝ ∗ *)
  (*       switch Π_s ({{κ4 σ_s6 POST5, *)
  (*         ⌜κ4 = None⌝ ∗ *)
  (*       POST5 Tgt _ _ ({{σ_t4 Π_t2, *)
  (*         ⌜Π_t2 = Π_t⌝ ∗ ⌜σ_t4 = σ_t3⌝ *)
  (*     }})}})}})}})}})}})}})}})}})}}) ∗ *)
  (*     POST_e (λ v, ⌜v = 0⌝) *)
  (*   }}). *)
  (* Proof. *)
  (*   iIntros "#?#?#? Hγs %%%% [-> [Hs Hend]]" => /=. *)

  (*   iApply (sim_tgt_rec_Call_internal with "[$]"). done. iModIntro. *)
  (*   iApply (sim_tgt_rec_AllocA); [done|]. *)
  (*   iIntros "% Hoof !>" => /=. *)
  (*   iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=. *)

  (*   iApply (sim_getc with "[$]"). *)
  (*   iSplit!. *)
  (*   iIntros (? ->). *)

  (*   iApply sim_tgt_rec_LetE. iModIntro => /=. *)
  (*   iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=. *)

  (*   iApply (sim_tgt_rec_Call_external with "[$]"). *)
  (*   iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst. *)
  (*   iApply "Hs" => /=. iSplit!. iFrame. iSplit!. *)
  (*   iIntros (? Πs) "[% Hs']" => /=. subst. *)

  (*   iMod (mstate_var_alloc Z) as (γs_s) "?". *)
  (*   iMod (mstate_var_split γs_s σ_s.2 with "[$]") as "[Hγs_s Hγs_s']". *)
  (*   pose (HSrcSpec := SpecGS γs_s). *)

  (*   iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. *)

  (*   iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. *)
  (*   iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". *)
  (*   iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind. *)

  (*   (* Here TCallRet *) (* TODO: What do the things I am throwing out allow me to do? *) *)

  (*   iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s'". *)
  (*   iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "<-". *)
  (*   iIntros (??) "[% [% _]]" => /=. simplify_eq. *)
  (*   iApply "Hs'". iSplit!. by rewrite H0. *)
  (*   iIntros (??) "[% [% Hs']]" => /=. subst. *)
  (*   iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>". *)
  (*   iApply "Hs'" => /=. iSplit!. *)
  (*   iIntros (??) "[% [% Hs']]". subst. *)

  (*   iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. *)
  (*   rewrite bind_bind. iApply sim_src_TExist. rewrite bind_bind. *)
  (*   iApply (sim_gen_TVis (H := HSrcSpec) with "[-]"). iIntros (?) "Hγs_s". *)
  (*   iIntros (??) "[% [% _]]" => /=. *)
  (*   iApply "Hs'" => /=. iSplit!. *)
  (*   iIntros (??) "[% [% Hs']]" => /=. subst. *)
  (*   iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. *)
  (*   destruct e. { iApply sim_src_TUb.  } *)
  (*   rewrite bind_ret_l. iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop. *)
  (*   iIntros (?) "/= % Hγs_s". iApply sim_gen_stop. *)
  (*   iApply "Hs'" => /=. iSplit!. *)
  (*   iIntros (??) "[% %]". subst. *)
  (*   iApply "HΠ" => /=. iSplit!. iFrame. *)
  (*   iApply sim_tgt_rec_LetE. iModIntro => /=. *)
  (*   iApply sim_gen_expr_stop. iSplit!. *)
  (*   iSplitL "Hoof". *)
  (*   { destruct ls; [by iApply big_sepL2_nil |done]. } *)
  (*   by iApply "Hend". *)
  (* Qed. *)

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

    set (Π_s := sim_src_constP γκ γt (EV := rec_event) (m_t := m_t) (m_s := spec_trans rec_event Z)).
    set (Π_t := tgt_link_left_constP _ _ _ _ _).

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.

    iDestruct (mstate_var_merge with "Hγs_s Hγs_s'") as "[% Hγs_s]".

    rewrite /echo_prog in Hin. simplify_map_eq.

    (**********************)
    (******** TODO ********)
    (**********************)

    iApply (sim_echo_full with "[] [] [] [Hγs //] [//] [//]"). 1-3: by iApply (rec_fn_intro with "[$]") => /=.
    iSplit!.
    iSplitL.
    - iIntros (??) "[% [% [% [Hγs [% HC]]]]]" => /=.
      subst. iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
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
      iApply (sim_tgt_link_left_const_recv γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC".
      iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iIntros (?). simplify_eq.

      iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "???".

      iApply "HC". iSplit!.
    - admit.
    Admitted.

End echo_getc.
