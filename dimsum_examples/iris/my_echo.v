From iris.proofmode Require Import proofmode.

From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO: upstream? *)
Arguments subst_static _ !_ /.

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

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

(* ********************************************************************************************** *)
(* getc rec program that calls read *)
(* ********************************************************************************************** *)

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

(* ********************************************************************************************** *)
(* read rec program that reads `c` ints into the pointer `l` from a buffer of increasing numbers *)
(* ********************************************************************************************** *)

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

(* ********************************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* ********************************************************************************************** *)

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

(* ********************************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* ********************************************************************************************** *)
Section sim_spec.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

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

  Definition getc_fn_spec_priv `{!specGS} (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, ⌜es = []⌝ ∗ spec_state v ∗
    POST (λ v', (⌜v' = ValNum v⌝) ∗ spec_state (v + 1))%I.

  Lemma sim_getc_heap_priv `{!specGS} fns Π (w : Z) :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    (spec_state w) -∗
    switch_link Tgt Π ({{ σ0 POST,
      ∃ vs h' v,
    POST (ERCall "getc" vs h') (spec_trans _ Z) (getc_spec_priv, v) ({{ _ Πr,
    switch_link Tgt Πr ({{ σ POST,
      ∃ h'' v', ⌜σ = (getc_spec_priv, (v' + 1)%Z)⌝ ∗
    POST (ERReturn v' h'') _ σ0 ({{ _ Πx,
      ⌜Πx = Π⌝}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_priv.
  Proof.
    iIntros "#Hfns #Hf Hs HΠ" (es Φ) "HΦ". iDestruct "HΦ" as (v ->) "[Hs' HΦ]".
    iDestruct (mstate_var_agree with "Hs Hs'") as "->".
    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#?Htoa Haa !>".
    iIntros (??) "[% [% Hσ]]". subst.
    iApply "HΠ" => /=. iSplit!. iIntros (??) "[-> HΠi]".

    iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|].
    iApply sim_getc_spec_heap_priv => /=. iIntros (??). iDestruct 1 as (????) "HC". subst.
    iApply "HΠi". iSplit!. iIntros (??) "[% [% HΠr]]". simplify_eq/=.
    iApply "HC".
    iExists (_).
    iSplit!.
    iSplitL "Hs'". { done. }
    iIntros (??). simpl. iDestruct 1 as (??) "[Hs Hs']".
    iApply "HΠr".
    iSplit!. iIntros (??) "[% HΠf]". simplify_eq.
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HΠf". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
    iIntros (???) "!>". iApply "HΠf". iSplit!. iIntros (??[?[??]]). simplify_eq.
    iApply "Hσ". iSplit!.
    iFrame.
    iApply "HΦ".
    by iFrame.
  Qed.
End sim_spec.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.
  (* TODO - I should probably fix the spec state? *)
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  (* TODO, experimental *)
  Definition echo_getc_spec_body : spec rec_event Z unit :=
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h');;
    TRet tt.

  Definition echo_getc_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    Spec.forever echo_getc_spec_body.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).

  Goal m_state (spec_trans rec_event Z) = (spec rec_event Z void * Z)%type. reflexivity. Qed.

  (* TODO: No idea what this even means *)
  Lemma echo_getc_sim (v : Z):
    (* TODO: What exactly is the state interp *)
    rec_state_interp (rec_init echo_prog) None -∗
    (* TODO: MLFRun? *)
    (MLFRun None, [], rec_init echo_prog, (getc_spec_priv, v)) ⪯{m_t,
      spec_trans rec_event Z} (echo_getc_spec, v).
  Proof. Admitted.

End echo_getc.
