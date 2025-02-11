From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint.

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

(* NOTE: Trying to formulate some things for TCallRet *)
Section TCallRet.

Context `{!dimsumGS Σ} `{!specGS} {S : Type}.
(* Canonical Structure spec_mod_lang. *)

(* NOTE - In src position we only need to ensure `Outgoing Call` and any incoming event *)
(* This cannot be quite true, in case it's not undefined, I'll have to refine it ? *)

(* The statement holds, assuming the following restriction on Π.
   ...
 *)
(* TODO: What does it mean if POST is unused in the hypothesis *)

Compute m_state (spec_trans (io_type * rec_ev) S).
(* Provable spec, but actually not what I'd want. I am now requiring a Return rather than case splitting on it *)
Lemma sim_src_TCallRet f vs h (k: _ → spec rec_event S void) Π Φ :
  switch Π ({{κ σ POST,
    ∃ f' vs' h1,
      ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗
      ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
      POST Src _ (spec_trans rec_event S) ({{σ' Π',
        ⌜σ = σ'⌝ ∗ ∃ v h',
        switch Π' ({{κ σ POST,
          (* TODO: Obligation? *)
          ⌜κ = Some (Incoming, ERReturn v h')⌝ ∗
          POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
            ⌜σ = σ''⌝ ∗
            ⌜Π = Π''⌝ ∗
            SRC (k (v, h')) @ Π {{ Φ }}
            }})
        }})
        }})
    }}) -∗
  SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
Proof.
  iIntros "HC" => /=. rewrite /TCallRet bind_bind.
  iApply sim_gen_TVis. iIntros (s) "Hs". iIntros "% % /=". iIntros "[% [% HΠ]]". subst.
  iApply "HC" => /=. iSplit!.
  iIntros (??) "[% [% [% HC]]]" => /=. subst.
  iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|].
  rewrite bind_bind.  iApply sim_src_TExist.
  rewrite bind_bind. iApply sim_gen_TVis. iIntros (s') "Hs". iIntros (??) "[% [% HΠ']]" => /=.
  subst. iApply "HC" => /=. iSplit!.
  iIntros (??) "[% [% H']]". subst.
  iApply "HΠ". iSplit!. iSplitL "Hs". 1: done.
  by rewrite bind_ret_l.
  Qed.

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

  Lemma sim_echo' Π :
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
  Proof. Admitted. (* I did this in the old echo file *)

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
  Proof. Admitted.
End echo.

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

  Definition getc_spec_priv : spec rec_event Z unit :=
    (* Spec.forever( *)
    (* Incoming call of getc *)
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    (* There is a current position of the buffer *)
    v ← TGet;
    TPut (v + 1);;
    (* Return old position *)
    TVis (Outgoing, ERReturn (ValNum v) h).

  Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
    γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
    inv H0. by dimsum.core.axioms.simplify_K.
  Qed.

  (* REVIEW: Do I get all my states back? *)
  Lemma sim_getc_spec_heap_priv `{!specGS} Π Φ k :
    switch Π ({{ κ σ POST,
      ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
      POST Tgt _ (spec_trans _ Z) ({{ σ' Π',
        ∃ v, ⌜σ' = σ⌝ ∗ ⌜f = "getc"⌝ ∗ ⌜vs = []⌝ ∗ (spec_state v) ∗
      switch Π' ({{ κ σ POST,
      ⌜κ = (Some (Outgoing, ERReturn (ValNum v) h))⌝ ∗
      spec_state (v + 1) ∗
      POST Tgt _ (spec_trans _ Z) ({{σ'' Π'',
        ⌜Π'' = Π⌝ ∗
        ⌜σ'' = σ⌝ ∗
        TGT k tt @ Π {{ Φ }}
        }})
      }})}})}}) -∗
    TGT Spec.bind getc_spec_priv k @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC".
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v) "Hs !>". simpl.
    iIntros (??) "[% [% HΠ]]". simpl.
    subst.
    iApply "HC". simpl. iSplit!. iIntros (??).
    iDestruct 1 as (????) "[Hs' HC]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>".
    rewrite bind_bind. iApply (sim_gen_TPut with "[Hs']"). 1: done.
    iIntros "Hs". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v') "Hs'".
    iDestruct (mstate_var_agree with "Hs Hs'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% HΠ']]" => /=. simplify_eq.
    iApply "HC". simpl.
    iSplit!. iFrame.
    (* Here I need strong assumptions *)
    iIntros (??) "[% [% H]]". subst.
    iApply "HΠ". by iFrame.
  Qed.

  Definition getc_fn_spec_priv (P: Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, ⌜es = []⌝ ∗ P v ∗
    POST (λ v', (⌜v' = ValNum v⌝) ∗ P (v + 1))%I.

Definition switch_link' `{!dimsumGS Σ} {S EV} (ts : tgt_src) (Π : option (io_event EV) → S → iProp Σ)
  (m : mod_trans (io_event EV)) (Π' : option (io_event EV) → m_state m → iProp Σ) (K : _) : iProp Σ :=
  switch Π ({{ κ σ0 POST,
    K σ0 ({{ e σ2 K2, ⌜κ = Some (Outgoing, e)⌝ ∗
  POST ts _ m ({{ σi Πi,
    ⌜σi = σ2⌝ ∗ ⌜Πi = Π'⌝ ∗
  switch Πi ({{ κ' σ POST,
    ∃ e', ⌜κ' = Some (Incoming, e')⌝ ∗
  POST ts _ m ({{ σr Πr,
    ⌜σr = σ⌝ ∗ ⌜e' = e⌝ ∗ K2 σ Πr}})}})}})}})}})%I.

(* TODO : Maybe think about notation - more general for switch *)
(* (WP (Spec.forever getc_spec_priv) @ Π' {{ e', sim_post Tgt () Π' e' }} -∗ σs ≈{spec_trans rec_event Z}≈>ₜ Π') *)

  (* The actual P?: λ v. ∃ σs. spec_state v ∗ Q σs ∗ (TGT Spec.forever ... @ Π {}) -∗ σs ≈≈> Π *)
  Lemma sim_getc_heap_priv Q fns Πr Πs :
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    Q (Spec.forever getc_spec_priv, 0) -∗ (* NOTE: Q needs to hold for the initial state of the module? - Am I okay with giving up Q? *)
    □ switch_link' Tgt Πr (spec_trans _ Z) Πs ({{ σr POST,
      ∃ vs h' σs,
      Q σs ∗
      POST (ERCall "getc" vs h') σs ({{ _ Πs,
        switch_link Tgt Πs ({{ σs' POST,
          ∃ h'' v',
            POST (ERReturn v' h'') _ σr ({{ _ Πr',
              ⌜Πr' = Πr⌝ ∗ Q σs' }})}})}})}}) -∗
    |==> ∃ P, P 0 ∗ □ rec_fn_spec_hoare Tgt Πr "getc" (getc_fn_spec_priv P).
  Proof.
    iIntros "#Hfns #Hf HQ #Hl /=".
    iMod (mstate_var_alloc Z) as (γ) "Hγ".
    iMod (mstate_var_split γ 0 with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    (* have Π' : option (io_type * rec_ev) → m_state (spec_trans (io_type * rec_ev) Z) → iProp Σ. admit. *)
    set (P := (λ (v : Z), (∃ σs, spec_state v ∗ Q σs ∗ (TGT (Spec.forever getc_spec_priv) @ Πs {{ e', sim_post Tgt () Πs e' }} -∗ σs ≈{spec_trans rec_event Z}≈>ₜ Πs))%I)).
    iExists P.
    iModIntro. iSplit.
    - iExists (_, 0).
      iFrame.
      iIntros "?".
      iApply (sim_gen_expr_intro with "[Hγ]") => /= //.
    - iIntros "!> % % [% [-> [[% [Hs [HQ Hσs]]] HΦ]]]".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#?Htoa Haa !>".
      iIntros (? σr) "[% [% HΠr]]" => /=. subst.
      iApply "Hl" => /=. iSplit!. iFrame. iSplit!.
      iIntros (? Π'') "[-> [-> HΠs]]" => /=.
      (* Here now I need to be talking about this specific Π - Should I pass this as parameter to the lemma? *)
      (* assert (HProblem : Π'' = Π') by admit. subst. *)
      iApply "Hσs". rewrite unfold_forever.
      iApply sim_getc_spec_heap_priv.
      iIntros (??) "[% [% [% [% Hσ]]]]" => /=.
      iApply "HΠs" => /=. subst. iSplit!.
      (* Π''' probably same as Πs, but I don't care *)
      iIntros (? Πs') "[% [% HΠs']]". simplify_eq.
      iApply "Hσ". iSplit!. iFrame.
      iIntros (??) "[% [? HΠs]]" => /=.
      iApply "HΠs'" => /=. subst. iSplit!.
      iIntros (? HΠr') "[% HΠr']". subst.
      iApply sim_tgt_rec_Waiting_raw.
      iSplit. { iIntros. iModIntro. iApply "HΠr'". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
      iIntros (???) "!>". iApply "HΠr'" => /=. iSplit!. iIntros (??) "[% [% [% HQ]]]". simplify_eq.
      iApply "HΠr". iSplit!. iFrame.
      iApply "HΦ". iSplit!. iFrame.
      iIntros "Hspec".
      iApply "HΠs". iSplit!.
  Qed.

End sim_spec.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.

  Context `{!dimsumGS Σ} `{!recGS Σ}.

  (* TODO, experimental *)
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

  (* REVIEW *)
  Lemma sim_echo `{!specGS} Π :
    "echo" ↪ Some echo_rec -∗
    (* FIXME: Okay, this is now a little bit awkward. :( *)
    rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_priv -∗
    rec_fn_spec_hoare Tgt Π "echo" ({{ es POST0, ⌜es = []⌝ ∗
      ∃ v,
      spec_state v ∗
      rec_fn_spec_hoare Tgt Π "putc" ({{ es POST,
          ⌜es = [Val (ValNum v)]⌝ ∗
          spec_state (v + 1) ∗
          spec_state (v + 1)
        (* POST ({{ _, *)
        (* spec_state (v + 1) ∗ *)
        (* spec_state (v + 1) *)
      }})}}).
  Proof. Admitted.

  Lemma sim_echo_full `{!specGS} Π γσ_s (σ : m_state (spec_trans _ Z)) :
    "echo" ↪ Some echo_rec -∗
    "putc" ↪ None -∗
    (* NOTE: Same here *)
    (* □ *) rec_fn_spec_hoare Tgt Π "getc" getc_fn_spec_priv -∗
    γσ_s ⤳ σ -∗
    ⌜σ.1 ≡ Spec.forever echo_getc_spec_body⌝ -∗
    rec_fn_spec_hoare Tgt Π "echo" (λ es POST,
      ⌜es = []⌝ ∗
      □ switch_external Π (λ κ σ POST,
          ∃ vs h σ_s, ⌜κ = Some (Outgoing, ERCall "putc" vs h)⌝ ∗ γσ_s ⤳ σ_s ∗
        POST (spec_trans _ Z) σ_s (λ _ Π',
          ∃ e,
        switch Π' (λ κ'' σ_s3 POST,
          ⌜κ'' = Some (Incoming, e)⌝ ∗
        POST Src _ _ (λ σ_s3' Π_s'',
          ⌜σ_s3' = σ_s3⌝ ∗
        switch Π_s'' (λ κ'' σ'' POST,
          ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ'' = None⌝ ∗
        POST Tgt _ _ (λ σ' Π',
          ⌜σ' = σ⌝ ∗ γσ_s ⤳ σ'' ∗
        switch Π' (λ κ σ POST,
          ∃ e', ⌜κ = Some (Incoming, e')⌝ ∗
        POST Tgt _ _ (λ σ' Π',
          ⌜σ' = σ⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π = Π'⌝)))))))) ∗
      POST (λ vr, ∃ σ_s, γσ_s ⤳ σ_s ∗ (∀ Π, σ_s ≈{ spec_trans rec_event Z }≈>ₛ Π))).
  Proof. Admitted.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).
  (* NOTE: Simulation statement: _ ⪯ (echo_getc_spec, v). The linked module (semantically)
    refines the spec, i.e., for any sequence of silent (module internal) steps followed by a visible
    event κ, the spec module can perform steps emitting κ. *)
  Lemma echo_getc_sim (v : Z):
    rec_state_interp (rec_init echo_prog) None -∗
    (* TODO: Not exactly sure what the list is *)
    (MLFRun None, [], rec_init echo_prog, (getc_spec_priv, v)) ⪯{m_t,
      spec_trans rec_event Z} (echo_getc_spec, v).
  Proof. Admitted.

End echo_getc.
