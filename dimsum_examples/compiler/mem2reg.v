From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import rec_heap_bij.
From dimsum.examples.compiler Require Import monad linear_rec linearize.

(** * Mem2Reg pass : LinearRec -> LinearRec *)
(** This pass optimizes local variables whose address is not taken to let bindings. *)

Module cr2a_mem2reg.

(** * pass and pass_fn *)
Inductive error := UsedAsLoc | NotSupported.

Definition M := compiler_monad unit (fn_compiler_monoid (option var_val)) error.

Definition is_var (e: var_val) (x: string) :=
  if e is (VVar y) then bool_decide (x = y) else false.

Lemma is_var_dec v x: is_var v x = bool_decide (v = VVar x).
Proof.
  rewrite /is_var. destruct v;
    rewrite !bool_decide_decide; destruct decide.
  - subst. destruct decide; naive_solver.
  - destruct decide; naive_solver.
  - naive_solver.
  - naive_solver.
Qed.


Definition lexpr_op_pass (x: string) (e: lexpr_op) : M lexpr_op :=
  match e with
  | LVarVal v =>
    cassert UsedAsLoc (v ≠ VVar x);;
    mret $ LVarVal v
  | LBinOp v1 o v2 =>
    cassert UsedAsLoc (v1 ≠ VVar x);;
    cassert UsedAsLoc (v2 ≠ VVar x);;
    mret $ LBinOp v1 o v2
  | LLoad v =>
    if is_var v x then
      mret $ LVarVal v
    else
      mret $ LLoad v
  | LStore v1 v2 =>
    cassert UsedAsLoc (v2 ≠ VVar x);;
    if is_var v1 x then
      cappend (λ _, Some v2);;
      mret $ LVarVal v2
    else mret $ LStore v1 v2
  | LCall f args =>
    cassert UsedAsLoc (f ≠ VVar x);;
    cassert UsedAsLoc (Forall (λ v, v ≠ VVar x) args);;
    mret (LCall f args)
  end.


Definition LLetM (x: string) (v: option var_val) (e: lexpr) :=
  match v with
  | None => e
  | Some w => LLetE x (LVarVal w) e
  end.

Fixpoint pass (x: string) (e : lexpr) : M lexpr :=
  match e with
  | LLetE v e1 e2 =>
    if bool_decide (v = x) then
      e1' ← lexpr_op_pass x e1;
      mret $ LLetE v e1' e2
    else
      '(e1', f) ← cscope (lexpr_op_pass x e1);
      e2' ← pass x e2;
      (* FIXME: discuss this constraint *)
      (* f None is the var_val that is assigned to x in e1'.
         if that var_val is v, then the meaning changes when
         we move the assignment to x underneath the
         assignment of v.*)
      cassert NotSupported (f None ≠ Some (VVar v));;
      mret $
        LLetE v e1' $
        LLetM x (f None) $
        e2'
  | LIf e1 e2 e3 =>
    '(e1', f) ← cscope (lexpr_op_pass x e1);
    e2' ← pass x e2;
    e3' ← pass x e3;
    mret $
      LIf e1' (LLetM x (f None) e2') (LLetM x (f None) e3')
  | LEnd e =>
    e' ← lexpr_op_pass x e;
    mret $ LEnd e'
  end.


Definition pass_single_var (x: string) (e: lexpr) (vars: list (string * Z)) :=
  let res := crun () (pass x e) in
  match list_find (λ '(y, n), bool_decide (y = x)) vars with
  | None => (e, vars)
  | Some (i, _) =>
    match res.(c_result) with
    | CSuccess e' => (LLetE x (LVarVal (VVal (StaticValNum 0))) e', delete i vars)
    | CError _ => (e, vars)
    end
  end.

Definition pass_body (e: lexpr) (vars: list (string * Z)) :=
  foldr (λ '(x, n) '(r, vars), pass_single_var x r vars) (e, vars) vars.


Definition pass_fn (f : lfndef) : lfndef :=
  let (e, vars) := pass_body f.(lfd_body) f.(lfd_vars) in
  {|
     lfd_args := f.(lfd_args);
     lfd_static_vars := f.(lfd_static_vars);
     lfd_vars := vars;
     lfd_body := e;
  |}.

Lemma pass_fn_args f :
  lfd_args (pass_fn f) = lfd_args f.
Proof. rewrite /pass_fn. by repeat case_match. Qed.

Lemma pass_fn_statics f :
  lfd_static_vars (pass_fn f) = lfd_static_vars f.
Proof. rewrite /pass_fn. by repeat case_match. Qed.

(** * Tests *)
Definition test_opt_fn (f: fndef) :=
  let s := fndef_to_static_fndef f in
  let c := cr2a_linearize.pass_fn s in
  let d := pass_fn <$> c in
  d.

Definition test_fn_1 : fndef := {|
  fd_args := ["y"];
  fd_static_vars := [("static", 42%Z)];
  fd_vars := [("x", 4%Z)];
  fd_body := (LetE "_" (Store (Var "x") (Val 1)) (Load (Var "x")));
  fd_static := I;
|}.
Lemma test_1 :
  test_opt_fn test_fn_1 =
  CSuccess
    {|
      lfd_args := ["y"];
      lfd_static_vars := [("static", 42%Z)];
      lfd_vars := [];
      lfd_body :=
        LLetE "x" (LVarVal (VVal (StaticValNum 0)))
        (LLetE "$0$" (LVarVal (VVal (StaticValNum 1)))
        (LLetE "x" (LVarVal (VVal (StaticValNum 1)))
        (LLetE "_" (LVarVal (VVar "$0$")) (LLetE "$1$" (LVarVal (VVar "x")) (LEnd (LVarVal (VVar "$1$")))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Definition test_fn_2 : fndef := {|
  fd_args := ["y"];
  fd_static_vars := [("static", 42%Z)];
  fd_vars := [("x", 4%Z); ("z", 4%Z)];
  fd_body := (LetE "_" (Store (Var "x") (Val 1))
             (LetE "_" (Store (Var "z") (Val 1))
              (BinOp (Load (Var "x")) AddOp (Var "z"))));
  fd_static := I;
|}.

Lemma test_2 :
  test_opt_fn test_fn_2 =
  CSuccess
    {|
      lfd_args := ["y"];
      lfd_static_vars := [("static", 42%Z)];
      lfd_vars := [("z", 4%Z)];
      lfd_body :=
        LLetE "x" (LVarVal (VVal (StaticValNum 0)))
        (LLetE "$0$" (LVarVal (VVal (StaticValNum 1)))
        (LLetE "x" (LVarVal (VVal (StaticValNum 1)))
        (LLetE "_" (LVarVal (VVar "$0$"))
        (LLetE "$1$" (LStore (VVar "z") (VVal (StaticValNum 1)))
        (LLetE "_" (LVarVal (VVar "$1$"))
        (LLetE "$2$" (LVarVal (VVar "x"))
        (LLetE "$3$" (LBinOp (VVar "$2$") AddOp (VVar "z")) (LEnd (LVarVal (VVar "$3$"))))))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.


(* TODO: this is kind of a corner case, since the expression has UB, which results in *)
Definition test_fn_3 : fndef := {|
  fd_args := ["y"];
  fd_static_vars := [("static", 42%Z)];
  fd_vars := [("x", 4%Z)];
  fd_body := (BinOp (BinOp (Var "y") OffsetOp (Val 2)) AddOp (Call (Val (ValFn "f")) [Load (Var "x"); Val 1]));
  fd_static := I;
|}.

Lemma test_3 :
  test_opt_fn test_fn_3 =
  CSuccess
    {|
      lfd_args := ["y"];
      lfd_static_vars := [("static", 42%Z)];
      lfd_vars := [];
      lfd_body :=
        LLetE "x" (LVarVal (VVal (StaticValNum 0)))
          (LLetE "$0$" (LBinOp (VVar "y") OffsetOp (VVal (StaticValNum 2)))
             (LLetE "$1$" (LVarVal (VVar "x"))
                (LLetE "$2$" (LCall (VVal (StaticValFn "f")) [VVar "$1$"; VVal (StaticValNum 1)])
                   (LLetE "$3$" (LBinOp (VVar "$0$") AddOp (VVar "$2$")) (LEnd (LVarVal (VVar "$3$")))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

Definition test_fn_4 : fndef := {|
  fd_args := ["x"];
  fd_static_vars := [("static", 42%Z)];
  fd_vars := [("y", 1%Z)];
  fd_body := (LetE "_" (Store (Var "y") (Var "x"))
             ((BinOp (Load (Var "y")) AddOp (Load (Var "y")))));
  fd_static := I;
|}.

Lemma test_4 :
  test_opt_fn test_fn_4 =
  CSuccess
    {|
      lfd_args := ["x"];
      lfd_static_vars := [("static", 42%Z)];
      lfd_vars := [];
      lfd_body :=
        LLetE "y" (LVarVal (VVal (StaticValNum 0)))
        (LLetE "$0$" (LVarVal (VVar "x"))
        (LLetE "y" (LVarVal (VVar "x"))
        (LLetE "_" (LVarVal (VVar "$0$"))
        (LLetE "$1$" (LVarVal (VVar "y"))
        (LLetE "$2$" (LVarVal (VVar "y"))
        (LLetE "$3$" (LBinOp (VVar "$1$") AddOp (VVar "$2$")) (LEnd (LVarVal (VVar "$3$")))))))))
    |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

(** * Verification of pass and pass_fn *)
Lemma lexpr_tsim_var_val  v es ei Ks Ki vss vsi x n hi hs fns1 fns2 rf r
  `{Hfill1: !RecExprFill es Ks (subst_map vss (var_val_to_expr v))}
  `{Hfill2: !RecExprFill ei Ki (subst_map vsi (var_val_to_expr v))}:
    dom vss ⊆ dom vsi →
    v ≠ VVar x →
    satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ r) →
    (∀ v' w',
      subst_map vsi (var_val_to_expr v) = Val v' →
      subst_map vss (var_val_to_expr v) = Val w' →
      satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ val_in_bij v' w' ∗ r) →
      Rec (expr_fill Ki (Val v')) hi fns1
        ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
      (SMProg, Rec (expr_fill Ks (Val w')) hs fns2, (PPInside, (), rf))
    ) →
    Rec ei hi fns1
      ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
    (SMProg, Rec es hs fns2, (PPInside, (), rf)).
Proof.
 intros Hdom Hne Hsat Hcont; destruct Hfill1 as [->], Hfill2 as [->].
 destruct v as [y|w]; simpl.
 - destruct (vss !! y) eqn: Hlook; last first.
   { tstep_s. done. }
   eapply elem_of_dom_2 in Hlook as Hel.
   eapply elem_of_weaken in Hel; last done.
   eapply elem_of_dom in Hel as [w Hlook'].
   rewrite Hlook'. eapply Hcont; simpl.
   { rewrite Hlook' //. }
   { rewrite Hlook //. }
   iSatMono. iIntros "[#Hv $]". iFrame "Hv".
   iApply (big_sepM2_lookup with "Hv");
    rewrite !lookup_delete_ne //; naive_solver.
  - eapply Hcont; [done..|].
    iSatMono. iIntros "[#Hv $]". iFrame "Hv".
    destruct w; done.
Qed.


Lemma lexpr_tsim_var_val_call vs' ws' ys es ei Ks Ki vss vsi x n hi hs fns1 fns2 rf fi fs r
  `{Hfill2: !RecExprFill ei Ki (Call (Val fi) ((Val <$> vs') ++ (subst_map vsi <$> (var_val_to_expr <$> ys))))}
  `{Hfill1: !RecExprFill es Ks (Call (Val fs) ((Val <$> ws') ++ (subst_map vss <$> (var_val_to_expr <$> ys))))}:
    dom vss ⊆ dom vsi →
    Forall (λ v, v ≠ VVar x) ys →
    satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs'; ws', val_in_bij v w) ∗ r) →
    (∀ vs ws,
      satisfiable (([∗ map] vi;vs ∈ (delete x vsi); (delete x vss), val_in_bij vi vs) ∗ ([∗ list] v; w ∈ vs' ++ vs; ws' ++ ws, val_in_bij v w) ∗ r) →
      Rec (expr_fill Ki (Call (Val fi) (Val <$> (vs' ++ vs)))) hi fns1
        ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
      (SMProg, Rec (expr_fill Ks (Call (Val fs) (Val <$> (ws' ++ ws)))) hs fns2, (PPInside, (), rf))
    ) →
    Rec ei hi fns1
      ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
    (SMProg, Rec es hs fns2, (PPInside, (), rf)).
Proof.
 intros Hdom Hall Hsat Hcont;destruct Hfill1 as [->], Hfill2 as [->].
 induction ys as [|y ys IH] in vs', ws', Hsat, Hall, Hcont |-*; simpl.
 - specialize (Hcont [] []). rewrite !app_nil_r in Hcont.
   rewrite !app_nil_r. eapply Hcont, Hsat.
 - eapply Forall_cons_1 in Hall as [Hne Hall]. eapply lexpr_tsim_var_val; eauto.
   { eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end. }
   { eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end. }
   clear Hsat; intros v w _ _ Hsat; simpl.
   rewrite !cons_middle !app_assoc. change ([Val v]) with (Val <$> [v]).
   change ([Val w]) with (Val <$> [w]). rewrite -!fmap_app.
   eapply IH.
   + done.
   + iSatMono. by iIntros "($ & $ & $ & $)".
   + clear Hsat. intros vs ws Hsat.
      rewrite -!app_assoc. eapply Hcont.
      rewrite !app_assoc //.
Qed.

Local Hint Resolve rec_heap_bij_call_mono : core.
Local Hint Resolve rec_heap_bij_return_mono : core.


Lemma pass_lexpr_op_correct ei' Ki ei Ks es es' x k (l: loc) n hi hs fns1 fns2 INV vsi vss wi ws r rf (f: option var_val → option var_val)
  `{Hfill1: !RecExprFill es Ks (subst_map vss (lexpr_op_to_expr es'))}
  `{Hfill2: !RecExprFill ei Ki (subst_map vsi (lexpr_op_to_expr ei'))}:
    rec_heap_bij_call n fns1 fns2 INV →
    (∀ (w1 w2: val),
       default (Val wi) (subst_map vsi <$> (var_val_to_expr <$> (f None))) = Val w1 →
      rec_heap_bij_return n fns1 fns2 Ki Ks
        (r ∗ heap_bij_const_s l.1 (<[0%Z := w2]> (zero_block k)) ∗ val_in_bij w1 w2) INV) →
    satisfiable (([∗ map] v1;v2 ∈ (delete x vsi);(delete x vss), val_in_bij v1 v2) ∗
                   heap_bij_inv hi hs ∗ val_in_bij wi ws ∗
                   heap_bij_const_s l.1 (<[0%Z := ws]> (zero_block k)) ∗
                   INV ∗ r ∗ rf) →
    vss !! x = Some (ValLoc l) →
    vsi !! x = Some wi →
    dom vss ⊆ dom vsi →
    l.2 = 0 →
    crun () (lexpr_op_pass x es') = CResult () f (CSuccess ei') →
    Rec ei hi fns1
      ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
    (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  intros Hcalls Hcont Hsat Hxs Hxi Hsub Hl Hrun.
  destruct Hfill1 as [->], Hfill2 as [->].
  destruct es' as [v|v1 op v2|v|v1 v2|y vs]; simpl in Hrun.
  - simplify_crun_eq.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v1 v2 _ _ Hsat; simpl.
    eapply Hcont; [done..|].
    iSatMono. iIntros "(_ & $ & $ & $ & $ & $ & $ & $)".
  - simplify_crun_eq.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v1' w1' _ _ Hsat; simpl.
    apply: lexpr_tsim_var_val; eauto; clear Hsat.
    intros v2' w2' _ _ Hsat; simpl.
    tstep_s. intros w' Heval.
    iSatStart. iIntros "(Hvals & H1 & H2 & Hbij & Hval & Hl & Hs & r & rf)".
    iDestruct (eval_binop_bij with "H2 H1") as "[%v' [%Heval2 Hw]]"; first done.
    iSatStop. tstep_i. split!.
    eapply Hcont; [done..|].
    iSatMono. iFrame.
  - simplify_crun_eq.
    rewrite is_var_dec bool_decide_decide in Hrun.
    destruct decide; simplify_crun_eq.
    + simpl. rewrite Hxs Hxi.
      tstep_s. intros ??; injection 1 as <-; intros Heq.
      eapply Hcont; [done..|].
      iSatMono.
      iIntros "(Hvals & Hbij & #Hval & Hl & Hs & $ & $)".
      iDestruct (heap_bij_inv_lookup_s with "Hbij Hl") as "%Heq'".
      rewrite Heq in Heq'. rewrite Hl in Heq'.
      rewrite lookup_insert in Heq'. simplify_eq. iFrame.
      iFrame "Hval".
    + apply: lexpr_tsim_var_val; eauto; clear Hsat.
      intros v1 v2 _ _ Hsat; simpl.
      tstep_s. intros l' v' -> Hlook'.
      iSatStart. iIntros "(Hvals & Hbij & Hinv & Hval & Hl & Hs & r & rf)".
      destruct v1 as [| |l''|]; simpl; try done.
      iDestruct (heap_bij_inv_lookup with "Hinv Hbij") as "[%w [%Heq' #Hval']]"; first done.
      iSatStop. tstep_i. split!. eapply Hcont; [done..|].
      iSatMono. iFrame. done.
  - rewrite !is_var_dec !bool_decide_decide in Hrun.
    destruct decide; simplify_crun_eq.
    + rewrite Hxs. apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros w1 w2 ? ? Hsat; simpl.
      tstep_s. intros l' Heq Halive; injection Heq as <-.
      eapply Hcont; [done..|].
      iSatMonoBupd. iIntros "(Hvals & #Hbij & Hinv & #Hval & Hl & Hs & r & rf)".
      iMod (heap_bij_inv_update_s with "Hinv Hl") as "[Hinv Hl]".
      iFrame "∗#". iModIntro.
      have -> : h_block (heap_update hs l w2) l.1 = <[0%Z:=w2]> (zero_block k); [|done].
      rewrite h_block_heap_update Hl. apply map_eq => i.
      iSatStart. iIntros "(? & ? & Hinv & ? & Hl & ?)"; simpl.
      iDestruct (heap_bij_inv_lookup_s (l.1, i) with "Hinv Hl") as %Hi.
      iSatStop. iSatClear.
      destruct (decide (i = 0%Z)); simplify_map_eq; by rewrite h_block_lookup Hi.
    + apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros w1 w2 _ _ Hsat; simpl.
      apply: (lexpr_tsim_var_val); eauto; clear Hsat.
      intros u1 u2 _ _ Hsat; simpl.
      tstep_s. intros l' Heq Halive; subst w2.
      iSatStart. iIntros "(Hvals & #Hu & Hw & Hinv & Hval & Hl & Hs & r & rf)".
      destruct w1 as [| |l''|]; simpl; try done.
      iDestruct (heap_bij_inv_alive with "Hinv Hw") as "%"; first done.
      iDestruct (heap_bij_inv_update with "Hinv Hw Hu") as "Hheap".
      iSatStop. tstep_i. split!. eapply Hcont; [done..|].
      iSatMono. iFrame. done.
  - simplify_crun_eq.
    apply: (lexpr_tsim_var_val); eauto; clear Hsat.
    intros w1 w2 _ _ Hsat; simpl.
    apply: (lexpr_tsim_var_val_call nil nil); eauto.
    { iSatMono. iIntros "[$ H]". simpl. iSplit; first done. iExact "H". }
    simpl. clear Hsat. intros vs' ws' Hsat.
    tstep_s => f ?. simplify_eq/=.
    iSatStart. iIntros!. destruct w1; iDestruct!. iSatStop.
    apply: Hcalls; eauto.
    { by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall. }
    { by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall. }
    { iSatMono. iFrame. iAccu. }
    iSatClear. intros v1'' v2'' h1'' h2'' rf'' Hsat; simpl.
    eapply Hcont; [done..|].
    iSatMono. iIntros!. iFrame.
Qed.




Lemma LLetM_sim Ki Ks vsi vss x o ei es n hi hs fns1 fns2 rf vi wi:
  vsi !! x = Some vi →
  default (Val vi) (subst_map vsi <$> (var_val_to_expr <$> o)) = Val wi →
  Rec (expr_fill Ki (subst_map (<[x := wi]> vsi) (lexpr_to_expr ei))) hi fns1
    ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
  (SMProg, Rec (expr_fill Ks (subst_map vss (lexpr_to_expr es))) hs fns2, (PPInside, (), rf)) →
  Rec (expr_fill Ki (subst_map vsi (lexpr_to_expr (LLetM x o ei)))) hi fns1
    ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
  (SMProg, Rec (expr_fill Ks (subst_map vss (lexpr_to_expr es))) hs fns2, (PPInside, (), rf)).
Proof.
  destruct o; simpl.
  - intros Hlook Heq Hsim; rewrite Heq.
    tstep_i. rewrite -subst_subst_map_delete.
    eapply Hsim.
  - intros Hlook. injection 1 as ->.
    rewrite insert_id //.
Qed.

Lemma pass_correct  r rf ei' Ki ei Ks es es' x (l: loc) n k h h' fns1 fns2 INV vsi vss vi vs r_p
  `{Hfill1: !RecExprFill es Ks (subst_map vss (lexpr_to_expr es'))}
  `{Hfill2: !RecExprFill ei Ki (subst_map vsi (lexpr_to_expr ei'))}:
    l.2 = 0 →
    rec_heap_bij_call n fns1 fns2 INV →
    (∀ w, rec_heap_bij_return n fns1 fns2 Ki Ks (r ∗ heap_bij_const_s l.1 (<[0%Z := w]> (zero_block k))) INV) →
    vss !! x = Some (ValLoc l) →
    vsi !! x = Some vi →
    dom vss ⊆ dom vsi →
    satisfiable (heap_bij_inv h h' ∗ heap_bij_const_s l.1 (<[0%Z := vs]> (zero_block k)) ∗
                val_in_bij vi vs ∗ ([∗ map] v1;v2 ∈ (delete x vsi);(delete x vss), val_in_bij v1 v2) ∗
                INV ∗ r ∗ rf) →
    crun () (pass x es') = CResult () r_p (CSuccess ei') →
    Rec ei h fns1
      ⪯{rec_trans, rec_heap_bij_trans rec_trans, n, true}
    (SMProg, Rec es h' fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  intros Hl; destruct Hfill1 as [->]. destruct Hfill2 as [->].
  revert r rf ei' Ki Ks x n k h h' fns1 fns2 vsi vss vi vs r_p.
  induction es' as [y op es' IH| op es1' IH1 es2' IH2 | op];
    intros r rf ei' Ki Ks x n k h h' fns1 fns2 vsi vss vi vs r_p;
    intros Hcall Hcont Hvss Hvsi Hdom Hsat Hrun; simpl in Hrun.
  - rewrite bool_decide_decide in Hrun.
    destruct decide; simplify_crun_eq.
    + apply: pass_lexpr_op_correct; eauto; last first.
      { iSatMono. iIntros "($ & $ & $ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
      simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
      simpl. tstep_s. tstep_i.
      rewrite -!subst_subst_map_delete.
      apply: rec_heap_bij_sim_refl_static; simpl; eauto.
      { set_solver. }
      { eapply lexpr_is_static. }
      iSatMono. iIntros!. iFrame.
      rewrite big_sepM2_insert_delete. iFrame.
    + (* FIXME: the next step should be automatic *)
      destruct x0, x2.
      simplify_crun_eq.

      apply: pass_lexpr_op_correct; eauto; last first.
      { iSatMono. iIntros "($ & $ & $ & #H & $ & r & $)". iFrame "H". iCombine "H r" as "r". iExact "r". }
      simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
      simpl. tstep_s. tstep_i.
      rewrite -!subst_subst_map_delete.
      eapply LLetM_sim.
      { rewrite lookup_insert_ne //. }
      { destruct o; last done.
        rewrite -Hdef /=. simpl in Hdef.
        destruct v as [z|]; last done; simpl.
        destruct (decide (z = y)); subst; first naive_solver.
        rewrite lookup_insert_ne //. }
      eapply IH; eauto using rec_heap_bij_call_mono; first last.
      { iSatMono. iIntros "(? & Hv & ?)". iDestruct!. iFrame.
        rewrite delete_insert_delete. rewrite !delete_insert_ne //.
        iApply (big_sepM2_insert_2 with "[Hv] [$]"); simpl.
        iFrame. }
      { set_solver. }
      { rewrite lookup_insert //. }
      { rewrite lookup_insert_ne //. }
  - simplify_crun_eq.
    (* FIXME: the next step should be automatic *)
    destruct x0, x2.
    simplify_crun_eq.
    destruct x0.

    apply: pass_lexpr_op_correct; eauto; last first.
    { iSatMono. iIntros "($ & $ & $ & #H & $ & r & $)". iFrame "H". iCombine "H r" as "r". iExact "r". }
    simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
    simpl. tstep_s. intros bb ->.
    assert (v1 = ValBool bb) as ->.
    { iSatStart. iIntros "(? & Hval & ? & ?)". destruct v1; eauto.
      iDestruct "Hval" as "%". subst. iSatStop. done. }
    tstep_i.
    destruct bb; eapply LLetM_sim; eauto.
    + eapply IH1; eauto using rec_heap_bij_call_mono; first last.
      { iSatMono. iIntros!. iFrame.
        rewrite delete_insert_delete. iFrame. }
      { set_solver. }
      { rewrite lookup_insert //. }
    + eapply IH2; eauto using rec_heap_bij_call_mono; first last.
      { iSatMono. iIntros!. iFrame.
        rewrite delete_insert_delete. iFrame. }
      { set_solver. }
      { rewrite lookup_insert //. }
  - simplify_crun_eq.
    apply: pass_lexpr_op_correct; eauto; last first.
    { iSatMono. iIntros "($ & $ & $ & $ & r & $)". iExact "r". }
    simpl. clear Hsat. intros w1 w2 Hdef. intros n' v1 v2 h1' h2' rf' b Hsub Hsat.
    simpl. eapply Hcont; eauto.
    iSatMono. iIntros!. iFrame.
Qed.

Lemma pass_lookup_singleton (f g: string) fn fn':
  (lfndef_to_fndef <$> <[f:=fn]> ∅: gmap string fndef) !! g = Some fn' →
  fn' = lfndef_to_fndef fn ∧ f = g.
Proof.
  rewrite !lookup_fmap.
  intros [x [Hlook ->]]%fmap_Some_1.
  eapply lookup_insert_Some in Hlook as [[-> <-]|[? ?]]; last set_solver.
  done.
Qed.


Lemma heap_alloc_list_app vs1 vs2 ls h1 h2:
  heap_alloc_list (vs1 ++ vs2) ls h1 h2 →
  ∃ h ls1 ls2,
    ls = ls1 ++ ls2 ∧
    length ls1 = length vs1 ∧
    heap_alloc_list vs1 ls1 h1 h ∧
    heap_alloc_list vs2 ls2 h h2.
Proof.
  induction vs1 as [|v vs1 IH] in ls, h1, h2 |-*; simpl.
  - intros ?. eexists _, nil, _. split; done.
  - simpl; intros (l' & ls' & Heq & Hfresh & Halloc). subst.
    eapply IH in Halloc as (h & ls1 & ls2 & -> & Hlen & Halloc1 & Halloc2).
    eexists _, (_ :: _), _. split_and!; eauto.
    simpl; by rewrite Hlen.
Qed.


Lemma heap_bij_alloc_elim vs l ls li i h1 h2 n h h':
  ls !! i = Some l →
  vs !! i = Some n →
  heap_alloc_list (delete i vs) li h1 h' →
  heap_alloc_list vs ls h2 h →
  heap_bij_inv h1 h2 ⊢ |==>
    heap_bij_inv h' h ∗
    heap_bij_const_s l.1 (zero_block n) ∗
    [∗ list] li; ls ∈ li; (delete i ls), loc_in_bij li ls.
Proof.
  intros Hlook1 Hlook2.
  rewrite delete_take_drop.
  eapply take_drop_middle in Hlook2 as Hsplit2; symmetry in Hsplit2.
  rewrite {3}Hsplit2.
  intros (h1' & li1 & li2 & -> & Hlen1 & H1i & H2i)%heap_alloc_list_app.
  intros (h2' & ls1 & ls2 & -> & Hlen2 & H1s & H2s)%heap_alloc_list_app.
  destruct H2s as (l' & ls2' & -> & Hfresh & H2s).
  assert (i = length ls1) as Hi.
  { rewrite Hlen2. symmetry. eapply length_take_le. eapply lookup_lt_Some in Hlook2. lia. }
  rewrite list_lookup_middle // in Hlook1.
  injection Hlook1 as ?; subst.
  rewrite delete_middle.

  iIntros "Hbij".
  iMod (heap_bij_inv_alloc_list with "Hbij") as "[Hbij Hbl]"; [done..|].
  iMod (heap_bij_inv_alloc_s with "Hbij") as "[Hbij Hconst]"; first done.
  iMod (heap_bij_inv_alloc_list with "Hbij") as "[Hbij Hbl']"; [done..|].
  rewrite h_block_heap_alloc //. iFrame "Hconst Hbij".
  iApply (big_sepL2_app with "Hbl Hbl'").
Qed.




Lemma heap_bij_free_elim lis lss hi hs hs' w l k i:
  heap_free_list lss hs hs' →
  lss !! i = Some (l, k) →
  lis.*2 = (delete i lss.*2) →
    heap_bij_inv hi hs -∗
    heap_bij_const_s l.1 (<[0%Z:=w]> (zero_block k)) -∗
    ([∗ list] li;ls ∈ lis.*1;(delete i lss.*1), loc_in_bij li ls) ==∗
      ∃ hi' : heap_state, ⌜heap_free_list lis hi hi'⌝ ∗
        heap_bij_inv hi' hs'.
Proof.
  induction lss as [|[l' k'] lss IH] in i, lis, hi, hs, hs' |-*; first by naive_solver.
  destruct i; simpl.
  - intros [Hb [Hr Hfree]] ? Heq. simplify_eq. simpl in *.
    iIntros "Hbij Hl Hlocs".
    iMod (heap_bij_inv_free_s with "Hbij Hl") as "Hbij"; [done|].
    iDestruct (heap_bij_inv_free_list with "Hbij Hlocs") as "?"; eauto.
  - intros [Hb [Hr Hfree]] ? Heq. destruct lis as [|[l'' k''] lis]; first naive_solver.
    simpl in Heq. simplify_eq. simpl.
    iIntros "Hbij Hl [Hl' Hlocs]".
    iDestruct (loc_in_bij_same_prov_kind with "Hl'") as "%Hkind".
    iDestruct (heap_bij_inv_range with "Hbij Hl'") as "%"; first done.
    iDestruct (heap_bij_inv_free with "Hbij Hl'") as "Hbij"; first done.
    iMod (IH with "Hbij Hl Hlocs") as "[%hi' [% Hbij]]"; eauto.
    iExists _. iFrame. iModIntro. iSplit!. by erewrite same_prov_kind_is_ProvBlock_iff.
Qed.

Lemma pass_correct_refines f x args static_vars vars exprs i k cont expri:
  vars !! i = Some (x, k) →
  (NoDup (args ++ static_vars.*1 ++ (vars.*1))) →
  crun () (pass x exprs) = CResult () cont (CSuccess expri) →
  trefines
    (linear_rec_mod (<[f:={|
                    lfd_args := args;
                    lfd_static_vars := static_vars;
                    lfd_vars := delete i vars;
                    lfd_body := LLetE x (LVarVal (VVal (StaticValNum 0))) expri
                  |}]> ∅))
    (let fns := (<[f:={| lfd_args := args; lfd_static_vars := static_vars; lfd_vars := vars; lfd_body := exprs |}]> ∅) in
      rec_heap_bij (fd_init_heap f static_vars) (linear_rec_mod fns)).
Proof.
  intros Heq Hnodup Hrun.
  pose (INV := ([∗ list] l ∈ static_locs f static_vars, loc_in_bij l l)%I).
  apply: (rec_heap_bij_proof INV).
  - set_solver.
  - move => ??. intros [-> ->]%pass_lookup_singleton.
    eexists. split; simpl.
    { rewrite lookup_fmap. eapply fmap_Some_2, lookup_insert.  }
    { done. }
  - iIntros. iApply (heap_bij_inv_share_init with "[$] [$]").
  - intros n K1 K2 g fn1 fn2 vs1 vs2 h1 h2 r rf.
    intros [-> <-]%pass_lookup_singleton.
    intros [-> _]%pass_lookup_singleton.
    rewrite /= !fmap_insert !fmap_empty /=.
    intros Hlen1 Hlen2 Hsat Hcalls Hcont.

    (* we allocate the stack variables *)
    tstep_both. intros li h' Halloc. tstep_s.
    edestruct (heap_alloc_list_fresh vars.*2 ∅ h2) as [h Heap].
    eexists _, _. split; first done. intros Hall. tend. split.
    { by eapply Forall_fmap, Forall_delete, Forall_fmap. }

    (* side condition we need later *)
    pose (ls := (heap_fresh_list vars.*2 ∅ h2)).
    assert (length vars.*2 = length ls) as Hlen.
    { subst ls. clear. unfold fmap. generalize (∅: (gset prov)). generalize h2.
      induction vars as [|[]? IH]; simpl; first done.
      intros ??. by erewrite IH. }

    (* we clean up the substitutions *)
    rewrite /subst_static !subst_l_subst_map; first last.
    { eapply heap_alloc_list_length in Halloc.
      revert Halloc. rewrite !length_fmap //.  }
    { by rewrite ?length_fmap ?length_imap. }
    { done. }
    { rewrite !length_fmap -Hlen !length_fmap //. }
    { by rewrite ?length_fmap ?length_imap. }
    { done. }
    rewrite -!subst_map_subst_map.
    rewrite -!list_to_map_app /=.

    (* we bind the pruned location in the target *)
    tstep_i.
    (* we clean up the substitutions *)
    rewrite -subst_subst_map_delete.

    destruct (ls !! i) as [l|] eqn: Hl; last first.
    { eapply lookup_lt_Some in Heq.
      rewrite length_fmap in Hlen.
      rewrite Hlen in Heq.
      eapply lookup_lt_is_Some_2 in Heq as [].
      naive_solver. }

    eapply heap_alloc_list_length in Halloc as Hlen3.
    eapply heap_alloc_list_length in Heap as Hlen4.
    assert (vars.*1 !! i = Some x) as Hvars1.
    { rewrite list_lookup_fmap Heq //. }
    assert (vars.*2 !! i = Some k) as Hvars2.
    { rewrite list_lookup_fmap Heq //. }

    eapply (pass_correct (r ∗ [∗ list] l1;l2 ∈ li;delete i ls, loc_in_bij l1 l2) _ _ _ _ _ _ _ _ l _ k _ _ _ _ _ _ _ 0%Z); last done.
    + eapply rec_expr_fill_expr_fill, rec_expr_fill_FreeA, rec_expr_fill_end.
    + eapply rec_expr_fill_expr_fill, rec_expr_fill_FreeA, rec_expr_fill_end.
    + by eapply heap_alloc_list_offset_zero.
    + done.
    + iSatClear. simpl. intros w n' v1 v2 h1' h2' rf' b Hle Hsat. simpl.
      tstep_s. intros h2'' Hfree. tstep_i.
      iSatStartBupd. iIntros "(Hbij & Hv & HINV & [[r Hlocs] Hloc] & Hl)".
      rewrite list_fmap_delete in Hlen3.
      iPoseProof ((heap_bij_free_elim (zip li (delete i vars.*2))) with "Hbij") as "Hw".
      { done. }
      { eapply lookup_zip_with_Some. naive_solver. }
      { rewrite ?snd_zip //; lia. }
      rewrite ?fst_zip; [|lia..].
      iSpecialize ("Hw" with "Hloc Hlocs").
      iMod "Hw" as "(%hi' & %Hfree' & Hbij)". iModIntro.
      iSatStop. eexists _; split.
      { rewrite list_fmap_delete //. }
      eapply Hcont; first done.
      iSatMono. iFrame.
    + eapply elem_of_list_to_map_1.
      { rewrite !fmap_app !fst_zip ?Hlen2 ?length_fmap -?Hlen4 ?length_imap ?length_fmap //. }
      do 2 (eapply elem_of_app; right). eapply (elem_of_list_lookup_2 _ i).
      eapply lookup_zip_with_Some. split!.
      { rewrite list_lookup_fmap Hl //. }
    + rewrite lookup_insert //.
    + rewrite dom_insert_L !dom_list_to_map_L.
      rewrite !fmap_app !list_to_set_app.
      rewrite !fst_zip ?Hlen2 ?length_fmap ?Hlen1 -?Hlen4 -?Hlen3 ?length_imap ?length_fmap //.
      rewrite list_fmap_delete.
      rewrite {1}(delete_Permutation vars.*1); last done.
      simpl. clear. set_solver.
    + erewrite (zero_block_insert_zero k); last first.
      { eapply Forall_lookup_1 in Hall; eauto. lia. }
      iSatMonoBupd. iIntros "(Hbij & Hvals & #Hs & r & rf)".
      iFrame "rf r".
      iMod (heap_bij_alloc_elim with "Hbij") as "(Hbij & Hconst & #Hlocs)"; eauto.
      { rewrite -list_fmap_delete //. }
      iFrame "Hbij Hconst Hlocs Hs".
      rewrite delete_insert_delete.
      iModIntro. iSplit; first done.

      rewrite length_fmap in Hlen3.
      assert (x ∉ args) as Hx.
      { eapply NoDup_app in Hnodup as (_ & Hnd & _).
        intros ?. eapply Hnd; first done.
        apply elem_of_app; right.
        by eapply elem_of_list_lookup_2. }
      fold ls. clear -Hx Heq Hlen Hlen1 Hlen2. revert Hlen.
      generalize ls. clear ls; intros ls. rewrite length_fmap. intros Hlen.

      rewrite !list_to_map_app !delete_union.
      rewrite !(delete_notin (list_to_map (zip args _))).
      2,3: apply not_elem_of_list_to_map; rewrite fst_zip //; lia.
      iDestruct "Hvals" as "#Hvals".
      repeat iApply big_sepM2_union.
      * iApply big_sepM2_list_to_map_2; [rewrite !fst_zip //; lia|].
        rewrite !snd_zip //; lia.
      * iApply big_sepM2_delete_2. iApply big_sepM2_list_to_map_2 => //=.
        rewrite !snd_zip ?length_fmap ?static_provs_length //.
        iApply big_sepL_sepL2_diag. by iApply big_sepL_fmap => /=.
      * rewrite !list_fmap_delete. iClear "Hs Hvals".
        iDestruct "Hlocs" as "-#Hlocs".
        iInduction vars as [|v vars] "IH" forall (i ls li Hlen Heq); csimpl => //.
        destruct ls => //; simplify_eq/=. destruct i; simplify_eq/=.
        -- rewrite delete_insert_delete. iApply big_sepM2_delete_2.
           iDestruct (big_sepL2_length with "Hlocs") as %?.
           iApply big_sepM2_list_to_map_2; [rewrite !fst_zip ?length_fmap //; lia|].
           rewrite !snd_zip ?length_fmap //; [|lia..].
           by rewrite big_sepL2_fmap_l big_sepL2_fmap_r.
        -- iDestruct (big_sepL2_cons_inv_r with "Hlocs") as (???) "[Hloc ?]".
           simplify_eq/=. destruct (decide (x = v.1)); simplify_eq.
           ++ rewrite !delete_insert_delete. iApply ("IH" with "[//] [//] [$]").
           ++ rewrite !delete_insert_ne//.
              iApply (big_sepM2_insert_2 with "[Hloc]"); [done|].
              iApply ("IH" with "[//] [//] [$]").
Qed.



Lemma pass_single_var_correct f x args static_vars exprs varss expri varsi :
  (NoDup (args ++ static_vars.*1 ++ (varss.*1))) →
  pass_single_var x exprs varss = (expri, varsi) →
  trefines
  (linear_rec_mod (<[f:={| lfd_args := args; lfd_static_vars := static_vars; lfd_vars := varsi; lfd_body := expri |}]> ∅))
  (let fns := (<[f:={| lfd_args := args; lfd_static_vars := static_vars; lfd_vars := varss; lfd_body := exprs |}]> ∅) in
    rec_heap_bij (fds_init_heap (fd_static_vars <$> (lfndef_to_fndef <$> fns))) (linear_rec_mod fns)).
Proof.
  intros Hnd. rewrite /pass_single_var.
  destruct list_find as [[i [y n]]|] eqn: Hfind;
    first destruct (crun () (pass x exprs)) as [[] ? [res|]] eqn: Hrun; simpl;
    last first.
  - injection 1 as ??; subst. eapply rec_heap_bij_refl.
  - injection 1 as ??; subst. eapply rec_heap_bij_refl.
  - injection 1 as ??; subst.
    eapply list_find_Some in Hfind as (Hlook & Hdec & _).
    eapply bool_decide_unpack in Hdec. subst.
    rewrite !fmap_insert fmap_empty fds_init_heap_insert //= fds_init_heap_empty right_id_L.
    by eapply pass_correct_refines.
Qed.



Lemma pass_single_vars x es ei varss varsi:
  pass_single_var x es varss = (ei, varsi) →
  varsi ⊆ varss.
Proof.
  rewrite /pass_single_var.
  destruct list_find as [[p i]|]; first destruct c_result;
    intros ?; simplify_eq; try done.
    pose proof (submseteq_delete varss p).
    intros ??. by eapply elem_of_submseteq.
Qed.


Lemma pass_single_nodup x es ei varss varsi:
  NoDup varss.*1 →
  pass_single_var x es varss = (ei, varsi) →
  NoDup varsi.*1.
Proof.
  rewrite /pass_single_var.
  destruct list_find as [[p i]|]; first destruct c_result;
    intros Hnd ?; simplify_eq; try done.
    rewrite list_fmap_delete.
    by eapply NoDup_delete.
Qed.


Lemma foldr_pass_single_vars exprs varss expri varsi (L : list (string * Z)):
  foldr (λ '(x, _) '(r, vars), pass_single_var x r vars) (exprs, varss) L = (expri, varsi) →
  varsi ⊆ varss.
Proof.
  induction L as [|[x ?] L IH] in exprs, varss, expri, varsi |-*; simpl.
  - injection 1 as ??; by subst.
  - destruct foldr as [exprs' varss'] eqn: Heq.
    eapply IH in Heq. intros ?%pass_single_vars.
    set_solver.
Qed.

Lemma foldr_pass_single_nodup exprs varss expri varsi (L : list (string * Z)):
  NoDup varss.*1 →
  foldr (λ '(x, _) '(r, vars), pass_single_var x r vars) (exprs, varss) L = (expri, varsi) →
  NoDup varsi.*1.
Proof.
  induction L as [|[x ?] L IH] in exprs, varss, expri, varsi |-*; simpl.
  - intros ?. injection 1 as ??; by subst.
  - destruct foldr as [exprs' varss'] eqn: Heq.
    intros Hnd.
    eapply IH in Heq; last done.
    intros ?%pass_single_nodup; done.
Qed.



Lemma pass_body_correct f args static_vars varss exprs expri varsi :
  pass_body exprs varss = (expri, varsi) →
  NoDup (args ++ static_vars.*1 ++ varss.*1) →
  trefines
    (linear_rec_mod (<[f:={| lfd_args := args; lfd_static_vars := static_vars; lfd_vars := varsi; lfd_body := expri |}]> ∅))
    (let fns := (<[f:={| lfd_args := args; lfd_static_vars := static_vars; lfd_vars := varss; lfd_body := exprs |}]> ∅) in
     rec_heap_bij_N (length varss) (fd_init_heap f static_vars) (linear_rec_mod fns)).
Proof.
  rewrite /pass_body. remember varss as L. rewrite {1 3 5}HeqL. clear HeqL.
  induction L as [|[x n] L IH] in varss, varsi, exprs, expri |-*; simpl.
  - injection 1 as ??. subst; reflexivity.
  - destruct foldr as [expri' varsi'] eqn: Hbody.
    eapply foldr_pass_single_vars in Hbody as Hsub.
    intros Hsingle Hnd.
    eapply IH in Hbody as Hx; last done.
    eapply rec_heap_bij_trefines in Hx; last apply rec_vis_no_all.
    eapply pass_single_var_correct in Hsingle; last first.
    + rewrite app_assoc. rewrite app_assoc in Hnd.
      eapply NoDup_app. eapply NoDup_app in Hnd as [Hnd [Hinter Hvarss]].
      split; first apply Hnd. split.
      { set_solver. }
      { by eapply foldr_pass_single_nodup. }
    + simpl in *. etrans; [apply Hsingle|]. etrans; [apply Hx|].
      rewrite !fmap_insert fmap_empty fds_init_heap_insert // fds_init_heap_empty right_id_L.
      done.
Qed.

Lemma pass_fn_vars f :
  lfd_vars (pass_fn f) ⊆ lfd_vars f.
Proof. rewrite /pass_fn. case_match => /=. by apply: foldr_pass_single_vars. Qed.

Lemma pass_fn_static_vars f :
  lfd_static_vars (pass_fn f) = lfd_static_vars f.
Proof. rewrite /pass_fn. by case_match => /=. Qed.

Lemma NoDup_pass_fn f :
  NoDup (lfd_args f ++ (lfd_static_vars f).*1 ++ (lfd_vars f).*1) →
  NoDup (lfd_args (pass_fn f) ++ (lfd_static_vars (pass_fn f)).*1 ++ (lfd_vars (pass_fn f)).*1).
Proof.
  rewrite !NoDup_app.
  rewrite pass_fn_args => [[Hnd1 [H1 [Hnd2 [Hnd3 H2]]]]].
  have ? := pass_fn_vars f.
  have Hstatic := pass_fn_static_vars f.
  split!.
  - rewrite Hstatic. set_solver.
  - by rewrite Hstatic.
  - rewrite Hstatic. set_solver.
  - rewrite /pass_fn. case_match => /=. by eapply foldr_pass_single_nodup.
Qed.

Lemma pass_fn_correct f fn :
  NoDup (fn.(lfd_args) ++ fn.(lfd_static_vars).*1 ++ fn.(lfd_vars).*1) →
  trefines (linear_rec_mod (<[f := pass_fn fn]> ∅))
           (rec_heap_bij_N (length fn.(lfd_vars)) (fd_init_heap f (fn.(lfd_static_vars))) (linear_rec_mod (<[f := fn]> ∅))).
Proof.
  rewrite /pass_fn. destruct pass_body as [expri varsi] eqn: Hpass.
  revert Hpass. destruct fn as [args static_varss varss exprs]; simpl.
  intros Heq Hnd. by eapply pass_body_correct.
Qed.

End cr2a_mem2reg.
