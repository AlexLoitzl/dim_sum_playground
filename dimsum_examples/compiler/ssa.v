From stdpp Require Import pretty.
From dimsum.core Require Export proof_techniques.
From dimsum.examples Require Import rec.

Local Open Scope Z_scope.
Set Default Proof Using "Type".

(** * SSA pass : Rec -> Rec *)
(** This pass renames let bindings, function arguments, and local
variables such that all names are unique. This is used by the
following passes. *)

Definition ssa_var (s : string) (n : N) : string :=
  s ++ "$" ++ pretty n.

Global Instance ssa_var_inj : Inj2 (=) (=) (=) ssa_var.
Proof.
  move => ????. unfold ssa_var.
  move => /string_list_eq.
  rewrite !string_to_list_app => /= /(app_inj_middle _ _ _ _  _)[| |??]. 3: naive_solver.
  all: move => /pretty_N_digits; compute_done.
Qed.

Module cr2a_ssa.

(** * pass *)
(** Since this pass is simple, we don't use the full compiler monad,
but just hand-roll a state monad. *)
Fixpoint state_bind {S A} (l : list (S → (S * A))) (s : S) : (S * list A) :=
  match l with
  | [] => (s, [])
  | f::l' =>
      let r1 := f s in
      let r2 := state_bind l' r1.1 in
      (r2.1, r1.2::r2.2)
  end.

Fixpoint pass (ren : gmap string string) (e : static_expr) (s : N) : (N * static_expr) :=
  match e with
  | SVar v => (s, SVar (default v (ren !! v)))
  | SVal v => (s, SVal v)
  | SBinOp e1 o e2 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      (p2.1, SBinOp p1.2 o p2.2)
  | SLoad e1 =>
      let p1 := pass ren e1 s in
      (p1.1, SLoad p1.2)
  | SStore e1 e2 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      (p2.1, SStore p1.2 p2.2)
  | SCall e args =>
      let p1 := pass ren e s in
      let p2 := state_bind (pass ren <$> args) p1.1 in
      (p2.1, SCall p1.2 p2.2)
  | SLetE v e1 e2 =>
      let p1 := pass ren e1 (s + 1) in
      let p2 := pass (<[v := ssa_var v s]> ren) e2 p1.1 in
      (p2.1, SLetE (ssa_var v s) p1.2 p2.2)
  | SIf e1 e2 e3 =>
      let p1 := pass ren e1 s in
      let p2 := pass ren e2 p1.1 in
      let p3 := pass ren e3 p2.1 in
      (p3.1, SIf p1.2 p2.2 p3.2)
  end.

Definition test_fn_1 : fndef := {|
  fd_args := ["x"];
  fd_static_vars := [("y", 1)];
  fd_vars := [("y", 1)];
  fd_body := (LetE "x" (LetE "x" (Var "y") $ Var "x") $
              LetE "y" (Var "x") $
              LetE "x" (Var "x") $
              Var "x");
  fd_static := I;
|}.
Lemma test_fn_1_test :
  pass ∅ (expr_to_static_expr $ test_fn_1.(fd_body)) 0 =
  (4%N, SLetE "x$0" (SLetE "x$1" (SVar "y") (SVar "x$1"))
       (SLetE "y$2" (SVar "x$0") (SLetE "x$3" (SVar "x$0") (SVar "x$3")))).
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

(** * Verification of pass *)
Lemma pass_state ren s e :
  (pass ren e s).1 = (s + N.of_nat (length (assigned_vars (static_expr_to_expr e))))%N.
Proof.
  revert ren s. induction e => //= ren s; try lia.
  all: rewrite ?IHe1 ?IHe2 ?IHe3 ?length_app; try lia.
  rewrite IHe Nat2N.inj_add N.add_assoc. move: ren (s + _)%N.
  revert select (Forall _ _). elim; csimpl; [lia|].
  move => ?? IH1 _ IH2 ??. rewrite IH1 IH2 length_app. lia.
Qed.

Lemma pass_vars ren s e :
  assigned_vars (static_expr_to_expr (pass ren e s).2) =
  imap (λ n v, ssa_var v (s + N.of_nat n)) (assigned_vars (static_expr_to_expr e)).
Proof.
  revert ren s. induction e => //= ren s.
  all: rewrite ?IHe1 ?IHe2 ?IHe3 ?pass_state ?imap_app.
  all: repeat match goal with
              | |- _ :: _ = _ :: _ => f_equal
              | |- _ ++ _ = _ ++ _ => f_equal
              | |- imap _ _ = imap _ _ => apply imap_ext => * /=
              | |- ssa_var _ _ = ssa_var _ _ => f_equal
              end; try lia; try done.
  (* setoid_rewrite does not work in the argument of imap so we have to use this workaround *)
  erewrite imap_ext. 2: { move => ?? _. rewrite Nat2N.inj_add N.add_assoc. done. }
  move: (s + _)%N. revert select (Forall _ _).
  elim => //; csimpl => ?? IH1 _ IH2 {}s.
  rewrite imap_app IH2 pass_state. f_equal; [done|].
  apply imap_ext => * /=. f_equal. lia.
Qed.

Lemma pass_correct Ki Ks ei es es' n h fns1 fns2 s vsi vss ren
      `{!RecExprFill es Ks (subst_map vss (static_expr_to_expr es'))}
      `{!RecExprFill ei Ki (subst_map vsi (static_expr_to_expr (pass ren es' s).2))}:
  rec_proof_call n fns1 fns2 →
  (∀ i v, vss !! i = Some v → ∃ i', ren !! i = Some i' ∧ vsi !! i' = Some v) →
  (∀ x s', (s ≤ s')%N → vsi !! ssa_var x s' = None) →
  (∀ h' v',
    Rec (expr_fill Ki $ (Val v')) h' fns1
       ⪯{rec_trans, rec_trans, n, false}
    Rec (expr_fill Ks (Val v')) h' fns2) →
  Rec ei h fns1
      ⪯{rec_trans, rec_trans, n, false}
  Rec es h fns2.
Proof.
  move => Hcall.
  revert es ei ren s vsi vss h Ks Ki RecExprFill0 RecExprFill1.
  induction es' => //= es ei ren s vsi vss h Ks Ki [?] [?] Hvs Hvars Hcont; simplify_eq.
  - destruct (vss !! x) eqn: Hx. 2: by tstep_s.
    move: Hx => /Hvs[?[-> ->]]. done.
  - done.
  - apply: IHes'1; [done|done|] => /= ??.
    apply: IHes'2; [done|rewrite pass_state;naive_solver lia|] => /= ??.
    tstep_s => ??. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'; [done|done|] => /= ??.
    tstep_s => *. subst. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'1; [done|done|] => /= ??.
    apply: IHes'2; [done|rewrite pass_state;naive_solver lia|] => /= ??.
    tstep_s => *. subst. tstep_i. split!. by apply tsim_mono_b_false.
  - apply: IHes'1; [done|done|] => /= ??.
    tstep_s => *. subst. tstep_i. apply tsim_mono_b_false. case_match.
    + apply: IHes'2; [done|rewrite pass_state;naive_solver lia|] => /= ??. done.
    + apply: IHes'3; [done|rewrite !pass_state;naive_solver lia|] => /= ??. done.
  - apply: IHes'1; [done|naive_solver lia|] => /= ??.
    tstep_i. tstep_s. rewrite -!subst_subst_map_delete. apply tsim_mono_b_false.
    apply: IHes'2; [ | |done].
    + move => ?? /lookup_insert_Some[[??]|[?/Hvs[?[? Hvsi]]]]; simplify_eq.
      { eexists _. by simplify_map_eq. }
      eexists _. rewrite lookup_insert_ne //. split; [done|].
      apply lookup_insert_Some. right. split!. move => ?. subst. move: Hvsi.
      apply: eq_None_ne_Some_1. naive_solver lia.
    + move => ? s'. rewrite !pass_state => ?. apply lookup_insert_None. naive_solver lia.
  - apply: IHes'; [done|done|] => /= {}h ?.
    rewrite pass_state. move Heq: (s + _)%N => s0'. have Hs0': (s ≤ s0')%N by lia. clear Heq.
    rewrite -(app_nil_l (subst_map vsi <$> _)) -(app_nil_l (subst_map vss <$> _)).
    change ([]) with (Val <$> []). move: [] => vs. move: s0' vs h Hs0' Hvars.
    revert select (Forall _ _). elim.
    + move => ????? /=. rewrite app_nil_r.
      tstep_s => ? ->.
      apply: Hcall; [done| | |done|done|done].
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
      { apply Forall2_fmap_l. apply Forall_Forall2_diag. by apply Forall_true. }
    + move => ?? IH _ IH2 s0' vs h Hs0' Hvars. csimpl.
      eapply IH => /=.
      { constructor. by instantiate (2:=(CallCtx _ _ _) ::_). }
      { constructor. by instantiate (4:=(CallCtx _ _ _) ::_). }
      { done. }
      { move => ??. naive_solver lia. }
      move => ?? /=. rewrite !cons_middle !app_assoc -fmap_snoc.
      apply IH2.
      { rewrite pass_state. naive_solver lia. }
      { done. }
Qed.

(** * pass_fn *)
Definition pass_fn (f : static_fndef) : static_fndef :=
  let args := imap (λ n v, ssa_var v (N.of_nat n)) f.(sfd_args) in
  let static_vars := imap (λ n v, (ssa_var v.1 (N.of_nat (length args + n)), v.2)) f.(sfd_static_vars) in
  let vars := imap (λ n v, (ssa_var v.1 (N.of_nat (length args + length static_vars + n)), v.2)) f.(sfd_vars) in
  {|
     sfd_args := args;
     sfd_static_vars := static_vars;
     sfd_vars := vars;
     sfd_body := (pass (list_to_map (zip f.(sfd_args) args)
                ∪ list_to_map (zip f.(sfd_static_vars).*1 static_vars.*1)
                ∪ list_to_map (zip f.(sfd_vars).*1 vars.*1))
                f.(sfd_body) (N.of_nat (length f.(sfd_args) + length f.(sfd_static_vars) + length f.(sfd_vars)))).2;
  |}.

Lemma pass_fn_statics_eq_snd f :
  (sfd_static_vars (pass_fn f)).*2 = (sfd_static_vars f).*2.
Proof.
  simpl.
  enough (∀ A g, (imap (λ n v, ((g n v) : A, v.2)) (sfd_static_vars f)).*2 = (sfd_static_vars f).*2) by done.
  induction (sfd_static_vars f) as [|? ? IH] => //=.
  move => A g. f_equal. apply IH.
Qed.

Lemma test_fn_1_test_pass :
  pass_fn (fndef_to_static_fndef test_fn_1) = {|
    sfd_args := ["x$0"];
    sfd_static_vars := [("y$1", 1)];
    sfd_vars := [("y$2", 1)];
    sfd_body :=
      SLetE "x$3" (SLetE "x$4" (SVar "y$1") (SVar "x$4"))
        (SLetE "y$5" (SVar "x$3") (SLetE "x$6" (SVar "x$3") (SVar "x$6")))
  |}.
Proof. vm_compute. match goal with |- ?x = ?x => exact: eq_refl end. Abort.

(** * Verification of pass_fn *)
Lemma pass_fn_args_NoDup fn:
  NoDup (sfd_args (pass_fn fn) ++ (sfd_static_vars (pass_fn fn)).*1 ++ (sfd_vars (pass_fn fn)).*1).
Proof.
  apply NoDup_alt => /= ???.
  rewrite !lookup_app_Some ?length_fmap ?length_imap ?list_lookup_fmap ?fmap_Some.
  setoid_rewrite list_lookup_imap_Some.
  naive_solver lia.
Qed.

Lemma pass_fn_vars f :
  sfd_args (pass_fn f) ++ (sfd_static_vars (pass_fn f)).*1 ++ (sfd_vars (pass_fn f)).*1 ++ assigned_vars (static_expr_to_expr (sfd_body (pass_fn f))) =
  imap (λ n v, ssa_var v (N.of_nat n)) (sfd_args f ++ (sfd_static_vars f).*1 ++ (sfd_vars f).*1 ++ assigned_vars (static_expr_to_expr (sfd_body f))).
Proof.
  rewrite !imap_app. f_equal. f_equal; last f_equal.
  - rewrite imap_fmap fmap_imap.
    apply imap_ext => * /=. f_equal. by rewrite length_imap.
  - rewrite fmap_imap imap_fmap. apply imap_ext. move => * /=. rewrite length_fmap !length_imap. f_equal. lia.
  - rewrite pass_vars !length_fmap. apply imap_ext. move => * /=. f_equal. lia.
Qed.

Lemma pass_fn_correct f fn :
  trefines (rec_static_mod (<[f := pass_fn fn]> ∅))
           (rec_static_mod (<[f := fn]> ∅)).
Proof.
  apply rec_proof. { move => ?. rewrite !lookup_fmap !fmap_None !lookup_insert_None. naive_solver. }
  move => ????? vs ?. rewrite /subst_static !fmap_insert !fmap_empty /=.
  move => /lookup_insert_Some[[??]|[??]]; simplify_map_eq. split!. { by rewrite length_imap. }
  rewrite !length_imap. move => ?? Hret.
  tstep_both => ls ? Hl. rewrite fmap_imap (imap_const snd) in Hl.
  tstep_s. split!; [done|] => ?. tend. rewrite !fmap_imap (imap_const snd). split!.
  opose proof* heap_alloc_list_length as Hlen; [done|]. rewrite length_fmap in Hlen.
  rewrite !subst_l_subst_map; [| rewrite ?length_fmap ?length_imap; lia..].
  rewrite -!subst_map_subst_map. apply tsim_mono_b_false.
  apply: pass_correct; [done|..].
  - move => i v /lookup_union_Some_raw.
    setoid_rewrite lookup_union_Some_raw.
    setoid_rewrite lookup_union_Some_raw.
    setoid_rewrite lookup_union_None.
    setoid_rewrite list_to_map_lookup_Some.
    setoid_rewrite <-not_elem_of_list_to_map.
    setoid_rewrite elem_of_list_fmap.
    setoid_rewrite elem_of_lookup_zip_with.
    setoid_rewrite lookup_zip_with_Some.
    setoid_rewrite list_lookup_imap_Some.
    setoid_rewrite list_lookup_fmap.
    setoid_rewrite fmap_Some.
    setoid_rewrite lookup_zip_with_Some.
    setoid_rewrite list_lookup_fmap.
    setoid_rewrite fmap_Some.
    setoid_rewrite list_lookup_imap_Some.
    setoid_rewrite list_lookup_fmap.
    setoid_rewrite fmap_Some.
    setoid_rewrite list_lookup_imap_Some.
    move => ?. destruct!.
    + split!; left; split! => //.
      * split!; left; split! => //.
        move => j' ???.
        have ?:= lookup_lt_Some vs j _ ltac:(done).
        have [|??]:= lookup_lt_is_Some_2 vs j'; [lia|].
        naive_solver.
      * naive_solver.
    + split!; [left; right; split! => //|].
      * rename select (¬ _) into Hneg. contradict Hneg. destruct!/=.
        have ?:= lookup_lt_Some (sfd_args fn) _ _ ltac:(done).
        have [|??]:= lookup_lt_is_Some_2 vs i; [lia|]. by split!.
      * move => j' ???.
        have ?:= lookup_lt_Some (sfd_static_vars fn) j _ ltac:(done).
        have [|??]:= lookup_lt_is_Some_2 ((sfd_static_vars fn).*2) j'; [rewrite length_fmap; lia|].
        destruct!/=. revert select (∀ j y, _ → _ → _ ≠ _). apply; [|done]. split!.
      * right. split! => //.
        -- move => ?. destruct!/=.
           rename select (¬ _) into Hneg. contradict Hneg. by split!.
        -- left. split!. move => j'' y'' ???.
           rename select (∀ j y, _ → _ → _ ≠ _) into Hneq.
           specialize (Hneq j'' x1.1).
           simplify_eq. destruct!/=.
           have ?:= lookup_lt_Some (sfd_static_vars fn) j _ ltac:(done).
           have [|??]:= lookup_lt_is_Some_2 ((sfd_static_vars fn).*2) j''; [rewrite length_fmap; lia|].
           apply Hneq; split!.
    + split!; right; split! => //.
      * rename select (¬ _) into Hneg. contradict Hneg. destruct!/=.
        have ?:= lookup_lt_Some (sfd_args fn) _ _ ltac:(done).
        have [|??]:= lookup_lt_is_Some_2 vs i; [lia|]. by split!.
      * contradict H1. destruct!/=. by split!.
      * move => j' ???.
        have ?:= lookup_lt_Some ls j _ ltac:(done).
        have [|??]:= lookup_lt_is_Some_2 ls j'; [lia|].
        destruct!/=.
        apply: H3; [|done]. split!.
      * move => ?. destruct!/=.
        have ?:= lookup_lt_Some (sfd_args fn) _ _ ltac:(done). lia.
      * right. split!; [|naive_solver lia..].
        move => ?. destruct!/=.
        have ?:= lookup_lt_Some (sfd_static_vars fn) i _ ltac:(done). lia.
  - move => ???. rewrite !lookup_union_None. split!; apply not_elem_of_list_to_map_1.
    + move => /elem_of_list_fmap[[??][?]] /(elem_of_zip_with _ _ _ _)[?[?[?[/elem_of_lookup_imap]]]].
      move => [?[?[? /(lookup_lt_Some _ _ _) ?]]]. naive_solver lia.
    + move => /elem_of_list_fmap[[??][?]] /(elem_of_zip_with _ _ _ _)[?[?[?[/elem_of_lookup_imap]]]].
      move => [?[?[? /(lookup_lt_Some _ _ _) ?]]]. naive_solver lia.
    + move => /elem_of_list_fmap[[??][?]] /(elem_of_zip_with _ _ _ _)[?[?[?[/elem_of_lookup_imap]]]].
    move => [?[?[? /(lookup_lt_Some _ _ _) ?]]]. naive_solver lia.
  - move => ?? /=.
    tstep_s => ??. tstep_i. split!; [done|].
    by apply Hret.
Qed.

End cr2a_ssa.
