From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import itree_mod.
From dimsum.examples Require Import rec asm rec_to_asm.
From dimsum.examples.compiler Require Import compiler.

Local Open Scope Z_scope.

(** * Example for specifying integer pointer casts via angelic choice *)

Definition int_to_ptr_asm : gmap Z asm_instr :=
  (* cast_int_to_ptr *)
  <[ 400 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $
  (* cast_ptr_to_int *)
  <[ 401 := [
        (* ret *)
        WriteReg "PC" (λ rs, rs !!! "R30")
    ] ]> $ ∅.

Definition int_to_ptr_fns : gset string :=
  {["cast_int_to_ptr"; "cast_ptr_to_int" ]}.

Definition int_to_ptr_f2i : gmap string Z :=
  <["cast_int_to_ptr" := 400]> $ <["cast_ptr_to_int" := 401]> $ ∅.

Definition int_to_ptr_spec : itree (moduleE rec_event (gmap prov Z)) void :=
  ITree.forever (
      '(f, vs, h) ← demonic _;
      visible (Incoming, ERCall f vs h);;
      if bool_decide (f = "cast_int_to_ptr") then
        z ← angelic Z;
        assume (vs = [ValNum z]);;
        l ← angelic loc;
        ps ← get_state;
        assume (ps !! l.1 = Some (z - l.2));;
        visible (Outgoing, ERReturn (ValLoc l) h)
      else if bool_decide (f = "cast_ptr_to_int") then
        l ← angelic loc;
        assume (vs = [ValLoc l]);;
        z ← demonic Z;
        ps ← get_state;
        let ps' := <[l.1 := (default z (ps !! l.1))]> ps in
        set_state ps';;
        visible (Outgoing, ERReturn (ValNum (ps' !!! l.1 + l.2)) h)
      else
        NB)%itree.

(**
 Example:

 100 <- cast_ptr_to_int(l);
 200 <- cast_ptr_to_int(p);

  (* b = nondet(); // works *)
  x = cast_int_to_ptr(300); // l + 200 | p + 100

  (* b = nondet(); // does not work *)

  assert(x == l);
  assert(x == p); // UB here (and in in PNVI)

  if(b) {
    assert(x == l);
  } else {
    assert(x == p);
  }

 *)

Local Ltac go :=
  clear_itree.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(*
  asm_module(int_to_ptr_asm) {asm_event}
    <= {asm_event}
  rec_to_asm(itree_module(int_to_ptr_spec {rec_event}) {rec_event}) {asm_event}
*)

Lemma int_to_ptr_asm_refines_spec :
  trefines (asm_mod int_to_ptr_asm)
           (rec_to_asm (dom int_to_ptr_asm) int_to_ptr_f2i ∅ ∅
              (itree_mod int_to_ptr_spec ∅)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(σf, (t, ps), (pp, σr2a, P)),
    ∃ b rP, P = uPred_shrink rP ∧
    t ⊒ ↓ᵢ (Tau?b int_to_ptr_spec) ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = int_to_ptr_asm ∧
    σr2a.(r2a_calls) = [] ∧
    σf = SMFilter ∧
    pp = PPOutside ∧
    (rP ⊢ r2a_f2i_incl int_to_ptr_f2i (dom int_to_ptr_asm) ∗ [∗ map] p↦z∈ps, r2a_heap_shared p z)). }
  { exists false. split!. iIntros!. iFrame "#". by rewrite big_sepM_empty. } { done. }
  move => n _ Hloop [????] [[?[? ps]][[??]?]] ?. destruct!/=.
  tstep_i => ????? Hi. tstep_s. split!.
  tstep_i => ??. simplify_map_eq.
  tstep_s => *. case_match => /= *. 2: congruence.
  go_s. tstep_s. rewrite -/int_to_ptr_spec. go. go_s. eexists (_, _, _). go.
  go_s. split!. go.
  revert select (_ ⊢ _) => HP.
  revert select (_ ∉ dom _) => /not_elem_of_dom?.
  iSatStart. rewrite HP. iIntros!. iDestruct select (r2a_f2i_incl int_to_ptr_f2i _) as "Hf2i".
  iDestruct (r2a_f2i_incl_in_ins with "Hf2i [$]") as %?; [done|]. iSatStop.
  unfold int_to_ptr_asm in Hi. unfold int_to_ptr_f2i in *. (repeat case_bool_decide); simplify_map_eq'.
  - tstep_i.
    go_s => ?. go.
    go_s => ?. go.
    go_s => ?. go.
    go_s. go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (r2a_args_intro with "[$]") as "?"; [done|].
    rewrite r2a_args_cons ?r2a_args_nil; [|done]. iDestruct!.
    iDestruct (big_sepM_lookup with "[$]") as "#?"; [done|].
    iSatStop.
    tstep_i => ??. simplify_map_eq'.
    go_s. go_s. split!.
    { by simplify_map_eq'. }
    { instantiate (1:=[_]). unfold r2a_regs_ret; split!; simplify_map_eq'; split!.
      - apply map_preserved_insert_r_not_in; [|done]. compute_done.
    }
    { apply map_scramble_insert_r_in; [compute_done|done]. }
    { iSatMono. simplify_map_eq'. iIntros!. iFrame. iSplitL; [iAccu|]. iSplit!; [|done]. lia. }
    apply Hloop; [done|]. exists true. split!. iIntros!. iFrame "#".
  - tstep_i.
    go_s => l. go.
    go_s => ?. go.
    iSatStart. iIntros!.
    iDestruct (r2a_args_intro with "[$]") as "?"; [done|].
    rewrite r2a_args_cons ?r2a_args_nil; [|done]. iDestruct!.
    iAssert ⌜z = default z (ps !! l.1)⌝%I as %Hz.
    { destruct (ps !! l.1) as [z'|] eqn:Hp => //=.
      iDestruct (big_sepM_lookup with "[$]") as "?"; [done|].
      iAssert ⌜z' = z⌝%I as %?; [|done].
      by iApply (r2a_heap_shared_ag with "[$]"). }
    iSatStop.
    go_s. eexists z. go.
    go_s. go_s. go_s.
    tstep_i => ??. simplify_map_eq'.
    go_s. split!.
    { by simplify_map_eq'. }
    { instantiate (1:=[_]). unfold r2a_regs_ret; split!; simplify_map_eq'; split!.
      - apply map_preserved_insert_r_not_in; [|done]. compute_done.
    }
    { apply map_scramble_insert_r_in; [compute_done|done]. }
    { iSatMono. simplify_map_eq'. iFrame. iSplitL; [by iStopProof|].
      rewrite -Hz. done.
    }
    apply Hloop; [done|]. exists true.
    split!. iIntros!. iFrame "#". rewrite -Hz.
    by iApply big_sepM_insert_2.
Qed.

(*
void main () {
  local l[1];
  *l = 1;
  size_t z = cast_ptr_to_int(l);
  size_t z' = z - 1 + 1;
  size_t *l' = cast_int_to_ptr(z');
  size_t r = *l';
  exit(r);
}

*)

Definition main_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [("l", 1)];
  fd_body := LetE "_" (Store (Var "l") (Val 1)) $
             LetE "z" (rec.Call (Val (ValFn "cast_ptr_to_int")) [(Var "l")]) $
             LetE "z'" (BinOp (BinOp (Var "z") AddOp (Val (-1))) AddOp (Val 1)) $
             LetE "l'" (rec.Call (Val (ValFn "cast_int_to_ptr")) [(Var "z")]) $
             rec.Call (Val (ValFn "exit")) [(Load (Var "l'"))];
  fd_static := I
|}.

Definition main_rec_prog : gmap string fndef :=
  <[ "main" := main_rec ]> ∅.

Definition main_spec : itree (moduleE rec_event unit) void :=
  ('(f, vs, h) ← demonic _;
  visible (Incoming, ERCall f vs h);;
  assume (f = "main");;
  assume (vs = []);;
  h' ← demonic (heap_state);
  visible (Outgoing, ERCall "exit" [ValNum 1] h');;
  UB)%itree.

(*
  rec_module(main_rec) {rec_event} +rec itree_module(int_to_ptr_spec {rec_event}) {rec_event}
      <= {rec_event}
  itree_module(main_spec {rec_event}) {rec_event}
*)

Lemma main_int_to_ptr_refines_spec :
  trefines (rec_link (dom main_rec_prog) int_to_ptr_fns (rec_mod main_rec_prog) (itree_mod int_to_ptr_spec ∅))
           (itree_mod main_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct!.
  go_s. eexists (_, _, _). go. go_s. split!. go.
  go_s => ?. go. go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|compute_done].
  tstep_i. split! => ???? Hf ?. simplify_eq.
  change (@nil expr) with (Val <$> []).
  tstep_i. split!. move => ??. simplify_eq. unfold main_rec_prog in Hf. simplify_map_eq. split!.
  tstep_i => ???. destruct!. split!. { repeat econs. }
  tstep_i. split. { apply heap_alive_alloc; [done|lia]. }
  tstep_i. change ([Val (ValLoc l)]) with (Val <$> [ValLoc l]).
  tstep_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  move => *. destruct!/=.
  tstep_i. rewrite -/int_to_ptr_spec. go.
  go_i => -[[??]?]. go.
  go_i => ?. go. simplify_eq/=.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i => z. go.
  go_i. go_i. simplify_map_eq'.
  go_i => *. go. destruct!.
  go_i. split!. move => *. simplify_eq.
  go_i.
  go_i.
  go_i.
  go_i. change ([Val (z + l.2)]) with (Val <$> [ValNum (z + l.2)]).
  tstep_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done]. rewrite bool_decide_true; [|compute_done].
  move => *. destruct!/=.
  go_i. tstep_i. rewrite -/int_to_ptr_spec. go.
  go_i => -[[??]?]. go.
  go_i => ?. go. simplify_eq/=.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i. eexists l. go.
  go_i.
  go_i. simplify_map_eq. split; [f_equal; lia|]. go.
  go_i => *. go. destruct!.
  go_i. split!. move => *. simplify_eq.
  go_i.
  go_i. eexists _. simplify_map_eq. rewrite heap_alloc_h_lookup; [|done|lia]. split. { by simplify_map_eq. }
  go_i. split. { move => *; simplify_map_eq. }
  move => ????. rewrite bool_decide_false; [|compute_done].
  move => *. destruct!/=.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s. done.
Qed.

Definition main_f2i : gmap string Z := <["main" := 200]> $ <["exit" := 100]> int_to_ptr_f2i .

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 200 ltac:(r2a_compile main_f2i 100 main_rec).

(* We need to lock this, otherwise simpl goes crazy. *)
Definition main_asm_dom : gset Z := locked dom main_asm.

(*
  asm_module(main_asm) {asm_event}
    <= {asm_event}
  rec_to_asm(rec_module(main_rec) {rec_event}) {asm_event}
*)

Lemma main_asm_refines_rec :
  trefines (asm_mod main_asm)
           (rec_to_asm (dom main_asm) main_f2i ∅ ∅ (rec_mod main_rec_prog)).
Proof. apply: (compile_correct 100); [|done|..]; compute_done. Qed.

(* https://thog.github.io/syscalls-table-aarch64/latest.html *)
Definition __NR_EXIT : Z := 93.

Definition exit_asm : gmap Z asm_instr :=
  (* exit *)
  <[ 100 := [
        WriteReg "R8" (λ rs, __NR_EXIT);
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 101 := [
        Syscall;
        WriteReg "PC" (λ rs, rs !!! "PC" + 1)
    ] ]> $
  <[ 102 := [
        (* loop *)
        WriteReg "PC" (λ rs, rs !!! "PC")
    ] ]> $ ∅.

Definition exit_spec : itree (moduleE asm_event unit) void :=
  ('(rs, mem) ← demonic _;
  visible (Incoming, EAJump rs mem);;
  assume (rs !!! "PC" = 100);;
  args ← demonic _;
  assert (length args = length syscall_arg_regs);;
  assert (args !! 0%nat = Some (rs !!! "R0"));;
  assert (args !! 8%nat = Some __NR_EXIT);;
  visible (Outgoing, EASyscallCall args mem);;
  '(ret, mem) ← demonic _;
  visible (Incoming, EASyscallRet ret mem);;
  NB)%itree.

(*
  asm_module(exit_asm) {asm_event}
    <= {asm_event}
  itree_module(exit_spec {asm_event}) {asm_event}
*)

Lemma exit_asm_refines_spec :
  trefines (asm_mod exit_asm) (itree_mod exit_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ????? Hi.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_i => ??. simplify_map_eq.
  go_s => ?. go.
  unfold exit_asm in Hi. simplify_map_eq'.
  go_i.
  go_i.
  go_i => ??. simplify_map_eq'.
  go_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  go_i => ? ?.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_i.
  sort_map_insert. simplify_map_eq'.
  unshelve eapply tsim_remember. { exact (λ _ '(AsmState i rs _ ins) _,
      i = ARunning [] ∧ rs !!! "PC" = 102 ∧ ins = exit_asm). }
  { split!. by simplify_map_eq'. } { done. }
  move => ?? Hloop [????] ? ?. destruct!.
  go_i => ??. simplify_map_eq'.
  go_i.
  apply Hloop; [done|]. split!. by simplify_map_eq'.
  Unshelve.
  - done.
  - by simplify_map_eq'.
  - by simplify_map_eq'.
Qed.

(* TODO: something even more high-level? Maybe stated as safety property on traces? *)

Definition top_level_spec : itree (moduleE asm_event unit) void :=
  ('(rs, mem) ← demonic _;
  visible (Incoming, EAJump rs mem);;
  assume (rs !!! "PC" = 200);;
  assume (rs !!! "R30" ∉ main_asm_dom ∪ dom int_to_ptr_asm);;
  assume (∃ ssz, r2a_mem_stack_mem (rs !!! "SP") ssz ⊆ mem);;
  args ← demonic _;
  mem ← demonic _;
  assert (length args = length syscall_arg_regs);;
  assert (args !! 0%nat = Some 1);;
  assert (args !! 8%nat = Some __NR_EXIT);;
  visible (Outgoing, EASyscallCall args mem);;
  '(ret, mem) ← demonic _;
  visible (Incoming, EASyscallRet ret mem);;
  NB)%itree.

(*
   rec_to_asm(itree_module(main_spec {rec_event}) {rec_event}) {asm_event}
    +asm
   itree_module(exit_spec {asm_event}) {asm_event}
      <= {asm_event}
   itree_module(toplevel_spec {asm_event}) {asm_event}
*)

Lemma top_level_refines_spec :
  trefines (asm_link (main_asm_dom ∪ dom int_to_ptr_asm) (dom exit_asm)
              (rec_to_asm (main_asm_dom ∪ dom int_to_ptr_asm) main_f2i ∅ ∅
                 (itree_mod main_spec tt)) (itree_mod exit_spec tt))
    (itree_mod top_level_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  go_i => ??????. case_match; destruct!.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go. destruct!. simplify_map_eq'.
  rewrite bool_decide_true; [|unfold main_asm_dom;unlock; compute_done].
  go_i => ??. simplify_eq.
  go_i. eexists true => /=. split; [done|]. eexists ∅, _, [], [], "main".
  split!.
  { simplify_map_eq'. rewrite/main_asm_dom. unlock. compute_done. }
  { apply: satisfiable_mono; [by eapply (r2a_res_init mem ∅ main_f2i)|].
    iIntros!. rewrite /r2a_mem_map big_sepM_empty. iFrame.
    iDestruct select (r2a_f2i_full _) as "#Hf2i".
    iSplit!. 2: iSplitL; iSplit!.
    - unfold r2a_f2i_incl. iExists _. iFrame "#". iSplit!.
    - iApply r2a_mem_stack_init. by iApply big_sepM_subseteq.
    - iApply (r2a_f2i_full_to_singleton with "[$]"). by simplify_map_eq'.
    - iExact "Hf2i". }
  go_i => -[[??]?]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. go.
  go_i => ?. go.
  go_i.
  go_i. move => *. unfold main_f2i in *. destruct!; simplify_map_eq'.
  iSatStart. iIntros!. iDestruct (r2a_f2i_full_singleton with "[$] [$]") as %?. simplify_map_eq'. iSatStop.
  rewrite bool_decide_false; [|done].
  rewrite bool_decide_true; [|compute_done].
  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => *. destruct!. go.
  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  go_i => *. case_match; destruct!.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_i => -[??]. go.
  go_i => *. go.
  go_i => *. done.
  Unshelve.
  - done.
  - iSatStart. iIntros!. iDestruct (r2a_args_intro with "[$]") as "?"; [done|].
    rewrite r2a_args_cons; [|done]. iDestruct!. iSatStop. by simplify_map_eq'.
  - done.
Qed.

(*
  asm_module(main_asm ∪ int_to_ptr_asm ∪ exit_asm) {asm_event}
    <= {asm_event}
  itree_module(toplevel_spec {asm_event}) {asm_event}
*)

Lemma complete_refinement :
  trefines (asm_mod (main_asm ∪ int_to_ptr_asm ∪ exit_asm))
           (itree_mod top_level_spec tt).
Proof.
  etrans. {
    apply asm_syn_link_refines_link. compute_done.
  }
  etrans. {
    apply: asm_link_trefines.
    - etrans. {
        apply asm_syn_link_refines_link. compute_done.
      }
      etrans. {
        apply: asm_link_trefines.
        - apply main_asm_refines_rec.
        - apply int_to_ptr_asm_refines_spec.
      }
      etrans. {
        apply (rec_to_asm_combine _ _ (dom main_rec_prog) int_to_ptr_fns); [apply _|apply _|..]; compute_done.
      }
      etrans. {
        apply rec_to_asm_trefines; [apply _|].
        apply main_int_to_ptr_refines_spec.
      }
      have -> : (main_f2i ∪ int_to_ptr_f2i) = main_f2i by compute_done.
      done.
    - apply exit_asm_refines_spec.
  }
  etrans. {
    etrans; [|apply: (top_level_refines_spec)].
    rewrite dom_union_L /main_asm_dom left_id_L. unlock. done.
  }
  done.
Qed.

(* Print Assumptions complete_refinement. *)
