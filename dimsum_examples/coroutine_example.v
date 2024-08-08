From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import rec asm rec_to_asm print coroutine.
From dimsum.examples.compiler Require Import compiler.

Local Open Scope Z_scope.

(** * Example using the coroutine library *)

Definition stream_addr: Z := 700.
Definition main_addr: Z := 800.

Definition stream_rec: fndef := {|
  fd_args := [("n")];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := LetE "_" (rec.Call (Val (ValFn "yield")) [Var "n"]) $
             (rec.Call (Val (ValFn "stream")) [BinOp (Var "n") AddOp (Val $ ValNum 1)]);
  fd_static := I
|}.
Definition stream_prog : gmap string fndef :=
  <["stream" := stream_rec]> $ ∅.

Definition main_rec: fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := LetE "x" (rec.Call (Val (ValFn "yield")) [Val $ ValNum 0]) $
             LetE "_" (rec.Call (Val (ValFn "print")) [(Var "x")]) $
             LetE "y" (rec.Call (Val (ValFn "yield")) [Val $ ValNum 0]) $
             LetE "_" (rec.Call (Val (ValFn "print")) [(Var "y")]) $
             (rec.Call (Val (ValFn "yield")) [Val $ ValNum 0]);
  fd_static := I
|}.
Definition main_prog : gmap string fndef :=
  <["main" := main_rec]> $ ∅.

Definition all_f2i : gmap string Z :=
  <["yield"  := yield_addr]> $
  <["stream" := stream_addr]> $
  <["main"   := main_addr]> $
  <["print"  := print_addr]> $
  ∅.

Definition stream_asm : gmap Z asm_instr :=
  deep_to_asm_instrs stream_addr ltac:(r2a_compile all_f2i 1000 stream_rec).

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs main_addr ltac:(r2a_compile all_f2i 2000 main_rec).

Definition stream_asm_dom : gset Z := locked dom stream_asm.
Definition main_asm_dom : gset Z := locked dom main_asm.

Lemma stream_asm_refines_rec :
  trefines (asm_mod stream_asm)
           (rec_to_asm (dom stream_asm) all_f2i ∅ ∅ (rec_mod (<["stream" := stream_rec]> ∅))).
Proof. apply: (compile_correct 1000); [|done|..]; compute_done. Qed.

Lemma main_asm_refines_rec :
  trefines (asm_mod main_asm)
           (rec_to_asm (dom main_asm) all_f2i ∅ ∅ (rec_mod (<["main" := main_rec]> ∅))).
Proof. apply: (compile_correct 2000); [|done|..]; compute_done. Qed.

Definition main_spec : spec rec_event unit void :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "main");;
  TAssume (vs = []);;
  TVis (Outgoing, ERCall "print" [ValNum 0] h);;
  e ← TExist _;
  TVis (Incoming, e);;
  TAssume (if e is ERReturn _ _ then true else false);;
  TVis (Outgoing, ERCall "print" [ValNum 1] (heap_of_event e));;
  e ← TExist _;
  TVis (Incoming, e);;
  TAssume (if e is ERReturn _ _ then true else false);;
  TVis (Outgoing, ERReturn (ValNum 2) (heap_of_event e));;
  TUb.
Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma main_refines_spec :
  trefines (coro_link {["main"]} {["stream"]} "stream" (rec_mod main_prog) (rec_mod stream_prog))
    (spec_mod main_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=. unfold main_prog, stream_prog.
  tstep_i => *. destruct!/=.
  go_s. eexists (_, _, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|compute_done].
  tstep_i. split! => *. simplify_map_eq.
  tstep_i. split! => *. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split; [by econs|].
  tstep_i. split! => *. destruct!/=.
  tstep_i. split! => *. simplify_map_eq.
  tstep_i. split! => *. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split; [by econs|].
  tstep_i. split! => *. destruct!/=.
  tstep_i. split! => *. destruct!/=.
  tstep_i.
  tstep_i. split! => *. destruct!/=.
  rewrite bool_decide_true; [|compute_done].
  rewrite bool_decide_false; [|compute_done].
  go_s. split!. go.
  tstep_i => e *. destruct!.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s => ?. destruct e => //. go.
  tstep_i. split! => *. simplify_eq.
  tstep_i.
  tstep_i. split! => *. destruct!.
  tstep_i. split! => *. destruct!.
  tstep_i.
  tstep_i.
  tstep_i. split! => *. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split; [by econs|].
  tstep_i. split! => *. destruct!/=.
  tstep_i. split! => *. destruct!/=.
  tstep_i.
  tstep_i. split! => *. destruct!/=.
  rewrite bool_decide_true; [|compute_done].
  rewrite bool_decide_false; [|compute_done].
  go_s. split!. go.
  tstep_i => e *. destruct!.
  go_s. eexists _. go.
  go_s. split!. go.
  go_s => ?. destruct e => //. go.
  tstep_i. split! => *. simplify_eq.
  tstep_i.
  tstep_i. split! => *. destruct!.
  tstep_i. split! => *. destruct!.
  tstep_i.
  tstep_i.
  tstep_i. split! => *. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split; [by econs|].
  tstep_i. split! => *. destruct!/=.
  tstep_i. split! => *. destruct!/=.
  tstep_i. split!.
  tstep_i. split! => *. destruct!.
  go_s. split!. go.
  go_s. done.
Qed.

Definition stream_sp : Z := 20000.
Definition stream_ssz : N := 4098.
Definition stream_regs_init : gmap string Z :=
  <["SP" := stream_sp]> $
  <["PC" := stream_addr]> $
  ∅.

Definition top_level_spec : spec asm_event unit void :=
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));
  TAssume (rs !!! "PC" = main_addr);;
  TAssume (rs !!! "R30" ∉ yield_asm_dom ∪ main_asm_dom ∪ stream_asm_dom ∪ dom print_asm);;
  TAssume (∃ ssz,
     (r2a_mem_stack_mem (rs !!! "SP") ssz ##ₘ
       (r2a_mem_stack_mem (stream_regs_init !!! "SP") stream_ssz ∪ coro_regs_mem stream_regs_init)) ∧
    r2a_mem_stack_mem (rs !!! "SP") ssz ∪
    (r2a_mem_stack_mem (stream_regs_init !!! "SP") stream_ssz ∪ coro_regs_mem stream_regs_init) ⊆ mem);;
  args ← TExist _;
  mem ← TExist _;
  TAssert (print_args 0 args);;
  TVis (Outgoing, EASyscallCall args mem);;
  '(ret, mem') ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
  TAssume (mem' = mem);;
  args ← TExist _;
  mem ← TExist _;
  TAssert (print_args 1 args);;
  TVis (Outgoing, EASyscallCall args mem);;
  '(ret, mem') ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
  TAssume (mem' = mem);;
  rs' ← TExist _;
  mem' ← TExist _;
  TAssert (rs' !!! "PC" = rs !!! "R30");;
  TAssert (rs' !!! "R0" = 2);;
  TVis (Outgoing, EAJump rs' mem');;
  TUb.

Lemma top_level_refines_spec :
  trefines (asm_link (yield_asm_dom ∪ main_asm_dom ∪ stream_asm_dom) (dom print_asm)
              (rec_to_asm (yield_asm_dom ∪ main_asm_dom ∪ stream_asm_dom)
                all_f2i
                (r2a_mem_stack_mem (stream_regs_init !!! "SP") stream_ssz ∪ coro_regs_mem stream_regs_init) ∅
                (spec_mod main_spec tt)) (spec_mod print_spec tt))
           (spec_mod top_level_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct!/=.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go. simplify_map_eq'.
  go_s => Hret. go. rewrite !not_elem_of_union in Hret.
  go_s => -[?[??]]. go.
  rewrite bool_decide_true. 2: unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; by vm_compute.
  tstep_i => ??. simplify_eq.
  tstep_i. eexists true. split; [done|] => /=. eexists ∅, _, [], [], "main". split!.
  { simplify_map_eq'. unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; compute_done. } { rewrite !not_elem_of_union. naive_solver. }
  { apply: satisfiable_mono; [by eapply (r2a_res_init _ ∅ all_f2i)|].
    iIntros!. iDestruct select (r2a_mem_auth _) as "$". iFrame.
    iDestruct (big_sepM_subseteq with "[$]") as "?"; [done|].
    rewrite big_sepM_union; [|done]. iDestruct!. iFrame.
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
  go_i.
  go_i => *. destruct!.
  iSatStart. iIntros!.
  iDestruct (r2a_f2i_full_singleton with "[$] [$]") as %Hf2i.
  iDestruct (r2a_args_intro with "[$]") as "?"; [done|]. rewrite r2a_args_cons ?r2a_args_nil; [|done].
  iDestruct!. iSatStop.

  unfold all_f2i in Hf2i. simplify_map_eq'.
  rewrite bool_decide_false. 2: unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; by vm_compute.
  rewrite bool_decide_true. 2: compute_done.
  go_i.
  go_i => -[??]. go.
  go_i => *. go. simplify_eq.

  go_i. split!. go.
  go_i. split. {
    apply not_elem_of_dom.
    apply: not_elem_of_disjoint; [done|].
    unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; compute_done.
  } go.

  go_i => ?. go.
  go_i => ?. go.
  go_i => *. go. destruct!.

  go_s. eexists _. go. simplify_map_eq'.
  go_s. eexists _. go.
  go_s. split; [done|]. go.
  go_s. split; [done|]. go.

  go_i => *. case_match; destruct!.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.

  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i => *. go. destruct!; simplify_map_eq'. rewrite bool_decide_true; [|done].
  go_i => ??. simplify_eq.
  go_i. eexists false. split; [done|]. eexists _, _, [ValNum _]. split!. { by simplify_map_eq'. }
  { split. { by simplify_map_eq'. }
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    done. }
  { iSatMono. simplify_map_eq'. iFrame. iSplit; [done|]. iAccu. }
  iSatClear.

  go_i => *. go.
  go_i => *. simplify_eq. go.
  go_i => *. split!. go.
  go_i. go.
  go_i => *. destruct!.
  iSatStart. iIntros!.
  iDestruct (r2a_args_intro with "[$]") as "?"; [done|]. rewrite r2a_args_cons ?r2a_args_nil; [|done].
  iDestruct (r2a_f2i_full_singleton _ _ (_ !!! _) with "[$] [$]") as %Hf2i2.
  iDestruct!. iSatStop.

  unfold all_f2i in Hf2i2. simplify_map_eq'.
  rewrite bool_decide_false. 2: unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; by vm_compute.
  rewrite bool_decide_true. 2: compute_done.
  tstep_i. rewrite -/print_spec. go.
  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split. {
    apply not_elem_of_dom.
    apply: not_elem_of_disjoint; [done|].
    unfold yield_asm_dom, yield_asm, main_asm_dom, stream_asm_dom; unlock; compute_done.
  } go.
  go_i => ?. go.
  go_i => ?. go.
  go_i => *. go. destruct!.

  go_s. eexists _. go. simplify_map_eq'.
  go_s. eexists _. go. simplify_map_eq'.
  go_s. split; [done|]. go.
  go_s. split; [done|]. go.

  go_i => *. case_match; destruct!.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.

  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i => *. go. destruct!; simplify_map_eq'. rewrite bool_decide_true; [|done].
  go_i => ??. simplify_eq.
  go_i. eexists false. split; [done|]. eexists _, _, [ValNum _]. split!. { by simplify_map_eq'. }
  { split. { by simplify_map_eq'. }
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    done. }
  { iSatMono. simplify_map_eq'. iFrame. iSplit; [done|]. iAccu. }
  iSatClear.

  go_i => ?. go.
  go_i => ?. simplify_eq. go.
  go_i. split!. go.
  go_i.
  go_i => *. destruct!. case_bool_decide; [done|]. simplify_map_eq'.
  rewrite bool_decide_false. 2: { naive_solver. }

  go_s. eexists _. go.
  go_s. eexists _. go.
  go_s. split; [done|]. go.
  go_s. split. {
    unfold r2a_regs_ret in *. destruct!. simplify_map_eq'.
    iSatStart. iIntros!.
    iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[%?]". simplify_eq/=.
    iSatStop. done.
  } go.
  go_s. split!. go.
  go_s. done.
Qed.

Lemma complete_refinement :
  trefines (asm_mod (yield_asm ∪ (main_asm ∪ stream_asm) ∪ print_asm))
           (spec_mod top_level_spec tt).
Proof.
  etrans. {
    apply asm_syn_link_refines_link. rewrite /yield_asm. unlock. compute_done.
  }
  etrans. {
    apply: asm_link_trefines; [|done].
    apply asm_syn_link_refines_link. rewrite /yield_asm. unlock. compute_done.
  }
  etrans. {
    apply: asm_link_trefines; [|done].
    apply: asm_link_trefines; [done|].
    apply asm_syn_link_refines_link. compute_done.
  }
  etrans. {
    apply: asm_link_trefines.
    - etrans. {
        apply: asm_link_trefines; [done|].
        apply: asm_link_trefines.
        + apply main_asm_refines_rec.
        + apply stream_asm_refines_rec.
      }
      etrans. {
        rewrite dom_union_L.
        have ->: dom yield_asm = yield_asm_dom by rewrite /yield_asm_dom; unlock.
        apply (coro_spec "stream" stream_regs_init stream_ssz {["main"]} {["stream"]}).
        1, 2: apply _.
        all: unfold yield_asm_dom, yield_asm, r2a_mem_stack_mem; unlock.
        all: compute_done.
      }
      etrans. {
        apply rec_to_asm_trefines; [apply _|].
        apply: main_refines_spec.
      }
      done.
    - apply print_asm_refines_spec.
  }
  etrans. {
    etrans; [|apply top_level_refines_spec].
    rewrite idemp_L assoc_L 2!dom_union_L.
    rewrite /yield_asm_dom/main_asm_dom/stream_asm_dom. unlock.
    done.
  }
  done.
Qed.
