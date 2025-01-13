From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import asm.

Local Open Scope Z_scope.

(** * Library for calling the PRINT syscall *)

Definition __NR_PRINT : Z := 8.
Definition print_addr : Z := 500.

Definition print_args (z : Z) (args : list Z) : Prop :=
  length args = length syscall_arg_regs ∧
  args !! 0%nat = Some z ∧
  args !! 8%nat = Some __NR_PRINT.

Definition print_asm : gmap Z asm_instr :=
  deep_to_asm_instrs print_addr [
      Amov "R8" __NR_PRINT;
      (* Aadd "R0" "R0" 0; *)
      Asyscall;
      Aret
    ].

Definition print_asm' : gmap Z asm_instr :=
  deep_to_asm_instrs print_addr [
      Amov "R8" __NR_PRINT;
      Aadd "R0" "R0" 0;
      Asyscall;
      Aret
    ].

Definition print_spec : spec asm_event unit void :=
  Spec.forever (
    '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));
    TAssume (rs !!! "PC" = print_addr);;
    TAssume (print_asm !! (rs !!! "R30") = None);;
    (* NOTE What are the exact semantics here if I say exists and then assume.
       Is it the same as assume? - Think about what it means to refine this spec *)
    args ← TExist _;
    TAssert (print_args (rs !!! "R0") args);;
    TVis (Outgoing, EASyscallCall args mem);;
    '(ret, mem) ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
    TVis (Outgoing, EAJump (<["PC" := rs !!! "R30"]> $
                            <["R0" := ret]> $
                            <["R8" := __NR_PRINT]> $
                            rs) mem)).

Definition print_spec' : spec asm_event unit void :=
  Spec.forever (
    '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));
    TAssume (rs !!! "PC" = print_addr);;
    TAssume (print_asm' !! (rs !!! "R30") = None);;
    (* NOTE What are the exact semantics here if I say exists and then assume.
       Is it the same as assume? - Think about what it means to refine this spec *)
    args ← TExist _;
    TAssert (print_args (rs !!! "R0") args);;
    TVis (Outgoing, EASyscallCall args mem);;
    '(ret, mem) ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
    TVis (Outgoing, EAJump (<["PC" := rs !!! "R30"]> $
                            <["R0" := ret]> $
                            <["R8" := __NR_PRINT]> $
                            rs) mem)).

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma print_asm_refines_spec :
  trefines (asm_mod print_asm) (spec_mod print_spec tt).
Proof.
  apply: tsim_implies_trefines => n0.
  (* What does this simpl do here? *)
  simpl.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, _),
    t ≡ print_spec ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = print_asm). }
  { split!. } { done. }
  move => n _ Hloop [????] [??] ?. destruct!/=.
  tstep_i => ?? rs' ?? Hi. tstep_s. rewrite -/print_spec. go.
  go_s. eexists (_, _). go.
  (* Set Typeclasses Debug. *)
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  tstep_i => ? ?.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  go_s. sort_map_insert. simplify_map_eq'. split!. go.
  by apply: Hloop.
  Unshelve.
  - split; [done|by simplify_map_eq'].
Qed.

Lemma print_asm_refines_spec' :
  trefines (asm_mod print_asm') (spec_mod print_spec' tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, _),
    t ≡ print_spec' ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = print_asm'). }
  { split!. } { done. }
  move => n _ Hloop [????] [??] ?. destruct!/=.
  tstep_i => ?? rs' mem' ? Hi. tstep_s. rewrite -/print_spec. go.
  go_s. eexists (_, _). go.
  (* Set Typeclasses Debug. *)
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  tstep_i => ??. simplify_map_eq'.
  tstep_i.
  tstep_i.
  tstep_i => ??. simplify_map_eq'.
  set args := (extract_syscall_args (<["PC":=print_addr + 1 + 1]> (<["R8":=__NR_PRINT]> rs'))).
  go_s. eexists args. go.
  go_s. split; [shelve|]. go.
  (* Noop *)
  tstep_i. tstep_i. tstep_i => ??. simplify_map_eq'.
  (* Set Typeclasses Debug. *)
  tstep_i.
  go_s. split!.
  { f_equal. subst args. unfold extract_syscall_args. simpl. rewrite Z.add_0_r. by simplify_map_eq'. }
  go. tstep_i => ? ?.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  tstep_i. tstep_i => ? ?. simplify_map_eq'.
  tstep_i. tstep_i => ? ?. sort_map_insert. simplify_map_eq'.
  go_s. split!;[by sort_map_insert|].
  go.
  by apply: Hloop.
  Unshelve.
  - subst args. split; [done| by simplify_map_eq'].
Qed.
