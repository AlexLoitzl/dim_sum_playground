From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import spec_mod.
From dimsum.examples Require Import rec asm rec_to_asm print.
From dimsum.examples.compiler Require Import compiler.

Local Open Scope Z_scope.

(** * Example for implementing memmove using assembly for pointer comparison *)

(** * locle *)

Definition locle_addr : Z := 400.

Definition locle_asm : gmap Z asm_instr :=
  deep_to_asm_instrs locle_addr [
      Asle "R0" "R0" "R1";
      Aret
    ].

(* NOTE What's going on here *)
Definition locle_fns : gset string :=
  {["locle" ]}.

Definition locle_f2i : gmap string Z :=
  <["locle" := locle_addr]> $ ∅.

(* Events are parameterized by mapping from provenances to adresses? *)
(* The internal state is not at all fixed for rec. It can vary from program to program *)
Definition locle_spec_strong : spec rec_event (gmap prov Z) void :=
  Spec.forever (
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
      TAssume (f = "locle");;
      l1 ← TAll loc; l2 ← TAll loc;
      TAssume (vs = [ValLoc l1; ValLoc l2]);;
      ps ← TGet;
      z1 ← TExist Z;
      (* NOTE - If ps has already mapped provenance of l1, z1 is that otherwise True *)
      TAssert (z1 = default z1 (ps !! l1.1));;
      TPut (<[l1.1 := z1]> ps);;

      ps ← TGet;
      z2 ← TExist Z;
      TAssert (z2 = default z2 (ps !! l2.1));;
      TPut (<[l2.1 := z2]> ps);;

      TVis (Outgoing, ERReturn (ValBool (bool_decide (z1 + l1.2 ≤ z2 + l2.2))) h)
    ).

Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

(* NOTE: What does this Lemma mean:
    ⟦locle⟧ < ⎡⟦locle_spec⟧⎤
    Wrapper needs arguments:
    1: Probaly almost length?
    2: Where are the function definitions
    3: Mapping of (part of) the memory that is required
    4: Mapping of (part of) the heap that is required
    5: spec_module (which in turn takes specifaction and (in the case of locle) a mapping of provenances to their location in memory)
 *)

Lemma locle_asm_refines_spec_strong :
  trefines (asm_mod locle_asm)
           (rec_to_asm (dom locle_asm) locle_f2i ∅ ∅
              (spec_mod locle_spec_strong ∅)).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(σf, (t, ps), (pp, σr2a, P)),
    ∃ rP, P = uPred_shrink rP ∧
    t ≡ locle_spec_strong ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = locle_asm ∧
    σr2a.(r2a_calls) = [] ∧
    σf = SMFilter ∧
    pp = PPOutside ∧
    (rP ⊢ r2a_f2i_incl locle_f2i (dom locle_asm) ∗ [∗ map] p↦z∈ps, r2a_heap_shared p z)). }
  { split!. iIntros!. iFrame "#". by rewrite big_sepM_empty. } { done. }
  move => n _ Hloop [????] [[?[? ps]][[??]?]] ?. destruct!/=.
  tstep_i => ????? Hi. tstep_s. split!.
  tstep_i => ??. simplify_map_eq'.
  tstep_s => *. case_match => /= *. 2: congruence.
  tstep_s. rewrite -/locle_spec_strong. go. go_s. eexists (_, _, _). go.
  go_s. split!. go.
  go_s => ?. go.
  revert select (_ ⊢ _) => HP.
  revert select (_ ∉ dom _) => /not_elem_of_dom?.
  iSatStart. rewrite HP. iIntros!. iDestruct select (r2a_f2i_incl locle_f2i _) as "Hf2i".
  iDestruct (r2a_f2i_incl_in_ins with "Hf2i [$]") as %?; [done|]. iSatStop.
  unfold locle_f2i in *. cbn in Hi. unfold Z.succ in Hi.
  simplify_map_eq'.
  tstep_i.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  tstep_i. simplify_map_eq'.
  go_s => l1. go.
  go_s => l2. go.
  go_s => ?. go. simplify_eq.
  iSatStart. iIntros!.
  iDestruct (r2a_args_intro with "[$]") as "Hargs"; [done|]. rewrite !r2a_args_cons; [|done..].
  iDestruct "Hargs" as "([%z1 [% Hl1]] & [%z2 [% Hl2]] & ?)".
  iSatStop.
  go_s.
  go_s. eexists z1. go.
  go_s. split.
  { iSatStart. iDestruct (r2a_heap_shared_ag_big with "[$] Hl1") as %?. iSatStop. done. }
  go.
  go_s.
  iSatStart.
  iAssert ([∗ map] p↦z ∈ <[l1.1 := z1]>ps, r2a_heap_shared p z)%I as "#Hps'".
  { by iApply (big_sepM_insert_2 with "Hl1"). }
  iSatStop.
  go_s.
  go_s. eexists z2. go.
  go_s. split.
  { iSatStart. iDestruct (r2a_heap_shared_ag_big with "Hps' Hl2") as %?. iSatStop. done. }
  go.
  go_s.
  tstep_i => ??. simplify_map_eq'.
  go_s.
  go_s. split!.
  - by simplify_map_eq'.
  - instantiate (1 := [_]). unfold r2a_regs_ret; split!; simplify_map_eq'; split!.
    apply map_preserved_insert_r_not_in; [compute_done|].
    apply map_preserved_insert_r_not_in; [compute_done|].
    done.
  - apply map_scramble_insert_r_in; [compute_done|].
    apply map_scramble_insert_r_in; [compute_done|].
    done.
  - iSatMono. simplify_map_eq'. iFrame. iSplit!. iDestruct "Hps'" as "-#Hps'". iAccu.
  - apply: Hloop; [done|]. split!.
    iIntros!. iFrame "#". by iApply (big_sepM_insert_2 with "[] [$]").
Qed.

Definition locle_spec : spec rec_event unit void :=
  Spec.forever (
      '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
      TAssume (f = "locle");;
      l1 ← TAll loc; l2 ← TAll loc;
      TAssume (vs = [ValLoc l1; ValLoc l2]);;
      b ← TExist _;
      TAssert (l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2));;
      TVis (Outgoing, ERReturn (ValBool b) h)).

Lemma locle_spec_strong_refines_spec :
  trefines (spec_mod locle_spec_strong ∅)
           (spec_mod locle_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(t1, ps) '(t2, _),
    t1 ≡ locle_spec_strong ∧
    t2 ≡ locle_spec). }
  { split!. } { done. }
  move => n _ Hloop [??] [??] ?. destruct!/=.
  go_i. go_s. fold locle_spec_strong in *. fold locle_spec in *.
  go_i => -[[??]?]. go.
  go_i.
  go_s. eexists (_, _, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split!. go.
  go_i. split!. go.
  go_i. split!. go.
  go_i.
  go_i => ?. go.
  go_i => ?. go.
  go_i.
  go_i.
  go_i => ?. go.
  go_i => Hz2. go.
  go_i.
  go_i.
  go_s. eexists _. go.
  go_s. split; [shelve|]. go.
  go_s. split!. go.
  by apply: Hloop.
  Unshelve.
  - move => Heq. rewrite Heq in Hz2. simplify_map_eq. repeat case_bool_decide; lia.
Qed.

Lemma locle_asm_refines_spec :
  trefines (asm_mod locle_asm)
           (rec_to_asm (dom locle_asm) locle_f2i ∅ ∅ (spec_mod locle_spec tt)).
Proof.
  etrans; [apply locle_asm_refines_spec_strong|].
  apply rec_to_asm_trefines; [apply _|].
  apply: locle_spec_strong_refines_spec.
Qed.

(** * Rec code *)

Definition memmove_rec : fndef := {|
  fd_args := ["d"; "s"; "n"];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := If (rec.Call (Val (ValFn "locle")) [Var "d"; Var "s"])
                (rec.Call (Val (ValFn "memcpy")) [Var "d"; Var "s"; Var "n"; Val $ ValNum 1])
                (rec.Call (Val (ValFn "memcpy")) [
                     BinOp (Var "d") OffsetOp (BinOp (Var "n") AddOp (Val $ ValNum (-1)));
                     BinOp (Var "s") OffsetOp (BinOp (Var "n") AddOp (Val $ ValNum (-1)));
                     Var "n"; Val $ ValNum (-1)]);
  fd_static := I
|}.
Definition memmove_prog : gmap string fndef :=
  <["memmove" := memmove_rec]> $ ∅.


Definition memcpy_rec : fndef := {|
  fd_args := ["d"; "s"; "n"; "o"];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := If (BinOp (Val $ ValNum 0) LtOp (Var "n"))
               (LetE "_" (Store (Var "d") (Load (Var "s"))) $
                rec.Call (Val (ValFn "memcpy")) [
                  BinOp (Var "d") OffsetOp (Var "o");
                  BinOp (Var "s") OffsetOp (Var "o");
                  BinOp (Var "n") AddOp (Val $ ValNum (-1));
                  Var "o"])
               (Val 0);
  fd_static := I
|}.
Definition memcpy_prog : gmap string fndef :=
  <["memcpy" := memcpy_rec]> $ ∅.

Definition main_addr : Z := 50.

Definition main_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [("x", 3)];
  fd_body := LetE "_" (Store (BinOp (Var "x") OffsetOp (Val $ ValNum 0)) (Val $ ValNum 1)) $
             LetE "_" (Store (BinOp (Var "x") OffsetOp (Val $ ValNum 1)) (Val $ ValNum 2)) $
             LetE "_" (rec.Call (Val (ValFn "memmove")) [
                           BinOp (Var "x") OffsetOp (Val $ ValNum 1);
                           BinOp (Var "x") OffsetOp (Val $ ValNum 0);
                           (Val $ ValNum 2)]) $
             LetE "_" (rec.Call (Val (ValFn "print")) [
                           Load (BinOp (Var "x") OffsetOp (Val $ ValNum 1))]) $
             LetE "_" (rec.Call (Val (ValFn "print")) [
                           Load (BinOp (Var "x") OffsetOp (Val $ ValNum 2))]) $
             (Val $ ValNum 0);
  fd_static := I
|}.
Definition main_prog : gmap string fndef :=
  <["main" := main_rec]> $ ∅.

Definition main_f2i : gmap string Z :=
  <["main" := main_addr]> $
  <["memmove" := 200]> $
  <["memcpy"  := 300]> $
  <["print"  := print_addr]> $
  locle_f2i.

Definition main_asm : gmap Z asm_instr :=
  deep_to_asm_instrs main_addr ltac:(r2a_compile main_f2i 1000 main_rec).

Definition memmove_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 200 ltac:(r2a_compile main_f2i 2000 memmove_rec).

Definition memcpy_asm : gmap Z asm_instr :=
  deep_to_asm_instrs 300 ltac:(r2a_compile main_f2i 3000 memcpy_rec).

Definition main_asm_dom : gset Z := locked dom main_asm.
Definition memmove_asm_dom : gset Z := locked dom memmove_asm.
Definition memcpy_asm_dom : gset Z := locked dom memcpy_asm.

Lemma main_asm_refines_rec :
  trefines (asm_mod main_asm)
           (rec_to_asm main_asm_dom main_f2i ∅ ∅ (rec_mod main_prog)).
Proof.
  unfold main_asm_dom; unlock.
  apply: (compile_correct 1000); [|done|..]; compute_done.
Qed.

Lemma memmove_asm_refines_rec :
  trefines (asm_mod memmove_asm)
           (rec_to_asm memmove_asm_dom main_f2i ∅ ∅ (rec_mod memmove_prog)).
Proof.
  unfold memmove_asm_dom; unlock.
  apply: (compile_correct 2000); [|done|..]; compute_done.
Qed.

Lemma memcpy_asm_refines_rec :
  trefines (asm_mod memcpy_asm)
           (rec_to_asm memcpy_asm_dom main_f2i ∅ ∅ (rec_mod memcpy_prog)).
Proof.
  unfold memcpy_asm_dom; unlock.
  apply: (compile_correct 3000); [|done|..]; compute_done.
Qed.

Lemma memcpy_spec n0 d s d' s' n o K e h m σ1 σ2 b cs hvs `{!RecExprFill e K
      (rec.Call (Val (ValFn "memcpy")) [Val (ValLoc d); Val (ValLoc s); Val (ValNum n); Val o])}:
  n = Z.of_nat (length hvs) →
  o = 1 ∨ o = -1 →
  d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
  s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
  (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
  (∀ i v, hvs !! i = Some v → h_heap h !! (s' +ₗ Z.of_nat i) = Some v) →
  (∀ i v, hvs !! i = Some v → heap_alive h (d' +ₗ Z.of_nat i)) →
  ((MLFRun (Some SPLeft), cs, Rec (expr_fill K (Val (ValNum 0)))
                   (heap_update_big h (kmap (λ i, d' +ₗ i) (map_seqZ 0 hvs)))
                   (memmove_prog ∪ memcpy_prog), σ1)
    ⪯{rec_link_trans {["memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()), m, n0, true}
  σ2) →
  (MLFRun (Some SPLeft), cs, Rec e h (memmove_prog ∪ memcpy_prog), σ1)
    ⪯{rec_link_trans {["memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()), m, n0, b}
  σ2.
Proof.
  elim/o_lt_ind: n0 b d d' s s' n h hvs e K RecExprFill0 => n1 IH b d d' s s' n h hvs e K [->] ? Ho ?? Hle Hhvs Halive Hcont. subst.
  tstep_i. split! => *. simplify_map_eq. split!.
  tstep_i. move => ?? [??]. simplify_eq. split!.
  tstep_i. split!.
  tstep_i. case_bool_decide (_ < _). 2: {
    tstep_i. split!. destruct hvs; [|done]. simplify_eq/=.
    move: Hcont. rewrite kmap_empty heap_update_big_empty. done.
  }
  destruct Ho; simplify_eq/=; repeat case_bool_decide => //.
  - destruct hvs; [done|].
    have := Hhvs 0%nat _ ltac:(done). rewrite offset_loc_0 => ?.
    have := Halive 0%nat _ ltac:(done). rewrite offset_loc_0 => ?.
    tstep_i. split!.
    tstep_i. split!.
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    have ->: (S (length hvs) + -1) = (length hvs) by lia.
    apply: tsim_mono_to_tiS => ??. apply: IH; [done|done|by left|done|done|..].
    { move => /= /Hle. lia. }
    { move => i v' ? /=. rewrite -offset_loc_S.
      rewrite lookup_alter_ne; [by apply: Hhvs|].
      destruct (decide (d.1 = s.1)); [|naive_solver].
      destruct d, s; rewrite /offset_loc => ?; simplify_eq/=.
      ogeneralize (Hle _); [done|lia].
    } { move => ???. apply heap_alive_update. rewrite -offset_loc_S. by apply: Halive. }
    simpl. tstep_i. split!.
    move: Hcont.
    rewrite /= kmap_insert offset_loc_0 heap_update_big_update.
    rewrite -insert_union_r. 2: {
      eapply lookup_kmap_None; [by apply _|].
      rewrite /offset_loc. move => ? /=?. destruct d; simplify_eq/=. apply lookup_map_seqZ_None. lia.
    }
    rewrite right_id_L.
    enough (kmap (λ i : Z, d +ₗ i) (map_seqZ (Z.succ 0) hvs) =@{gmap _ _}
            kmap (λ i : Z, d +ₗ 1 +ₗ i) (map_seqZ 0 hvs)) as ->. {
      move => ?. apply: tsim_mono; [done|]. etrans; [|done]. apply o_le_S.
    }
    apply map_eq => i. apply option_eq => v'. rewrite !lookup_kmap_Some.
    setoid_rewrite lookup_map_seqZ_Some. split; move => [j ?]; destruct!.
    + eexists (Z.pred j).
      rewrite Z.sub_pred_l -Z.sub_succ_r. split!; [|lia].
      rewrite /offset_loc/=. f_equal. lia.
    + eexists (Z.succ j).
      rewrite Z.sub_succ_r Z.sub_succ_l Z.pred_succ. split!; [|lia].
      rewrite /offset_loc/=. f_equal. lia.
  - destruct (snoc_inv hvs) as [|[v[hvs' ?]]]; [naive_solver|]. simplify_eq. tstep_i.
    move: Hhvs Halive. rewrite length_app /=.
    have -> : (- (length hvs' + 1)%nat + 1) = - length hvs' by lia.
    move => Hhvs Halive.
    have := Hhvs (length hvs') v.
    have := Halive (length hvs') v.
    rewrite lookup_app_r // Nat.sub_diag /= !offset_loc_add_sub; [|lia..]. move => ??.
    split!; [naive_solver|].
    tstep_i. split!; [naive_solver|].
    tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    have ->: ((length hvs' + 1)%nat + -1) = length hvs' by lia.
    apply: tsim_mono_to_tiS => ??. apply: IH; [done|done|by right|..].
    { have ->: d +ₗ -1 +ₗ (- length hvs' + 1) = d +ₗ (- length hvs'); [|done].
      rewrite /offset_loc /=. f_equal. lia. }
    { have ->: s +ₗ -1 +ₗ (- length hvs' + 1) = s +ₗ (- length hvs'); [|done].
      rewrite /offset_loc /=. f_equal. lia. }
    { move => /= /Hle. lia. }
    { move => i v' Hv' /=.  move: (Hv') => /(lookup_lt_Some _ _ _)?.
      rewrite lookup_alter_ne; [apply: Hhvs; apply lookup_app_Some; naive_solver|].
      destruct (decide (d.1 = s.1)); [|naive_solver].
      destruct d, s; rewrite /offset_loc => ?; simplify_eq/=.
      ogeneralize (Hle _); [done|lia].
    } { move => ???. apply heap_alive_update. apply: Halive. apply lookup_app_Some; naive_solver. }
    simpl. tstep_i. split!.
    move: Hcont.
    rewrite /= heap_update_big_update length_app /=.
    have -> : (- (length hvs' + 1)%nat + 1) = - length hvs' by lia.
    rewrite map_seqZ_app /= kmap_union kmap_insert kmap_empty offset_loc_add_sub //.
    move => ?. apply: tsim_mono; [done|]. etrans; [|done]. apply o_le_S.
Qed.

Definition memmove_spec : spec rec_event unit void :=
  Spec.forever (
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "memmove");;
    '(d, s, n) ← TAll _;
    TAssume (vs = [ValLoc d; ValLoc s; ValNum n]);;
    hvs ← TAll (list val);
    TAssume (n = Z.of_nat (length hvs));;
    TAssume (∀ i v, hvs !! i = Some v → h_heap h !! (s +ₗ Z.of_nat i) = Some v);;
    TAssume (∀ i v, hvs !! i = Some v → heap_alive h (d +ₗ Z.of_nat i));;
    TVis (Outgoing, ERReturn 0 (heap_update_big h (kmap (λ i, d +ₗ i) (map_seqZ 0 hvs))) );;
    TRet ()).

Lemma memmove_refines_spec :
  trefines (rec_link {["memmove"; "memcpy"]} {["locle"]} (rec_mod (memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
           (spec_mod memmove_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ '(σi, cs, Rec e h fns, (ti, _)) '(t, _),
    ti ≡ locle_spec ∧
    t ≡ memmove_spec ∧
    cs = [] ∧
    σi = MLFRun None ∧
    e = Waiting false ∧
    fns = (memmove_prog ∪ memcpy_prog)). }
  { split!. } { done. }
  move => n ? IH [[[??] [???]] [??]] [??] ?. destruct!.
  tstep_i => *. case_match; destruct!/=.
  go_s.
  go_s. eexists (_, _, _). rewrite -/memmove_spec. go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => -[[??]?]. go.
  go_s => ?. go.
  go_s => hvs. go.
  go_s => ?. go.
  go_s => Hhvs. go.
  go_s => ?. go.
  simplify_map_eq/=. case_bool_decide; [|done].
  tstep_i. split!. move => *. simplify_map_eq.
  tstep_i. split!. move => ??. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split!.
  tstep_i. split!. move => *. destruct!. repeat case_bool_decide => //.
  tstep_i. rewrite -/locle_spec. go.
  go_i => -[[??]?]. go.
  go_i => *. simplify_eq. go.
  go_i. split!. go.
  go_i. eexists _. go.
  go_i. eexists _. go.
  go_i. split!. go.
  go_i => b. go.
  go_i => Heq. go.
  go_i => *. destruct!. go.
  tstep_i. split!. move => *. simplify_eq.
  tstep_i.
  destruct b.
  - apply: memcpy_spec; [done|by left|by rewrite bool_decide_true|by rewrite bool_decide_true| |done|done|..].
    { rewrite bool_decide_true // => /Heq. case_bool_decide; lia. }
    simpl. tstep_i. split!.
    tstep_i. move => *. destruct!/=.
    go_s. split!. rewrite bind_ret_l. go.
    eapply IH; [done|]. split!.
  - tstep_i.
    tstep_i.
    tstep_i.
    tstep_i.
    apply: memcpy_spec; [done|by right|..].
    { rewrite bool_decide_false; [|done]. rewrite offset_loc_add_sub; [done|lia]. }
    { rewrite bool_decide_false; [|done]. rewrite offset_loc_add_sub; [done|lia]. }
    { rewrite bool_decide_false //= => /Heq. case_bool_decide; lia. }
    { done. }
    { done. }
    simpl. tstep_i. split!.
    tstep_i. move => *. destruct!/=.
    go_s. split!. rewrite bind_ret_l. go.
    eapply IH; [done|]. split!.
Qed.

Definition main_spec : spec rec_event unit void :=
  '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
  TAssume (f = "main");;
  TAssume (vs = []);;
  h' ← TExist _;
  TVis (Outgoing, ERCall "print" [ValNum 1] h');;
  e ← TExist _;
  TVis (Incoming, e);;
  TAssume (if e is ERReturn _ h'' then h' = h'' else false);;
  h' ← TExist _;
  TVis (Outgoing, ERCall "print" [ValNum 2] h');;
  e ← TExist _;
  TVis (Incoming, e);;
  TAssume (if e is ERReturn _ h'' then h' = h'' else false);;
  TUb.

Lemma main_refines_spec :
  trefines (rec_link {["main"]} {["memmove"; "memcpy"; "locle"]}
              (rec_mod main_prog) (spec_mod memmove_spec tt))
           (spec_mod main_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct!/=.
  go_s. eexists (_, _, _). rewrite -/main_spec. go.
  go_s. split!. go.
  go_s => ?. go. simplify_eq. rewrite bool_decide_true; [|done].
  go_s => ?. go.
  tstep_i. split! => ???? Hf ?. unfold main_prog in Hf. simplify_map_eq.
  tstep_i. split! => ? Hf. unfold main_prog in Hf. simplify_map_eq. split!.
  tstep_i => *. destruct!/=. split; [by repeat econs|].
  tstep_i. rewrite offset_loc_0.
  have ? : l.2 = 0 by destruct select (heap_is_fresh _ _) as [?[??]].
  tstep_i.
  split.
  { eapply heap_alive_alloc; [done|lia]. }
  tstep_i.
  tstep_i.
  tstep_i.
  split.
  { eapply heap_alive_update. eapply heap_alive_alloc; simpl; [done|lia]. }
  tstep_i.
  tstep_i.
  tstep_i.
  tstep_i.
  split! => *. destruct!/=.
  rewrite bool_decide_false; [|compute_done].
  rewrite bool_decide_true; [|compute_done].
  rewrite offset_loc_0 /=.

  tstep_i. rewrite -/memmove_spec. go.
  go_i => -[[??]?]. go.
  go_i => ?. go. simplify_eq/=.
  go_i. split!. go.
  go_i. eexists (_, _, _). go.
  go_i. split!. go.
  go_i. eexists ([ValNum 1; ValNum 2]). go.
  go_i. split!. go.
  go_i. split!.
  { move => -[|[|//]] /= ??; simplify_eq; rewrite ?offset_loc_0.
    - rewrite lookup_alter_ne.
      2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
      by rewrite lookup_alter heap_alloc_h_lookup/=; [..|lia].
    - rewrite lookup_alter lookup_alter_ne.
      2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
      by rewrite heap_alloc_h_lookup/=; [..|lia].
  }
  go.

  go_i. split!. {
    move => i ??. do 2 apply heap_alive_update.
    apply heap_alive_alloc => //=. destruct i as [|[|]] => //; lia.
  }
  go.

  go_i => ??????. destruct!. go.
  go_i. split! => *. destruct!.
  rewrite !kmap_insert kmap_empty.
  tstep_i.
  tstep_i.
  tstep_i.
  exists (ValNum 1). split. {
    rewrite !map_union_weak_insert map_union_weak_empty.
    rewrite offset_loc_0 lookup_alter lookup_alter_ne.
    2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
    rewrite lookup_alter lookup_alter_ne.
    2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
    by rewrite heap_alloc_h_lookup/=; [..|lia].
  }
  tstep_i. split! => *. destruct!.
  rewrite bool_decide_false; [|compute_done].
  go_s. split!. go.
  go_s. split!. go.
  tstep_i => e *. destruct!.

  destruct e; destruct!.
  { go_s. split!. go.
    go_s. split!. go.
    go_s. split!.
  }
  go_s. split!. go.
  go_s. split!. go.
  tstep_i.
  split! => *. simplify_eq.
  tstep_i.
  tstep_i.
  go_s => *. subst. go.
  tstep_i. split!.  {
    rewrite !map_union_weak_insert map_union_weak_empty.
    rewrite offset_loc_0 lookup_alter_ne.
    2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
    rewrite offset_loc_assoc lookup_alter lookup_alter_ne.
    2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
    rewrite lookup_alter_ne.
    2: { destruct l. rewrite /offset_loc /=. naive_solver lia. }
    by rewrite heap_alloc_h_lookup/=; [..|lia].
  }
  tstep_i. split!. intros. destruct!.
  rewrite bool_decide_false; [|compute_done].
  go_s. split!. go.
  go_s. split!. go.
  tstep_i => e *. destruct!.
  destruct e; destruct!.
  { go_s. split!. go.
    go_s. split!. go.
    go_s. split!.
  }
  go_s. split!. go.
  go_s. split!. go.
  tstep_i.
  split!. intros. simplify_eq.
  tstep_i.
  go_s. intros. subst. go.
  go_s. done.
Qed.

(** * Top-level specification *)

Definition top_level_spec : spec asm_event unit void :=
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));
  TAssume (rs !!! "PC" = main_addr);;
  TAssume (rs !!! "R30" ∉ main_asm_dom ∪ memmove_asm_dom ∪ memcpy_asm_dom ∪ dom locle_asm);;
  TAssume (∃ ssz, r2a_mem_stack_mem (rs !!! "SP") ssz ⊆ mem);;
  args ← TExist _;
  mem ← TExist _;
  TAssert (print_args 1 args);;
  TVis (Outgoing, EASyscallCall args mem);;
  '(ret, mem') ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
  TAssume (mem' = mem);;
  args ← TExist _;
  mem ← TExist _;
  TAssert (print_args 2 args);;
  TVis (Outgoing, EASyscallCall args mem);;
  '(ret, mem') ← TReceive (λ '(ret, mem), (Incoming, EASyscallRet ret mem));
  TAssume (mem' = mem);;
  TUb.

Lemma top_level_refines_spec :
  trefines (asm_link (main_asm_dom ∪ memmove_asm_dom ∪ memcpy_asm_dom ∪ dom locle_asm)
              (dom print_asm)
              (rec_to_asm (main_asm_dom ∪ memmove_asm_dom ∪ memcpy_asm_dom ∪ dom locle_asm)
                 main_f2i ∅ ∅ (spec_mod main_spec tt)) (spec_mod print_spec tt))
           (spec_mod top_level_spec tt).
Proof.
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct!/=.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go. simplify_map_eq'.
  go_s => ?. go.
  go_s => -[??]. go.
  rewrite bool_decide_true. 2: unfold main_asm_dom, memmove_asm_dom, memcpy_asm_dom; unlock; by vm_compute.
  tstep_i => ??. simplify_eq.
  tstep_i. eexists true. split; [done|] => /=. eexists ∅, _, [], [], "main". split!.
  { simplify_map_eq'. unfold main_asm_dom, memmove_asm_dom, memcpy_asm_dom. unlock. compute_done. }
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
  go_i => *. destruct!.
  iSatStart. iIntros!.
  iDestruct (r2a_args_intro with "[$]") as "?"; [done|]. rewrite r2a_args_cons ?r2a_args_nil; [|done].
  iDestruct (r2a_f2i_full_singleton with "[$] [$]") as %Hf2i.
  iDestruct!. iSatStop.

  unfold main_f2i in Hf2i. simplify_map_eq'.
  rewrite bool_decide_false. 2: done.
  rewrite bool_decide_true. 2: compute_done.
  tstep_i. rewrite -/print_spec. go.
  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split. {
    apply not_elem_of_dom.
    apply: not_elem_of_disjoint; [done|].
    unfold main_asm_dom, memmove_asm_dom, memcpy_asm_dom; unlock; compute_done.
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

  go_i => *. go.
  go_i => *. simplify_eq. go.
  go_i => *. split!. go.
  go_i => *. go.
  go_i.
  go_i => *. destruct!.
  iSatStart. iIntros!.
  iDestruct (r2a_args_intro with "[$]") as "?"; [done|]. rewrite r2a_args_cons ?r2a_args_nil; [|done].
  iDestruct (r2a_f2i_full_singleton _ _ (_ !!! _) with "[$] [$]") as %Hf2i2.
  iDestruct!. iSatStop.

  unfold main_f2i in Hf2i2. simplify_map_eq'.
  rewrite bool_decide_false. 2: done.
  rewrite bool_decide_true. 2: compute_done.
  tstep_i. rewrite -/print_spec. go.
  go_i => -[??]. go.
  go_i => ?. go. simplify_eq.
  go_i. split!. go.
  go_i. split. {
    apply not_elem_of_dom.
    apply: not_elem_of_disjoint; [done|].
    unfold main_asm_dom, memmove_asm_dom, memcpy_asm_dom; unlock; compute_done.
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
  by go_s.
Qed.

(** * Overall refinement *)

Lemma complete_refinement :
  trefines (asm_mod (main_asm ∪ memmove_asm ∪ memcpy_asm ∪ locle_asm ∪ print_asm))
           (spec_mod top_level_spec tt).
Proof.
  etrans. {
    have -> : (main_asm ∪ memmove_asm ∪ memcpy_asm ∪ locle_asm ∪ print_asm) =
             (main_asm ∪ (memmove_asm ∪ memcpy_asm ∪ locle_asm) ∪ print_asm) by rewrite 2!assoc_L.
    etrans. {
      apply asm_syn_link_refines_link. compute_done.
    }
    etrans. {
      apply: asm_link_trefines; [|done].
      etrans. { apply asm_syn_link_refines_link. compute_done. }
      apply: asm_link_trefines; [done|].
      etrans. { apply asm_syn_link_refines_link. compute_done. }
      apply: asm_link_trefines; [|done].
      apply asm_syn_link_refines_link. compute_done.
    }
    done.
  }
  etrans. {
    apply: asm_link_trefines; [|done].
    apply: asm_link_trefines; [apply main_asm_refines_rec|].
    apply: asm_link_trefines; [|done].
    apply: asm_link_trefines; [apply memmove_asm_refines_rec|apply memcpy_asm_refines_rec].
  }
  etrans. {
    apply: asm_link_trefines; [|apply print_asm_refines_spec].
    apply: asm_link_trefines; [done|].
    apply: asm_link_trefines; [done|apply locle_asm_refines_spec].
  }
  etrans. {
    etrans. {
      apply: asm_link_trefines; [|done].
      apply: asm_link_trefines; [done|].
      apply: asm_link_trefines; [|done].
      rewrite /memmove_asm_dom /memcpy_asm_dom. unlock.
      apply (rec_to_asm_combine _ _ {["memmove"]} {["memcpy"]}); [apply _|apply _|..]; compute_done.
    }
    rewrite idemp.
    etrans. {
      apply: asm_link_trefines; [|done].
      apply: asm_link_trefines; [done|].
      rewrite idemp -dom_union_L.
      apply (rec_to_asm_combine _ _ {["memmove"; "memcpy"]} {["locle"]}); [apply _|apply _|..]; compute_done.
    }
    rewrite idemp -dom_union_L.
    etrans. {
      apply: asm_link_trefines; [|done].
      rewrite /main_asm_dom. unlock.
      apply (rec_to_asm_combine _ _ {["main"]} ({["memmove"; "memcpy"; "locle"]})); [apply _|apply _|..]; compute_done.
    }
    done.
  }
  etrans. {
    etrans. {
      apply: asm_link_trefines; [|done].
      apply rec_to_asm_trefines; [apply _|].
      apply rec_link_trefines; [apply _|apply _|done|].
      apply rec_link_trefines; [apply _|apply _| |done].
      have -> : {["memmove"]} = dom memmove_prog by compute_done.
      have -> : {["memcpy"]} = dom memcpy_prog by compute_done.
      apply: rec_link_refines_syn_link.
      compute_done.
    }
    etrans. {
      apply: asm_link_trefines; [|done].
      apply rec_to_asm_trefines; [apply _|].
      apply rec_link_trefines; [apply _|apply _|done|].
      apply memmove_refines_spec.
    }
    done.
  }
  etrans. {
    apply: asm_link_trefines; [|done].
    apply rec_to_asm_trefines; [apply _|].
    apply main_refines_spec.
  }
  etrans. {
    etrans; [|apply top_level_refines_spec].
    rewrite /main_asm_dom/memmove_asm_dom/memcpy_asm_dom/locle_fns. unlock.
    rewrite -4!dom_union_L !assoc_L idemp_L.
    have -> : (main_f2i ∪ locle_f2i) = main_f2i by compute_done.
    assert ((∅ ∪ ∅) = ∅) as ->. by rewrite !left_id_L.
    done.
  }
  done.
Qed.

(* Print Assumptions complete_refinement. *)
(* Print Assumptions sim_trefines. *)
