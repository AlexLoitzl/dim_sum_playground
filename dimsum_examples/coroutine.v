From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import seq_product link spec_mod.
From dimsum.examples Require Import rec asm rec_to_asm.

Local Open Scope Z_scope.
Local Opaque map_union. (* without this simpl takes very long *)

(** * Coroutine library *)

(** * Preliminary definitions *)
Definition yield_addr : Z := 2000.

Definition coro_state_addr : Z := 3000.

Definition coro_saved_regs : list string := saved_registers ++ ["PC"].

Definition coro_get_regs (regs : gmap string Z) : list Z :=
  ((regs !!!.) <$> coro_saved_regs).
Arguments coro_get_regs : simpl never.

Definition coro_regs_mem_n (regs : gmap string Z) (n : nat) : gmap Z (option Z) :=
  map_seqZ coro_state_addr (Some <$> take n (coro_get_regs regs)).
Arguments coro_regs_mem_n : simpl never.

Definition coro_regs_mem (regs : gmap string Z) : gmap Z (option Z) :=
  coro_regs_mem_n regs (length coro_saved_regs).
Arguments coro_regs_mem : simpl never.

Definition coro_regs_regs_n (regs : gmap string Z) (n : nat) : gmap string Z :=
  list_to_map ((λ x, (x, regs !!! x)) <$> take n coro_saved_regs).
Arguments coro_regs_regs_n : simpl never.

Definition coro_regs_regs (regs : gmap string Z) : gmap string Z :=
  list_to_map ((λ x, (x, regs !!! x)) <$> coro_saved_regs).
Arguments coro_regs_regs : simpl never.

(** ** Lemmas about preliminary definitions *)
Lemma coro_saved_regs_length :
  length coro_saved_regs = 13%nat.
Proof. done. Qed.

Lemma coro_saved_regs_lookup_saved i :
  (i < 12)%nat →
  coro_saved_regs !! i = Some (saved_registers !!! i).
Proof. move => ?. do 12 (destruct i as [|i]; try done); lia. Qed.

Lemma coro_saved_regs_take_PC r :
  r ≠ "PC" →
  r ∈ take 12 coro_saved_regs ↔ r ∈ coro_saved_regs.
Proof. fast_set_solver. Qed.

Lemma coro_saved_regs_take_saved r i :
  (i < 12)%nat →
  r ≠ saved_registers !!! i →
  r ∈ take (i + 1) coro_saved_regs ↔ r ∈ take i coro_saved_regs.
Proof. cbn. repeat (destruct i as [|i] => /=; [fast_set_solver|try lia]). Qed.

Lemma coro_regs_regs_args_preserved rs rs':
 map_preserved args_registers rs (coro_regs_regs rs' ∪ rs).
Proof.
  rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  repeat (apply map_preserved_insert_r_not_in; [compute_done|]).
  done.
Qed.

Lemma coro_regs_regs_touched_scramble rs rs' rs'':
  map_scramble touched_registers rs rs' →
  map_scramble touched_registers rs (coro_regs_regs rs'' ∪ rs').
Proof.
  move => ?.
  rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  repeat (apply map_scramble_insert_r_in; [compute_done|]).
  done.
Qed.

Lemma coro_regs_regs_saved_preserved rs rs' rs'':
  map_preserved saved_registers rs rs'' →
  map_preserved saved_registers rs (coro_regs_regs rs'' ∪ rs').
Proof.
  move => Hp. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  repeat (apply map_preserved_insert_r_in; [compute_done|]; split; [apply: Hp; compute_done|]).
  apply map_preserved_insert_r_not_in; [compute_done|].
  apply map_preserved_nil'. compute_done.
Qed.

Lemma coro_regs_mem_dom rs rs':
  dom (coro_regs_mem rs) = dom (coro_regs_mem rs').
Proof.
  rewrite /coro_regs_mem/coro_get_regs. cbn. rewrite !dom_insert_L. done.
Qed.

Lemma coro_regs_regs_lookup_in r rs rs' :
  r ∈ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs !!! r.
Proof.
  move => ?. set_unfold. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  destruct!.
  all: repeat (rewrite lookup_total_insert_ne; [|done]).
  all: by rewrite lookup_total_insert.
Qed.

Lemma coro_regs_regs_lookup_not_in r rs rs' :
  r ∉ "PC"::saved_registers →
  (coro_regs_regs rs ∪ rs') !!! r = rs' !!! r.
Proof.
  move => ?. set_unfold. rewrite /coro_regs_regs. cbn.
  rewrite -!insert_union_l left_id_L.
  by repeat (rewrite lookup_total_insert_ne; [|naive_solver]).
Qed.
Opaque coro_saved_regs.

Lemma coro_regs_regs_lookup_Some rs r v:
  coro_regs_regs rs !! r = Some v ↔ r ∈ coro_saved_regs ∧ v = rs !!! r.
Proof.
  rewrite /coro_regs_regs -elem_of_list_to_map; [|compute_done].
  rewrite elem_of_list_fmap. naive_solver.
Qed.

Lemma coro_regs_regs_n_lookup_Some rs r v i:
  coro_regs_regs_n rs i !! r = Some v ↔ r ∈ take i coro_saved_regs ∧ v = rs !!! r.
Proof.
  rewrite /coro_regs_regs_n.
  rewrite -elem_of_list_to_map.
  2: { rewrite -list_fmap_compose. apply NoDup_fmap.
       2: { do 15 (destruct i as [|i]; [compute_done|]). compute_done. }
       move => ?? /=?. done. }
  rewrite elem_of_list_fmap. naive_solver.
Qed.

Lemma coro_regs_regs_lookup_None rs r:
  coro_regs_regs rs !! r = None ↔ r ∉ coro_saved_regs.
Proof. rewrite eq_None_not_Some /is_Some. setoid_rewrite coro_regs_regs_lookup_Some. naive_solver. Qed.

Lemma coro_regs_regs_n_lookup_None rs r i:
  coro_regs_regs_n rs i !! r = None ↔ r ∉ take i coro_saved_regs.
Proof. rewrite eq_None_not_Some /is_Some. setoid_rewrite coro_regs_regs_n_lookup_Some. naive_solver. Qed.

Lemma coro_get_regs_lookup_Some rs i v :
  coro_get_regs rs !! i = Some v ↔ ∃ r, coro_saved_regs !! i = Some r ∧ v = rs !!! r.
Proof. by rewrite /coro_get_regs list_lookup_fmap fmap_Some. Qed.

Lemma coro_regs_mem_n_lookup_Some (k : nat) rs (i : nat) j  v:
  i ≤ 13 →
  j = coro_state_addr + k →
  coro_regs_mem_n rs i !! j = Some (Some v) ↔
    ∃ r, coro_saved_regs !! k = Some r ∧ k < i ∧ v = rs !!! r.
Proof.
  move => ??. subst.
  rewrite /coro_regs_mem_n lookup_map_seqZ_Some list_lookup_fmap fmap_Some.
  setoid_rewrite lookup_take_Some. setoid_rewrite coro_get_regs_lookup_Some.
  have ->: Z.to_nat (coro_state_addr + k - coro_state_addr) = k by lia.
  split => ?; destruct!; split!; lia.
Qed.

Lemma coro_regs_mem_lookup_Some (k : nat) rs j  v:
  j = coro_state_addr + k →
  coro_regs_mem rs !! j = Some (Some v) ↔
    ∃ r, coro_saved_regs !! k = Some r ∧ k < 13 ∧ v = rs !!! r.
Proof. move => ?. rewrite /coro_regs_mem coro_regs_mem_n_lookup_Some //. Qed.

Lemma coro_regs_mem_n_lookup_None rs i j:
  coro_regs_mem_n rs i !! j = None ↔ j < coro_state_addr ∨ coro_state_addr + (i `min` 13) ≤ j.
Proof.
  rewrite /coro_regs_mem_n lookup_map_seqZ_None length_fmap length_take.
  rewrite /coro_get_regs length_fmap coro_saved_regs_length. lia.
Qed.

Lemma coro_regs_mem_n_insert rs (i : nat) v r:
  coro_saved_regs !! i = Some r →
  <[coro_state_addr + i := Some v]> (coro_regs_mem_n rs i) =
    coro_regs_mem_n (<[r := v]> rs) (i + 1).
Proof.
  move => Hk. move: (Hk) => /(lookup_lt_Some _ _ _). rewrite coro_saved_regs_length => ?.
  apply map_eq => k.
  destruct (decide (k = coro_state_addr + i)); simplify_map_eq.
  - symmetry. eapply coro_regs_mem_n_lookup_Some; [lia|done|]. split!; [lia|by simplify_map_eq'].
  - rewrite /coro_regs_mem_n !lookup_map_seqZ. apply option_eq => ?. case_guard; [|done].
    rewrite !list_lookup_fmap !fmap_Some.
    setoid_rewrite lookup_take_Some.
    setoid_rewrite coro_get_regs_lookup_Some.
    split => ?; destruct!; split!; try lia; rewrite lookup_total_insert_ne // => ?; subst.
    all: have /NoDup_alt Hx : NoDup coro_saved_regs by compute_done.
    all: exploit Hx; [exact: Hk| done| ]; lia.
Qed.

Lemma coro_regs_mem_n_rs_eq rs1 rs2 n :
  (∀ i, rs1 !!! i = rs2 !!! i) →
  coro_regs_mem_n rs1 n = coro_regs_mem_n rs2 n.
Proof.
 move => Heq.
 rewrite /coro_regs_mem_n/coro_get_regs.
 f_equal. f_equal. f_equal. by apply list_fmap_ext.
Qed.

Lemma coro_regs_mem_n_0 rs :
  coro_regs_mem_n rs 0 = ∅.
Proof. done. Qed.

Lemma coro_regs_regs_n_0 rs :
  coro_regs_regs_n rs 0 = ∅.
Proof. done. Qed.

(** * [yield] library  *)
(** ** Implementation of [yield]  *)
Definition yield_swap_reg (r : string) (o : Z) : list deep_asm_instr := [
    Aload "R16" "R17" o;
    Astore r "R17" o;
    Amov r "R16"
  ].

Definition yield_asm: gmap Z asm_instr := deep_to_asm_instrs yield_addr ([
  Amov "R17" coro_state_addr;
  Amov "R16" 0] ++ (* dummy *)
  mjoin (imap (λ i r, yield_swap_reg r (Z.of_nat i)) (locked saved_registers)) ++ [
  Aload "R16" "R17" (Z.of_nat $ length saved_registers);
  Astore "R30" "R17" (Z.of_nat $ length saved_registers);
  Abranch true "R16"]).

Definition yield_asm_dom : gset Z := locked dom yield_asm.

(** ** Specification of [yield]  *)
Definition yield_spec : spec asm_event (gmap string Z) void :=
  Spec.forever (
  '(rs, mem) ← TReceive (λ '(rs, mem), (Incoming, EAJump rs mem));
  TAssume (rs !!! "PC" = yield_addr);;
  TAssume (rs !!! "R30" ∉ yield_asm_dom);;
  rsold ← TGet;
  TAssume (coro_regs_mem rsold ⊆ mem);;
  let rs' := (<["PC" := rs !!! "R30"]> rs) in
  TPut rs';;
  r16 ← TExist Z;
  r17 ← TExist Z;
  TVis (Outgoing, EAJump
                    (<["R16" := r16]> $ <["R17" := r17]> $ (coro_regs_regs rsold ∪ rs))
                    (coro_regs_mem rs' ∪ mem))).

(** ** Verification of [yield]  *)
Local Ltac go :=
  clear_spec.
Local Ltac go_s :=
  tstep_s; go.
Local Ltac go_i :=
  tstep_i; go.

Lemma yield_asm_refines_spec regs :
  regs !!! "PC" ∉ yield_asm_dom →
  trefines (asm_mod yield_asm) (spec_mod yield_spec regs).
Proof.
  move => ?. apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, rs),
    t ≡ yield_spec ∧
    σa.(asm_cur_instr) = AWaiting ∧
    σa.(asm_instrs) = yield_asm ∧
    rs !!! "PC" ∉ yield_asm_dom). }
  { split!. } { done. }
  move => n _ Hloop [????] [? rsold] ?. destruct!/=.
  tstep_i => ?? rs mem ? Hi. simpl.
  tstep_s. rewrite -/yield_spec. go.
  go_s. eexists (_, _). go.
  go_s. split!. go.
  go_s => ?. go.
  go_s => ?. go.
  go_s.
  go_s => ?. go.
  go_s.
  tstep_i => ??. simplify_map_eq'.
  rewrite /yield_asm deep_to_asm_instrs_cons in Hi. simplify_map_eq.
  tstep_i.
  tstep_i. simplify_map_eq'.
  tstep_i => ??. simplify_map_eq'.
  rewrite (deep_to_asm_instrs_lookup_nat 1) /=; [|lia].
  tstep_i.
  tstep_i. simplify_map_eq'.
  rename select (spec _ _ _) into t'.
  unshelve eapply tsim_remember. { simpl. exact (λ _ σa '(t, rs'),
    ∃ (n : nat) r16,
    n ≤ length saved_registers ∧
    t = t' ∧
    σa.(asm_cur_instr) = (ARunning []) ∧
    σa.(asm_regs) = <["PC" := yield_addr + (2 + n * 3)]> $
                    <["R16" := r16]> $
                    <["R17" := coro_state_addr]> $
                    coro_regs_regs_n rsold n ∪ rs ∧
    σa.(asm_mem) = coro_regs_mem_n rs n ∪ coro_regs_mem rsold ∪ mem ∧
    σa.(asm_instrs) = yield_asm ∧
    rs' = <["PC":=rs !!! "R30"]> rs ). }
  { eexists 0%nat. split!; simplify_map_eq' => //.
    { apply map_eq => i.
      destruct (decide (i = "PC")); simplify_map_eq; [f_equal; lia|].
      destruct (decide (i = "R16")); simplify_map_eq; [done|].
      destruct (decide (i = "R17")); simplify_map_eq; [done|].
      by rewrite coro_regs_regs_n_0 left_id_L. }
   { rewrite coro_regs_mem_n_0 left_id_L. symmetry. by apply map_subseteq_union. } }
  { done. }
  move => n1 ? Hloop2 [? rs' ??] [??] [i ?]. destruct!/=.
  tstep_i => ??. simplify_map_eq'.
  rewrite (deep_to_asm_instrs_lookup_nat (S (S (i * 3)))) /=; [|lia].
  have Hlen: length (mjoin (imap (λ (i : nat) (r : string), yield_swap_reg r i) (locked saved_registers))) = 36%nat.
  { by unlock. }
  destruct (decide (i = 12%nat)); subst.
  - repeat match goal with | H : context [take 12 saved_registers] |- _ => rewrite take_ge in H; [|done] end.
    rewrite lookup_app_r Hlen //=.
    tstep_i. simplify_map_eq'. split!.
    tstep_i.
    tstep_i => ??. simplify_map_eq'.
    rewrite (deep_to_asm_instrs_lookup_nat (S (S (S (12 * 3))))) /=; [|lia].
    rewrite lookup_app_r Hlen /=; [|lia].
    tstep_i. simplify_map_eq'. split!. sort_map_insert. rewrite 2!insert_insert.
    tstep_i. simplify_map_eq'.
    tstep_i => ??. simplify_map_eq'.
    rewrite (deep_to_asm_instrs_lookup_nat (S (S (S (S (12 * 3)))))) /=; [|lia].
    rewrite lookup_app_r Hlen /=; [|lia].
    tstep_i. simplify_map_eq'.
    tstep_i => ??. simplify_map_eq'.
    rewrite not_elem_of_dom_1.
    2: { revert select (rsold !!! "PC" ∉ yield_asm_dom). unfold yield_asm_dom. by unlock. }
    go_s. eexists _. go.
    go_s. eexists _. go.
    go_s. split!. {
      apply map_eq => i.
      destruct (decide (i = "R16")); simplify_map_eq; [done|].
      destruct (decide (i = "R17")); simplify_map_eq; [done|].
      destruct (decide (i = "PC")). 1: by simplify_map_eq.
      repeat (rewrite lookup_insert_ne; [|done]).
      destruct (coro_regs_regs rsold !! i) eqn: Heq.
      * rewrite lookup_union_l' // Heq. symmetry. apply lookup_union_Some_l.
        move: Heq => /coro_regs_regs_lookup_Some[??].
        apply coro_regs_regs_n_lookup_Some. split!.
        by rewrite coro_saved_regs_take_PC.
      * rewrite lookup_union_r // lookup_union_r //.
        move: Heq => /coro_regs_regs_lookup_None?.
        apply coro_regs_regs_n_lookup_None. split!.
        by rewrite coro_saved_regs_take_PC.
    } {
      rewrite !insert_union_l.
      erewrite coro_regs_mem_n_insert; [|done].
      rewrite !lookup_total_alt. by rewrite lookup_union_r.
    } go.
    apply: Hloop. { etrans; [|done]. apply o_le_S. }
    split!. by simplify_map_eq'.
  - rewrite lookup_app_l ?Hlen //=.
    have ->: (i * 3)%nat = (i * 3 + 0)%nat by lia.
    erewrite join_lookup_Some_same_length_2.
    2: { apply Forall_forall => ? /elem_of_lookup_imap. naive_solver. }
    2: { lia. }
    2: { apply list_lookup_imap_Some. split!. apply list_lookup_lookup_total_lt. unlock => /=. lia. }
    2: { done. }
    2: { lia. }
    simpl.
    tstep_i. simplify_map_eq'. split!. {
      apply lookup_union_Some_l. apply lookup_union_Some_raw. right.
      split.
      - apply coro_regs_mem_n_lookup_None. lia.
      - eapply coro_regs_mem_lookup_Some; [done|]. split!; [|lia].
        apply coro_saved_regs_lookup_saved. lia.
    } simpl.
    tstep_i.
    tstep_i => ??. simplify_map_eq'.
    rewrite (deep_to_asm_instrs_lookup_nat (S (S (i * 3 + 1)))) /=; [|lia].
    rewrite lookup_app_l ?Hlen /=; [|lia].
    erewrite join_lookup_Some_same_length_2.
    2: { apply Forall_forall => ? /elem_of_lookup_imap. naive_solver. }
    2: { lia. }
    2: { apply list_lookup_imap_Some. split!. apply list_lookup_lookup_total_lt. unlock => /=. lia. }
    2: { done. }
    simpl.
    tstep_i. simplify_map_eq'. split!. {
      apply lookup_union_Some_l. apply lookup_union_Some_raw. right.
      split.
      - apply coro_regs_mem_n_lookup_None. lia.
      - eapply coro_regs_mem_lookup_Some; [done|]. split!; [|lia].
        apply coro_saved_regs_lookup_saved. lia.
    } simpl. unlock.
    tstep_i. simplify_map_eq'.
    rewrite lookup_total_insert_ne.
    2: { do 12 (destruct i as [|i]; try done). }
    rewrite lookup_total_insert_ne.
    2: { do 12 (destruct i as [|i]; try done). }
    tstep_i => ??. simplify_map_eq'.
    rewrite (deep_to_asm_instrs_lookup_nat (S (S (i * 3 + 2)))) /=; [|lia].
    rewrite lookup_app_l ?Hlen /=; [|lia].
    erewrite join_lookup_Some_same_length_2.
    2: { apply Forall_forall => ? /elem_of_lookup_imap. naive_solver. }
    2: { lia. }
    2: { apply list_lookup_imap_Some. split!. apply list_lookup_lookup_total_lt. unlock => /=. lia. }
    2: { done. }
    simpl. unlock.
    tstep_i. simplify_map_eq'.
    tstep_i. rewrite lookup_total_insert_ne.
    2: { do 12 (destruct i as [|i]; try done). }
    simplify_map_eq'.
    apply: Hloop2; [done|]. eexists (i + 1)%nat. split!.
    + lia.
    + sort_map_insert. rewrite !insert_insert. apply map_eq => j.
      destruct (decide (j = "PC")); simplify_map_eq; [f_equal; lia|].
      rewrite (lookup_insert_ne _ "PC"); [|done].
      destruct (decide (j = (saved_registers !!! i))); simplify_map_eq. {
        rewrite lookup_insert_ne.
        2: { do 12 (destruct i as [|i]; try done). }
        rewrite lookup_insert_ne.
        2: { do 12 (destruct i as [|i]; try done). }
        symmetry. apply lookup_union_Some_l.
        apply coro_regs_regs_n_lookup_Some. split!.
        apply elem_of_take. eexists i. split; [|lia].
        apply coro_saved_regs_lookup_saved. lia.
      }
      destruct (decide (j = "R16")); simplify_map_eq; [done|].
      destruct (decide (j = "R17")); simplify_map_eq; [done|].
      destruct (coro_regs_regs_n rsold i !! j) eqn: Heq.
      * rewrite lookup_union_l' // Heq. symmetry. apply lookup_union_Some_l.
        move: Heq => /coro_regs_regs_n_lookup_Some[??].
        apply coro_regs_regs_n_lookup_Some. split!.
        rewrite coro_saved_regs_take_saved; [done|lia|done].
      * rewrite lookup_union_r // lookup_union_r //.
        move: Heq => /coro_regs_regs_n_lookup_None?.
        apply coro_regs_regs_n_lookup_None. split!.
        rewrite coro_saved_regs_take_saved; [done|lia|done].
    + rewrite lookup_total_insert_ne.
      2: { do 12 (destruct i as [|i]; try done). }
      rewrite lookup_total_insert_ne.
      2: { do 12 (destruct i as [|i]; try done). }
      rewrite lookup_total_insert_ne.
      2: { do 12 (destruct i as [|i]; try done). }
      rewrite !insert_union_l.
      erewrite coro_regs_mem_n_insert. 2: { apply coro_saved_regs_lookup_saved. lia. }
      f_equal. f_equal. apply coro_regs_mem_n_rs_eq => k.
      destruct (decide (k = saved_registers !!! i)); simplify_map_eq' => //.
      rewrite !lookup_total_alt. rewrite lookup_union_r //.
      apply coro_regs_regs_n_lookup_None.
      do 12 (destruct i as [|i]; [compute_done|]). lia.
Qed.

(** * Definition of coroutine linking *)
Inductive coro_link_filter_case :=
| CPFInit
| CPFLeft
| CPFRight.

Global Instance coro_link_filter_case_inhabited : Inhabited coro_link_filter_case := populate CPFRight.

Definition coro_link_filter (fns1 fns2 : gset string) : seq_product_case → coro_link_filter_case * (option string) → rec_ev → seq_product_case → coro_link_filter_case * (option string) → rec_ev → bool → Prop :=
  λ p s e p' s' e' ok,
    match s.1, p with
    | CPFInit, None =>
        ∃ f vs h,
        e = ERCall f vs h ∧
        e' = e ∧
        p' = Some SPLeft ∧
        ok = bool_decide (f ∈ fns1) ∧
        s' = (CPFLeft, s.2)
    | CPFInit, _ => False
    | CPFLeft, None
    | CPFRight, None =>
        e' = e ∧
        p' = (if s.1 is CPFRight then Some SPRight else Some SPLeft) ∧
        s' = s ∧
        ok = if e is ERCall _ _ _ then false else true
    | CPFLeft, _ =>
        (* p must be SPLeft *)
        p = Some SPLeft ∧
        match e with
        | ERCall f vs h =>
            if bool_decide (f = "yield") then
              e' = (if s.2 is Some f then ERCall f vs h else ERReturn (vs !!! 0%nat) h) ∧
              p' = Some SPRight ∧
              s' = (CPFRight, None) ∧
              ok = bool_decide (length vs = 1%nat)
            else
              e' = e ∧
              p' = (if bool_decide (f ∈ fns2) then Some SPRight else None) ∧
              s' = s ∧
              ok = bool_decide (f ∉ fns2)
        | ERReturn v h =>
            e' = e ∧
            p' = None ∧
            s' = (CPFInit, s.2) ∧
            ok = true
        end
    | CPFRight, _ =>
        (* p must be SPRight *)
        p = Some SPRight ∧
        match e with
        | ERCall f vs h =>
            if bool_decide (f = "yield") then
              e' = ERReturn (vs !!! 0%nat) h ∧
              p' = Some SPLeft ∧
              s' = (CPFLeft, None) ∧
              ok = bool_decide (length vs = 1%nat)
            else
              e' = e ∧
              p' = (if bool_decide (f ∈ fns1) then Some SPLeft else None) ∧
              s' = s ∧
              ok = bool_decide (f ∉ fns1)
        | ERReturn v h =>
            ok = false ∧
            e' = e ∧
            p' = Some SPRight ∧
            s' = s
        end
    end.
Arguments coro_link_filter _ _ _ _ _ _ _ _ /.

Definition coro_link_trans (fns1 fns2 : gset string) (m1 m2 : mod_trans rec_event) : mod_trans rec_event :=
  link_trans (coro_link_filter fns1 fns2) m1 m2.

Definition coro_link (fns1 fns2 : gset string) (finit : string) (m1 m2 : module rec_event) : module rec_event :=
  Mod (coro_link_trans fns1 fns2 m1.(m_trans) m2.(m_trans))
    (MLFRun None, (CPFInit, (Some finit)), m1.(m_init), m2.(m_init)).

Lemma coro_link_trefines m1 m1' m2 m2' fns1 fns2 finit `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (coro_link fns1 fns2 finit m1 m2) (coro_link fns1 fns2 finit m1' m2').
Proof. move => ??. by apply link_mod_trefines. Qed.

(** * Main Theorem: Yield library refines coroutine linking *)
Theorem coro_spec finit regs_init ssz_init fns1 fns2 m1 m2 ins1 ins2 f2i1 f2i2
  `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  let fns := {["yield"]} ∪ fns1 ∪ fns2 in
  let ins := yield_asm_dom ∪ ins1 ∪ ins2 in
  let f2i := f2i1 ∪ f2i2 in
  let mo := (r2a_mem_stack_mem (regs_init !!! "SP") ssz_init ∪ coro_regs_mem regs_init) in
  f2i2 !! finit = Some (regs_init !!! "PC") →
  finit ∈ fns2 →
  "yield" ∉ fns1 ∪ fns2 →
  ins1 ## ins2 →
  fns1 ## fns2 →
  yield_asm_dom ## ins1 ∪ ins2 →
  f2i1 !! "yield" = Some yield_addr →
  f2i2 !! "yield" = Some yield_addr →
  f2i_fns_ins_wf f2i1 fns1 ins1 →
  f2i_fns_ins_wf f2i2 fns2 ins2 →
  map_agree f2i1 f2i2 →
  map_Forall (λ f i, i ∉ ins2 ∨ f2i2 !! f = Some i) f2i1 →
  map_Forall (λ f i, i ∉ ins1 ∨ f2i1 !! f = Some i) f2i2 →
  map_Forall (λ f i, f = "yield" ∨ i ∉ yield_asm_dom) f2i →
  r2a_mem_stack_mem (regs_init !!! "SP") ssz_init ##ₘ coro_regs_mem regs_init →
  trefines
    (asm_link yield_asm_dom (ins1 ∪ ins2) (asm_mod yield_asm)
       (asm_link ins1 ins2 (rec_to_asm ins1 f2i1 ∅ ∅ m1) (rec_to_asm ins2 f2i2 ∅ ∅ m2)))
    (rec_to_asm ins f2i mo ∅ (coro_link fns1 fns2 finit m1 m2))
.
Proof.
  move => fns ins f2i mo Hinit Hfinit Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hwf1 Hwf2 Hag Hf1 Hf2 Hfy Hmo.
  destruct m1 as [m1 σ1], m2 as [m2 σ2] => /=.
  have : regs_init !!! "PC" ∈ ins2. { by apply: f2i_fns_ins_wf_in_fns_pure. }
  etrans. {
    apply: asm_link_trefines; [|done]. apply (yield_asm_refines_spec regs_init).
    fast_set_solver.
  }
  apply: tsim_implies_trefines => n0 /=.
  tstep_i => *. case_match; destruct!/=.
  tstep_s. split!.
  tstep_s. move => -[] //= ? h ssz vs avs f *.
  tstep_s. split!.
  tstep_s => ?.
  iSatStart. iIntros!.
  rewrite r2a_f2i_incl_union; [ |done| | ]. 2: {
   move => i f' /elem_of_union[?|?] ?.
   - exploit Hfy.
     rewrite /f2i map_union_comm_agree; [by apply lookup_union_Some_l|done].
     naive_solver.
   - move => *. unfold map_Forall in *. naive_solver. } 2:{
   move => *. unfold map_Forall in *. naive_solver. }
  have {1} -> : f2i1 = {["yield" := yield_addr]} ∪ f2i1. {
    apply map_eq => f'. apply option_eq => ?.
    rewrite lookup_union_Some_raw. rewrite lookup_singleton_Some. rewrite lookup_singleton_None.
    destruct (decide (f' = "yield")); naive_solver.
  }
  rewrite r2a_f2i_incl_union. 2: {
    apply map_agree_singleton_l. naive_solver. } 2: {
    move => *. apply lookup_singleton_Some.
    exploit Hfy; [by apply lookup_union_Some_l|]. naive_solver. } 2: {
    move => ??? /lookup_singleton_Some[??]. subst. done. }
  iDestruct!. iSatStop.
  have ? : regs !!! "PC" ∈ ins1. {
    iSatStart. iDestruct (f2i_fns_ins_wf_in_fns f2i1 with "[$] [$]") as %?; [done..|]. by iSatStop.
  }
  rewrite bool_decide_false; [|fast_set_solver].
  rewrite bool_decide_true; [|fast_set_solver].
  tstep_i => *. case_match; destruct!/=.
  rewrite bool_decide_true; [|fast_set_solver].
  tstep_i => *. simplify_eq.
  tstep_i. eexists true. split; [done|]. eexists h, ssz, vs, avs, f.
  split!. { fast_set_solver. }
  { iSatMono. iIntros!. rewrite /r2a_mem_map/mo big_sepM_empty big_sepM_union //. iDestruct!.
    iDestruct select (r2a_f2i_incl f2i1 _) as "#Hf2i1". iFrame "#∗".
    iDestruct (r2a_mem_stack_init with "[$]") as "?".
    iDestruct "Hf2i1" as "-#?". iSplit!. iAccu. }
  tsim_mirror m1 σ1. { tstep_s. by exists None. }
  move => *. subst.
  tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
  unshelve apply: tsim_remember. { simpl. exact (λ _
      '(σpy1, σpy2, (yt, yregs), (σpc1, σpc2, (σsm1, σ1, (pp1, (R2A cs1 lr1), x1)), (σsm2, σ2, (pp2, (R2A cs2 lr2), x2))))
      '(σsm', (σlc, σc, σ1', σ2'), (ppc, (R2A csc lrc), xc)),
       ∃ cret cregs rx1 rx2 rxc,
       x1 = uPred_shrink rx1 ∧ x2 = uPred_shrink rx2 ∧ xc = uPred_shrink rxc ∧
       yt ≡ yield_spec ∧
       σ1' = σ1 ∧
       σ2' = σ2 ∧
       σpy1 = MLFRun (Some SPRight) ∧
       σpy2 = None ∧
       σpc2 = None ∧
       σsm' = SMProg ∧
       ppc = PPInside ∧
       csc = [R2AI false cret cregs] ∧
       cret ∉ ins ∧
       match σc.1 with
       (* Left side, not yet changed to right side *)
       | CPFLeft =>
           ∃ ssz,
           σpc1 = MLFRun (Some SPLeft) ∧
           σsm1 = SMProg ∧
           pp1 = PPInside ∧
           cs1 = csc ∧
           map_scramble touched_registers lrc lr1 ∧
           (rx1 ⊣⊢ r2a_f2i_incl {["yield" := yield_addr]} yield_asm_dom ∗
                   r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2 ∗
                   r2a_mem_stack (yregs !!! "SP") ssz ∗ r2a_mem_map (coro_regs_mem yregs) ∗ rx2 ∗ rxc)%I ∧
           σsm2 = SMFilter ∧
           pp2 = PPOutside ∧
           (if σc.2 is Some f then
              cs2 = [] else
              ∃ regs1 ret2 regs2,
                cs2 = [R2AI true (yregs !!! "PC") regs1; R2AI false ret2 regs2] ∧
                map_preserved saved_registers regs1 yregs) ∧
           σlc = MLFRun (Some SPLeft) ∧
           yregs !!! "PC" ∈ ins2 ∧
           (if σc.2 is Some f then f2i2 !! f = Some (yregs !!! "PC") ∧ f ∈ fns2 else True)
       (* Right side *)
       | CPFRight =>
           ∃ ssz regs1 ret2 regs2,
           σpc1 = MLFRun (Some SPRight) ∧
           σsm1 = SMFilter ∧
           pp1 = PPOutside ∧
           cs1 = [R2AI true (yregs !!! "PC") regs1; R2AI false cret cregs] ∧
           map_preserved saved_registers regs1 yregs ∧
           map_scramble touched_registers lrc lr2 ∧
           (rx2 ⊣⊢ r2a_f2i_incl {["yield" := yield_addr]} yield_asm_dom ∗
                   r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2 ∗
                   r2a_mem_stack (yregs !!! "SP") ssz ∗ r2a_mem_map (coro_regs_mem yregs) ∗ rx1 ∗ rxc)%I ∧
           σsm2 = SMProg ∧
           pp2 = PPInside ∧
           cs2 = [R2AI false ret2 regs2] ∧
           σlc = MLFRun (Some SPRight) ∧
           yregs !!! "PC" ∈ ins1
       | _ => False
       end). }
  { split!. {
      iSplit; iIntros!; iDestruct select (r2a_f2i_incl f2i2 _) as "#?"; iFrame "#∗".
      iSplit!. by iApply big_sepM_empty. } } { done. }
  clear -Hyf Hidisj Hfdisj Hydisj Hy1 Hy2 Hwf1 Hwf2 Hag VisNoAng0 VisNoAng1.
  have ? : yield_addr ∈ yield_asm_dom by rewrite /yield_asm_dom /yield_asm; unlock; compute_done.
  move => n ? Hloop [[[σpy1 σpy2][yt yregs]][[[σpc1 σpc2][[σsm1 σ1][[pp1 [cs1 lr1]]x1]]][[σsm2 σ2][[pp2 [cs2 lr2]]x2]]]].
  move => [[σsm' [[[σlc σc] σ1'] σ2']][[ppc [csc lrc]] xc]] [state ?]. destruct!.
  destruct σc as [[| |] finit] => //; destruct!/=.
  - tsim_mirror m1 σ1. { tstep_s. by eexists None. }
    move => ???[i e]? Hstep.
    tend. have [σ' Hσ'] := vis_no_all _ _ _ Hstep. eexists σ'. split; [naive_solver|].
    destruct i; [by tstep_i|].
    tstep_s. eexists (Some (Outgoing, e)).
    destruct e => /=; [case_bool_decide|]; split!.
    all: apply: steps_spec_step_end; [done|] => σ'' ?; assert (σ'' = σ') by naive_solver.
    + (* left to right *)
      tstep_s => ?.
      tstep_i => *. setoid_subst. destruct!; simplify_map_eq'.
      iSatStart. iIntros!.
      iDestruct (r2a_f2i_incl_agree_f _ _ _ {[_:=_]} {[_:=_]} with "[$] [$]") as %?; [by apply lookup_singleton..|].
      iSatStop. simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: { fast_set_solver. }
      move => /= *. destruct!; simplify_map_eq'.
      rewrite bool_decide_true; [|done].
      tstep_i. rewrite -/yield_spec. go.
      go_i => -[??]. go.
      go_i => ?. simplify_eq. go.
      go_i. split; [done|]. go.
      go_i. split; [fast_set_solver|]. go.
      go_i.
      iSatStart.
      iDestruct select (r2a_mem_inv _ _ _) as "Hm".
      iDestruct (r2a_mem_lookup_big with "Hm [$]") as %?.
      iSatStop.
      go_i. split!. go.
      go_i.
      go_i => ?. go.
      go_i => ?. go.
      go_i => *. destruct!. simplify_map_eq'. go.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. destruct!/=; simplify_map_eq'.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. simplify_eq.
      tstep_i.
      destruct finit; destruct!.
      * eexists true. split!.
        { apply: r2a_args_pure_mono; [|done].
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply coro_regs_regs_args_preserved. }
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R30"); [|compute_done]. fast_set_solver. }
        { iSatMonoBupd. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
          iDestruct (r2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (r2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
          iModIntro. iSplit.
          - iSplit; [|done]. by iApply r2a_f2i_incl_single.
          - iDestruct select (r2a_f2i_incl _ ∅) as "_". iAccu. }
        tsim_mirror m2 σ2. { tstep_s. by exists None. }
        move => *. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
        split!.
        { simplify_map_eq'. done. }
        { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
        { etrans; [done|]. etrans; [done|].
          apply map_scramble_insert_r_in; [compute_done|].
          apply map_scramble_insert_r_in; [compute_done|].
          by apply coro_regs_regs_touched_scramble. }
        { simplify_map_eq'. iSplit; iIntros!; iFrame. }
        { simplify_map_eq'. done. }
      * destruct args as [|? [|]] => //.
        eexists false. split!.
        { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
        { split. { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R0"); [|compute_done]. done. }
          apply map_preserved_insert_r_not_in; [compute_done|].
          apply map_preserved_insert_r_not_in; [compute_done|].
          by apply coro_regs_regs_saved_preserved. }
        { iSatMonoBupd.
          iDestruct (r2a_args_intro with "[$]") as "?"; [done|].
          rewrite r2a_args_cons; [|done]. rewrite r2a_args_nil. iDestruct!. iFrame. simplify_map_eq'.
          rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
          iDestruct (r2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
          iMod (r2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
          iModIntro. iDestruct select (r2a_f2i_incl _ ∅) as "_". iAccu. }
        tsim_mirror m2 σ2. { tstep_s. by eexists None. }
        move => *. subst.
        tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
        apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
        split!.
        { simplify_map_eq'. done. }
        { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
        { etrans; [done|]. etrans; [done|].
          apply map_scramble_insert_r_in; [compute_done|].
          apply map_scramble_insert_r_in; [compute_done|].
          by apply coro_regs_regs_touched_scramble. }
        { simplify_map_eq'. iSplit; iIntros!; iFrame. }
        { simplify_map_eq'. done. }
    + (* left call to outside *)
      case_bool_decide; [by tstep_s|].
      rewrite bool_decide_true //=.
      tstep_i => ? rs *. destruct!.
      have ?: rs !!! "PC" ∉ ins. {
        iSatStart. setoid_subst. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_fns f2i2 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_fns {["yield" := yield_addr]} {["yield"]} yield_asm_dom with "[$] [$]") as %?.
        { unfold yield_asm_dom, yield_asm. unlock. compute_done. }
        { fast_set_solver. }
        iSatStop. fast_set_solver.
      }
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct!/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!. { done. } { fast_set_solver. } { by etrans. }
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* go back inside *)
      tstep_i => e *. destruct e; destruct!.
      tstep_s. split!.
      tstep_s => -[] /= *. { tstep_s. split!. by tstep_s. }
      tstep_s. split!. destruct!. simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => /= *. destruct!/=.
      rewrite bool_decide_true; [|done].
      tstep_i => *. simplify_eq.
      tstep_i => *. eexists false. split!. { done. }
      { iSatMono. iIntros!. iFrame. iAccu. }
      tsim_mirror m1 σ'. { tstep_s. by eexists None. }
      move => *. simplify_eq.
      tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
      split!. iSplit; iIntros!; iFrame.
    + (* left return to outside *)
      tstep_i => *. destruct!.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct!/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!. { done. } { by etrans. }
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* going back inside *)
      tstep_i => e *. tstep_s. split!. destruct!/=.
      destruct e; destruct!.
      tstep_s => -[] //= ? h' ssz' vs' avs' f' *.
      tstep_s. split!.
      tstep_s => ?.
      have ? : regs !!! "PC" ∈ ins1. {
        iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_fns f2i1 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      rewrite bool_decide_false; [|fast_set_solver].
      rewrite bool_decide_true; [|fast_set_solver].
      tstep_i => *. case_match; destruct!/=.
      rewrite bool_decide_true; [|fast_set_solver].
      tstep_i => *. simplify_eq.
      tstep_i. eexists true. split; [done|]. eexists h', ssz', vs', avs', f'.
      split!. { fast_set_solver. }
      { iSatMono. iIntros!. iFrame. iAccu. }
      tsim_mirror m1 σ'. { tstep_s. by eexists None. }
      move => *. subst.
      tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
      split!. { iSplit; iIntros!; iFrame. }
  - tsim_mirror m2 σ2. { tstep_s. by exists None. }
    move => ??? [i e] ? Hstep.
    tend. have [σ' Hσ'] := vis_no_all _ _ _ Hstep. eexists σ'. split; [naive_solver|].
    destruct i; [by tstep_i|].
    tstep_s. eexists (Some (Outgoing, e)).
    destruct e => /=; [case_bool_decide|]; split!.
    all: apply: steps_spec_step_end; [done|] => σ'' ?; assert (σ'' = σ') by naive_solver.
    + (* right to left *)
      tstep_s => ?.
      tstep_i => *. setoid_subst. destruct!; simplify_map_eq'.
      iSatStart. iIntros!.
      iDestruct (r2a_f2i_incl_agree_f _ _ _ {[_:=_]} {[_:=_]} with "[$] [$]") as %?; [by apply lookup_singleton..|].
      iSatStop. simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct!; simplify_map_eq'.
      rewrite bool_decide_true. 2: done.
      tstep_i. rewrite -/yield_spec. go.
      go_i => -[??]. go.
      go_i => ?. simplify_eq. go.
      go_i. split; [done|]. go.
      go_i. split; [fast_set_solver|]. go.
      go_i.
      iSatStart.
      iDestruct select (r2a_mem_inv _ _ _) as "Hm".
      iDestruct (r2a_mem_lookup_big with "Hm [$]") as %?.
      iSatStop.
      go_i. split!. go.
      go_i.
      go_i => ?. go.
      go_i => ?. go.
      go_i => *. destruct!. simplify_map_eq'. go.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. destruct!/=; simplify_map_eq'.
      rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done].
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => *. simplify_eq.
      tstep_i.
      destruct args as [|? [|]] => //.
      eexists false. split!.
      { simplify_map_eq'. rewrite (coro_regs_regs_lookup_in "PC"); [|compute_done]. done. }
      { split. { simplify_map_eq'. rewrite (coro_regs_regs_lookup_not_in "R0"); [|compute_done]. done. }
        apply map_preserved_insert_r_not_in; [compute_done|].
        apply map_preserved_insert_r_not_in; [compute_done|].
        by apply coro_regs_regs_saved_preserved. }
      { iSatMonoBupd.
        iDestruct (r2a_args_intro with "[$]") as "?"; [done|].
        rewrite r2a_args_cons; [|done]. rewrite r2a_args_nil. iDestruct!. iFrame. simplify_map_eq'.
        rewrite (coro_regs_regs_lookup_in "SP"); [|compute_done].
        iDestruct (r2a_mem_swap_stack with "Hm [$]") as "[Hm ?]".
        iMod (r2a_mem_update_big with "Hm [$]") as "[? $]"; [apply coro_regs_mem_dom|].
        iModIntro. iDestruct select (r2a_f2i_incl _ ∅) as "_". iAccu. }
      tsim_mirror m1 σ1. { tstep_s. by eexists None. }
      move => *. subst.
      tstep_s. eexists (Some (Incoming, _)). split!. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
      split!.
      { etrans; [done|]. etrans; [done|].
        apply map_scramble_insert_r_in; [compute_done|].
        apply map_scramble_insert_r_in; [compute_done|].
        by apply coro_regs_regs_touched_scramble. }
      { simplify_map_eq'. iSplit; iIntros!; iFrame. }
      { simplify_map_eq'. done. }
      { apply map_preserved_insert_r_not_in; [compute_done|]. done. }
      { simplify_map_eq'. done. }
    + (* right call to outside *)
      case_bool_decide; [by tstep_s|].
      rewrite bool_decide_true //=.
      tstep_i => ? rs *. destruct!.
      have ?: rs !!! "PC" ∉ ins. {
        iSatStart. setoid_subst. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_fns f2i1 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_fns {["yield" := yield_addr]} {["yield"]} yield_asm_dom with "[$] [$]") as %?.
        { unfold yield_asm_dom, yield_asm. unlock. compute_done. }
        { fast_set_solver. }
        iSatStop. fast_set_solver.
      }
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      move => /= *. destruct!/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_false. 2: fast_set_solver.
      tstep_s. split!. { done. } { fast_set_solver. } { by etrans. }
      { iSatMono. setoid_subst. iIntros!. iFrame. iAccu. }
      iSatClear.

      (* go back inside *)
      tstep_i => e *. destruct e; destruct!.
      tstep_s. split!.
      tstep_s => -[] /= *. { tstep_s. split!. by tstep_s. }
      tstep_s. split!. destruct!. simplify_map_eq'.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true. 2: fast_set_solver.
      tstep_i => /= *. destruct!/=.
      rewrite bool_decide_false. 2: fast_set_solver.
      rewrite bool_decide_true; [|done].
      tstep_i => *. simplify_eq.
      tstep_i => *. eexists false. split!. { done. }
      { iSatMono. iIntros!. iFrame. iAccu. }
      tsim_mirror m2 σ'. { tstep_s. by eexists None. }
      move => *. simplify_eq.
      tstep_s. eexists (Some (Incoming, _)). split!.
      apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop. { etrans; [|done]. etrans; [|done]. apply o_le_S. }
      split!. iSplit; iIntros!; iFrame.
    + (* right return to outside *) by tstep_s.
 Unshelve.
 all: apply: inhabitant.
Qed.
