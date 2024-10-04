From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris expr2 spec2.
From dimsum.examples Require Export asm.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Definition instrsUR : cmra :=
  agreeR (gmapO Z (leibnizO asm_instr)).

Definition to_instrs : gmap Z asm_instr → instrsUR :=
  to_agree.


Class asmPreGS (Σ : gFunctors) := AsmPreGS {
  asm_mapsto_ghost_map_preG :: ghost_mapG Σ Z (option Z);
  asm_reg_mapsto_ghost_map_preG :: ghost_mapG Σ string Z;
  asm_instrs_preG :: inG Σ instrsUR;
}.

Class asmGS (Σ : gFunctors) := AsmGS {
  asm_mapsto_ghost_mapG :: ghost_mapG Σ Z (option Z);
  asm_reg_mapsto_ghost_mapG :: ghost_mapG Σ string Z;
  asm_instrsG :: inG Σ instrsUR;
  asm_mapsto_name : gname;
  asm_reg_mapsto_name : gname;
  asm_instrs_name : gname;
}.

Definition asmΣ : gFunctors :=
  #[ ghost_mapΣ Z (option Z); ghost_mapΣ string Z; GFunctor instrsUR ].

Global Instance subG_asmΣ Σ :
  subG asmΣ Σ → asmPreGS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!asmGS Σ}.

  Definition asm_mapsto_def (a : Z) (q : dfrac) (v : option Z) : iProp Σ :=
    ghost_map_elem asm_mapsto_name a q v.
  Local Definition asm_mapsto_aux : seal (@asm_mapsto_def).
  Proof. by eexists. Qed.
  Definition asm_mapsto := asm_mapsto_aux.(unseal).
  Local Definition asm_mapsto_unseal :
    @asm_mapsto = @asm_mapsto_def := asm_mapsto_aux.(seal_eq).

  Definition asm_mapsto_auth (mem : gmap Z (option Z)) : iProp Σ :=
    ghost_map_auth asm_mapsto_name 1 mem.

  Definition asm_reg_mapsto_def (r : string) (v : Z) : iProp Σ :=
    ghost_map_elem asm_reg_mapsto_name r (DfracOwn 1) v.
  Local Definition asm_reg_mapsto_aux : seal (@asm_reg_mapsto_def).
  Proof. by eexists. Qed.
  Definition asm_reg_mapsto := asm_reg_mapsto_aux.(unseal).
  Local Definition asm_reg_mapsto_unseal :
    @asm_reg_mapsto = @asm_reg_mapsto_def := asm_reg_mapsto_aux.(seal_eq).

  Definition asm_reg_mapsto_auth (regs : gmap string Z) : iProp Σ :=
    ∃ rs, ⌜∀ r z, rs !! r = Some z → regs !!! r = z⌝ ∗
      ghost_map_auth asm_reg_mapsto_name 1 rs.

  Definition reg_col (rs : list string) (regs : gmap string Z) : iProp Σ :=
    [∗ list] r∈rs, asm_reg_mapsto r (regs !!! r).

  Definition asm_instrs_auth (instrs : gmap Z asm_instr) : iProp Σ :=
    own asm_instrs_name (to_instrs instrs).

  Definition asm_instrs_mapsto_def (a : Z) (instr : option asm_instr) : iProp Σ :=
    ∃ instrs, ⌜instrs !! a = instr⌝ ∗ asm_instrs_auth instrs.
  Local Definition asm_instrs_mapsto_aux : seal (@asm_instrs_mapsto_def).
  Proof. by eexists. Qed.
  Definition asm_instrs_mapsto := asm_instrs_mapsto_aux.(unseal).
  Local Definition asm_instrs_mapsto_unseal :
    @asm_instrs_mapsto = @asm_instrs_mapsto_def := asm_instrs_mapsto_aux.(seal_eq).

  Definition asm_instrs_mapsto_big (instrs : gmap Z asm_instr) : iProp Σ :=
    [∗ map] a↦i∈instrs, asm_instrs_mapsto a (Some i).

  Definition asm_state_interp (σ : asm_state) : iProp Σ :=
    asm_instrs_auth (asm_instrs σ) ∗
    asm_mapsto_auth (asm_mem σ) ∗
    asm_reg_mapsto_auth (asm_regs σ).
End definitions.

Notation "a ↦ₐ? v" := (asm_mapsto a (DfracOwn 1) v)
  (at level 20, format "a  ↦ₐ?  v") : bi_scope.
Notation "a ↦ₐ v" := (asm_mapsto a (DfracOwn 1) (Some v))
  (at level 20, format "a  ↦ₐ  v") : bi_scope.
Notation "a ↦ₐ #" := (asm_mapsto a (DfracOwn 1) None)
  (at level 20, format "a  ↦ₐ  #") : bi_scope.
Notation "r ↦ᵣ v" := (asm_reg_mapsto r v)
  (at level 20, format "r  ↦ᵣ  v") : bi_scope.
Notation "a ↪ₐ instr" := (asm_instrs_mapsto a instr)
  (at level 20, format "a  ↪ₐ  instr") : bi_scope.
Notation "↪ₐ∗ instrs" := (asm_instrs_mapsto_big instrs)
  (at level 20, format "↪ₐ∗  instrs") : bi_scope.

Local Ltac unseal := rewrite
  ?asm_mapsto_unseal /asm_mapsto_def /asm_mapsto_auth
  ?asm_reg_mapsto_unseal /asm_reg_mapsto_def /asm_reg_mapsto_auth
  ?asm_instrs_mapsto_unseal /asm_instrs_mapsto_def /asm_instrs_auth.

Section lemmas.
  Context `{!asmGS Σ}.

  (** mapsto ghost state  *)
  Lemma asm_mapsto_lookup mem a v :
    asm_mapsto_auth mem -∗ a ↦ₐ? v -∗ ⌜mem !! a = Some v⌝.
  Proof. unseal. apply ghost_map_lookup. Qed.

  Lemma asm_mapsto_update mem a v v' :
    asm_mapsto_auth mem -∗ a ↦ₐ? v ==∗ asm_mapsto_auth (<[a:=v']>mem) ∗ a ↦ₐ? v'.
  Proof.
    iIntros "Hmem Hl".
    iDestruct (asm_mapsto_lookup with "Hmem Hl") as %?.
    unseal.
    by iMod (ghost_map_update with "Hmem Hl") as "[? $]".
  Qed.

  Lemma asm_mapsto_alloc_big mem' mem :
    mem' ##ₘ mem →
    asm_mapsto_auth mem ==∗
    asm_mapsto_auth (mem' ∪ mem) ∗ [∗ map] a↦v∈mem', a ↦ₐ? v.
  Proof. unseal. apply ghost_map_insert_big. Qed.

  (** reg mapsto ghost state  *)
  Lemma asm_reg_mapsto_lookup regs r z :
    asm_reg_mapsto_auth regs -∗ r ↦ᵣ z -∗ ⌜regs !!! r = z⌝.
  Proof.
    unseal. iIntros "[%rs [% ?]] ?".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iPureIntro. naive_solver.
  Qed.

  Lemma asm_reg_mapsto_disj r z1 z2 :
    r ↦ᵣ z1 -∗ r ↦ᵣ z2 -∗ False.
  Proof. unseal. iIntros "Hr1 Hr2". iCombine "Hr1 Hr2" gives %?. naive_solver. Qed.

  Lemma asm_reg_mapsto_update regs r v v' :
    asm_reg_mapsto_auth regs -∗ r ↦ᵣ v ==∗ asm_reg_mapsto_auth (<[r:=v']>regs) ∗ r ↦ᵣ v'.
  Proof.
    unseal.
    iIntros "[% [%Hrs Hregs]] Hr".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iMod (ghost_map_update with "Hregs Hr") as "[$ $]".
    iPureIntro. move => ?? /lookup_insert_Some[[-> ->]|[??]]; simplify_map_eq' => //.
    naive_solver.
  Qed.

  (** instrs ghost state  *)
  Global Instance asm_instrs_auth_pers instrs : Persistent (asm_instrs_auth instrs).
  Proof. unseal. apply _. Qed.

  Global Instance asm_instrs_mapsto_pers a instr : Persistent (a ↪ₐ instr).
  Proof. unseal. apply _. Qed.

  Lemma asm_instrs_auth_agree instrs1 instrs2 :
    asm_instrs_auth instrs1 -∗ asm_instrs_auth instrs2 -∗ ⌜instrs1 = instrs2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
    by fold_leibniz.
  Qed.

  Lemma asm_instrs_intro a instr instrs :
    instrs !! a = instr → asm_instrs_auth instrs -∗ a ↪ₐ instr.
  Proof. unseal. iIntros (?) "Htbl". iExists _. by iFrame. Qed.

  Lemma asm_instrs_lookup a instr instrs :
    asm_instrs_auth instrs -∗ a ↪ₐ instr -∗ ⌜instrs !! a = instr⌝.
  Proof.
    unseal. iIntros "Htbl Hf".
    iDestruct "Hf" as (instrs2 ?) "Hf".
    by iDestruct (asm_instrs_auth_agree with "Htbl Hf") as %->.
  Qed.

  Lemma asm_instrs_big_lookup a instr instrs :
    instrs !! a = Some instr →
    ↪ₐ∗ instrs -∗
    a ↪ₐ Some instr.
  Proof. iIntros (?) "?". by iApply (big_sepM_lookup with "[$]"). Qed.

  Lemma asm_instrs_big_lookup_deep (n : nat) a0 a instr instrs :
    a = a0 + n →
    instrs !! n = Some instr →
    ↪ₐ∗ deep_to_asm_instrs a0 instrs -∗
    a ↪ₐ Some (deep_to_asm_instr instr).
  Proof.
    iIntros (-> Hl) "?".
    iApply (asm_instrs_big_lookup with "[$]").
    by rewrite (deep_to_asm_instrs_lookup_nat n) // Hl.
  Qed.

End lemmas.

Lemma asmgs_alloc `{!asmPreGS Σ} rs regs instrs :
  NoDup rs →
  ⊢ |==> ∃ H : asmGS Σ, asm_mapsto_auth ∅ ∗ asm_reg_mapsto_auth regs ∗ asm_instrs_auth instrs ∗ reg_col rs regs.
Proof.
  iIntros (Hdup).
  iMod (own_alloc (to_instrs instrs)) as (γf) "#Hinstrs" => //.
  iMod (ghost_map_alloc (K:=Z)) as (γmem) "[??]".
  iMod (ghost_map_alloc (K:=string) (list_to_map ((λ r, (r, regs !!! r)) <$> rs)))
    as (γregs) "[??]".

  iModIntro. iExists (AsmGS _ _ _ _ γmem γregs γf). iFrame "#∗".
  rewrite big_sepM_list_to_map.
  2: { by rewrite -list_fmap_compose/compose/= list_fmap_id. }
  iSplit.
  - iPureIntro. move => ?? /(elem_of_list_to_map_2 _ _ _) /elem_of_list_fmap.
    naive_solver.
  - rewrite /reg_col. rewrite big_sepL_fmap. by unseal.
Qed.

Program Canonical Structure asm_mod_lang {Σ} `{!asmGS Σ} := {|
  mexpr := asm_instr;
  mectx := unit;
  mfill _ x := x;
  mcomp_ectx _ _ := tt;
  mtrans := asm_trans;
  mexpr_rel σ e := asm_cur_instr σ = ARunning e;
  mstate_interp σ := asm_state_interp σ;
|}.
Next Obligation. move => ?????/=. done. Qed.

Definition asm_spec `{!dimsumGS Σ} `{!asmGS Σ} (ts : tgt_src)
  (Π : option asm_event → _ → iProp Σ)
  (pre : (iProp Σ → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ Φ, pre (λ POST, POST -∗ (WP{ts} [] :> asm_instr @ Π {{ Φ }})) -∗
     WP{ts} [] :> asm_instr @ Π {{ Φ }}).

Section lifting.
  Context `{!dimsumGS Σ} `{!asmGS Σ}.

  Lemma sim_tgt_asm_Waiting regs instrs Π mem :
    (∀ regs mem instr, ⌜instrs !! (regs !!! "PC") = Some instr⌝ -∗
      ▷ₒ Π (Some (Incoming, EAJump regs mem))
           (AsmState (ARunning []) regs mem instrs)) -∗
    AsmState AWaiting regs mem instrs ≈{asm_trans}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    inv select (asm_step _ _ _). iModIntro. iSplit!.
    iMod ("HΠ" with "[//]"). by iModIntro.
  Qed.

  Lemma sim_Jump_internal Π ts Φ pc i :
    "PC" ↦ᵣ pc -∗
    pc ↪ₐ Some i -∗
    (▷ₒ?ts ("PC" ↦ᵣ pc -∗ WP{ts} i @ Π {{ Φ }})) -∗
    WP{ts} [] @ Π {{ Φ }}.
  Proof.
    iIntros "HPC Hpc HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]").
    iDestruct (asm_reg_mapsto_lookup with "Hregs HPC") as %<-.
    iDestruct (asm_instrs_lookup with "Hinstrs Hpc") as %?.
    iApply ts_step_det. { by econs. } { naive_solver. } { inv 1. naive_solver. }
    iMod "HΦ". iModIntro. iFrame. iSplit!. iApply ("HΦ" with "[$]").
  Qed.

  Lemma sim_Jump_external Π ts Φ pc :
    "PC" ↦ᵣ pc -∗
    pc ↪ₐ None -∗
    (∀ σ,
      ⌜asm_cur_instr σ = AWaiting⌝ -∗
      asm_state_interp σ -∗
      "PC" ↦ᵣ pc -∗
      ▷ₒ?ts switch_id ts asm_trans Π
        (Some (Outgoing, EAJump (asm_regs σ) (asm_mem σ))) σ ({{ σ',
        ∃ i, ⌜asm_cur_instr σ' = ARunning i⌝ ∗ asm_state_interp σ' ∗
          WP{ts} i @ Π {{ Φ }} }})) -∗
    WP{ts} [] @ Π {{ Φ }}.
  Proof.
    iIntros "HPC Hpc HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]").
    iDestruct (asm_reg_mapsto_lookup with "Hregs HPC") as %<-.
    iDestruct (asm_instrs_lookup with "Hinstrs Hpc") as %?.
    iApply ts_step_det. { by econs. } { naive_solver. } { inv 1. naive_solver. }
    iMod ("HΦ" $! (AsmState _ _ _ _) with "[//] [$] [$]") as "HΦ". iModIntro.
    iApply (switch_id_mono with "HΦ") => /=. iIntros (?) "$".
  Qed.

  Definition learn_regs (P : gmap string Z → Prop) : iProp Σ :=
    ∃ rs, ([∗ map] r↦v∈rs, r ↦ᵣ v) ∗
        ⌜∀ regs, (∀ r z, rs !! r = Some z → regs !!! r = z) → P regs⌝.

  Definition learn_regs_dual (regs : gmap string Z) (Φ : iProp Σ) : iProp Σ :=
    ∀ C, (∃ P, learn_regs P ∧ (⌜P regs⌝ -∗ Φ -∗ C)) -∗ C.

  Lemma learn_regs_reg r v P:
    r ↦ᵣ v -∗
    learn_regs P -∗
    learn_regs (λ regs, regs !!! r = v ∧ P regs)%type.
  Proof.
    iIntros "Hr [%rs [Hrs %Hf]]".
    destruct (rs !! r) eqn:Hr.
    { iDestruct (big_sepM_lookup with "Hrs") as "?"; [done|].
      iDestruct (asm_reg_mapsto_disj with "[$] [$]") as %[]. }
    iExists (<[r:=v]>rs). iSplit.
    - iApply (big_sepM_insert_2 with "Hr Hrs").
    - iPureIntro. move => regs Hregs. split.
      + apply Hregs. by rewrite lookup_insert.
      + apply Hf. move => ???. apply Hregs. apply lookup_insert_Some. naive_solver.
  Qed.

  Lemma learn_regs_done:
    ⊢ learn_regs (λ _, True%type).
  Proof. iExists ∅. rewrite big_sepM_empty. iSplit!. Qed.

  Lemma learn_regs_elim P regs :
    learn_regs P -∗
    asm_reg_mapsto_auth regs -∗
    ⌜P regs⌝.
  Proof.
    iIntros "[%rs [Hrs %Hf]]".
    unseal. iIntros "[%rs' [%Hf' Ha]]".
    iDestruct (ghost_map_lookup_big with "Ha Hrs") as %Hsub.
    iPureIntro. apply Hf. move => ???. apply Hf'.
    rewrite map_subseteq_spec in Hsub. by apply Hsub.
  Qed.

  Lemma sim_WriteReg Π ts Φ r P f v (es : asm_instr) :
    learn_regs P ∧
     (r ↦ᵣ v ∗ ▷ₒ?ts (∀ regs, ⌜P regs⌝ -∗ r ↦ᵣ f regs -∗ WP{ts} es @ Π {{ Φ }})) -∗
    WP{ts} WriteReg r f :: es @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[#Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iAssert (⌜P regs⌝)%I as %?; subst. {
      iDestruct "HΦ" as "[? _]".
      iApply (learn_regs_elim with "[$] [$]").
    }
    iDestruct "HΦ" as "[_ [Hr HΦ]]".
    iApply (sim_gen_step_end with "[-]").
    iApply ts_step_det; [econs|naive_solver|by inv 1|].
    iMod "HΦ". iMod (asm_reg_mapsto_update with "Hregs Hr") as "[$ ?]".
    iModIntro. iFrame. iSplit!. by iApply "HΦ".
  Qed.

  Lemma sim_ReadMem Π ts Φ r1 r2 f v1 v2 z (es : asm_instr) :
    r1 ↦ᵣ v1 -∗
    r2 ↦ᵣ v2 -∗
    f v2 ↦ₐ z -∗
    (▷ₒ?ts (r1 ↦ᵣ z -∗ r2 ↦ᵣ v2 -∗ f v2 ↦ₐ z -∗ WP{ts} es @ Π {{ Φ }})) -∗
    WP{ts} ReadMem r1 r2 f :: es @ Π {{ Φ }}.
  Proof.
    iIntros "Hr1 Hr2 Ha HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]").
    iDestruct (asm_reg_mapsto_lookup with "Hregs Hr2") as %<-.
    iDestruct (asm_mapsto_lookup with "Hmem Ha") as %?.
    iApply ts_step_det. { econs. } { naive_solver. } { inv 1. naive_solver. }
    iMod "HΦ". iMod (asm_reg_mapsto_update with "Hregs Hr1") as "[$ ?]".
    iModIntro. iFrame. iSplit!. iApply ("HΦ" with "[$] [$] [$]").
  Qed.

  Lemma sim_WriteMem Π ts Φ r1 r2 f v1 v2 z (es : asm_instr) :
    r1 ↦ᵣ v1 -∗
    r2 ↦ᵣ v2 -∗
    f v2 ↦ₐ z -∗
    (▷ₒ?ts (r1 ↦ᵣ v1 -∗ r2 ↦ᵣ v2 -∗ f v2 ↦ₐ v1 -∗ WP{ts} es @ Π {{ Φ }})) -∗
    WP{ts} WriteMem r1 r2 f :: es @ Π {{ Φ }}.
  Proof.
    iIntros "Hr1 Hr2 Ha HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]").
    iDestruct (asm_reg_mapsto_lookup with "Hregs Hr2") as %<-.
    iDestruct (asm_reg_mapsto_lookup with "Hregs Hr1") as %<-.
    iDestruct (asm_mapsto_lookup with "Hmem Ha") as %?.
    iApply ts_step_det. { econs. } { naive_solver. } { inv 1. naive_solver. }
    iMod "HΦ". iMod (asm_mapsto_update with "Hmem Ha") as "[$ ?]".
    iModIntro. iFrame. iSplit!. iApply ("HΦ" with "[$] [$] [$]").
  Qed.

  Lemma sim_Syscall Π Φ (es : asm_instr) :
    (▷ₒ switch Π ({{ κ σ POST,
         ∃ regs mem,
           ⌜κ = Some (Outgoing, EASyscallCall (extract_syscall_args regs) mem)⌝ ∗
           asm_mapsto_auth mem ∗ learn_regs_dual regs (
       POST Tgt _ _ ({{ σ' Π', ∃ ret0, ⌜σ' = σ⌝ ∗ "R0" ↦ᵣ ret0 ∗
       switch Π' ({{ κ σ POST,
         ∃ ret mem',
         ⌜κ = Some (Incoming, EASyscallRet ret mem')⌝ ∗ "R0" ↦ᵣ ret ∗
       POST Tgt _ _ ({{ σ' Π',
          ⌜σ' = σ⌝ ∗ ⌜Π' = Π⌝ ∗ asm_mapsto_auth mem' ∗
          TGT es @ Π {{ Φ }} }})}})}}))}})) -∗
    TGT Syscall :: es @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? regs mem instrs] [] ?) "[Hinstrs [Hmem Hregs]]"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]") => /=.
    iIntros (?? Hf). inv Hf. iModIntro. iSplit!. iModIntro. iModIntro.

    iIntros (??) "[-> [-> HC]]".
    iApply "HΦ" => /=. iFrame. iSplit!; [done|]. iIntros (?) "[%P HX]".
    iAssert (⌜P regs⌝)%I as %?. {
      iDestruct "HX" as "[? _]". iApply (learn_regs_elim with "[$] [$]").
    }
    iDestruct "HX" as "[_ HX]". iApply "HX"; [done|].
    iIntros (??) "[% [-> [HR0 HΦ]]]".
    iApply (sim_gen_step_end with "[-]") => /=.
    iIntros (?? Hf). inv Hf. iModIntro. iSplit!. iModIntro.
    iMod (asm_reg_mapsto_update with "Hregs HR0") as "[??]". iModIntro.
    iApply "HΦ". iSplit!. iFrame. iIntros (??) "[-> [-> [? Hwp]]]".
    iApply "HC". iSplit!. iFrame.
  Qed.

End lifting.
