From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core Require Export proof_techniques prepost.
From dimsum.core Require Import link.
From dimsum.core Require Import axioms.
From dimsum.core Require Import weak_embed.
From dimsum.examples Require Import rec asm.
From dimsum.examples Require Export heapUR memUR.

Local Open Scope Z_scope.

(** * rec_to_asm *)

(** * Registers *)
Definition args_registers : list string :=
  ["R0"; "R1"; "R2"; "R3"; "R4"; "R5"; "R6"; "R7" ; "R8"].

Definition tmp_registers : list string :=
  args_registers ++ ["R9"; "R10"; "R11"; "R12"; "R13"; "R14"; "R15"; "R16"; "R17"; "R30"; "PC"].

Definition saved_registers : list string :=
  ["R19"; "R20"; "R21"; "R22"; "R23"; "R24"; "R25"; "R26"; "R27"; "R28"; "R29"; "SP"].

Definition touched_registers : list string :=
  tmp_registers ++ saved_registers.

Definition r2a_regs_ret (rs rsold : gmap string Z) (av : Z) : Prop :=
  rs !!! "R0" = av ∧
  map_preserved saved_registers rsold rs.

(** * Camera definition *)
Definition rec_to_asmUR : ucmra :=
  prodUR (optionO (agree (gset prov)))
 (prodUR (gmap_viewUR prov (agreeR Z))
 (prodUR (optionUR (agreeR (leibnizO (gmap string Z))))
 (prodUR heapUR
    (memUR)))).

Global Instance rec_to_asmUR_shrink : Shrink rec_to_asmUR.
Proof. solve_shrink. Qed.

Global Instance rec_to_asmUR_discrete : CmraDiscrete rec_to_asmUR.
Proof. apply _. Qed.

Program Definition r2a_heap : BiOwn (uPredI rec_to_asmUR) heapUR := {|
  bi_own r := uPred_ownM (None, (ε, (ε, (r, ε))))
|}.
Next Obligation.
  move => /= ?. etrans; [apply uPred.ownM_valid|]. iPureIntro.
  by move => [_ [_ [_ []]]].
Qed.
Next Obligation. move => ??/=. by rewrite -!uPred.ownM_op -!pair_op_2 -pair_op_1. Qed.
Next Obligation.
  move => ???/=. apply uPred.bupd_ownM_update.
  by repeat (apply prod_update; [done|] => /=).
Qed.
Next Obligation. solve_proper. Qed.

Program Definition r2a_mem : BiOwn (uPredI rec_to_asmUR) memUR := {|
  bi_own r := uPred_ownM (None, (ε, (ε, (ε, r))))
|}.
Next Obligation.
  move => /= ?. etrans; [apply uPred.ownM_valid|]. iPureIntro.
  by move => [_ [_ [_ []]]].
Qed.
Next Obligation. move => ??/=. by rewrite -!uPred.ownM_op -!pair_op_2 -?pair_op_1. Qed.
Next Obligation.
  move => ???/=. apply uPred.bupd_ownM_update.
  by repeat (apply prod_update; [done|] => /=).
Qed.
Next Obligation. solve_proper. Qed.

Definition r2a_shared_inj (r : (gmap_viewUR prov (agreeR Z))) : rec_to_asmUR
  := (None, (r, ε)).
Definition r2a_f2i_inj (f2i : gmap string Z) : rec_to_asmUR := (None, (ε, (Some (to_agree (f2i : leibnizO (gmap string Z))), ε))).
Definition r2a_statics_inj (r : agree (gset prov)) : rec_to_asmUR := (Some r, ε).

Notation r2a_heapUR_inv := (heapUR_inv r2a_heap).
Notation r2a_memUR_inv := (memUR_inv r2a_mem).

Notation "l '↦h' dq v" := (heapUR_ptsto r2a_heap l dq v)
  (at level 20, dq custom dfrac,format "l  ↦h dq  v") : bi_scope.
Notation "p '↦∗h' dq b" := (heapUR_block r2a_heap p dq b)
  (at level 20, dq custom dfrac at level 1, format "p  '↦∗h' dq  b") : bi_scope.
Notation "p '⤚h' dq d" := (heapUR_dom r2a_heap p dq d)
  (at level 20, dq custom dfrac at level 1, format "p  '⤚h' dq  d") : bi_scope.
Notation "a '↦m' dq v" := (memUR_ptsto r2a_mem a dq v)
  (at level 20, dq custom dfrac, format "a  ↦m dq  v") : bi_scope.


Definition r2a_shared_auth_raw (ps : gmap prov Z) : uPred (rec_to_asmUR) :=
  uPred_ownM (r2a_shared_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> ps)).
Definition r2a_shared (p : prov) (a : Z) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_shared_inj (gmap_view_frag p DfracDiscarded (to_agree $ a))).
Definition r2a_shared_auth (ps : gmap prov Z) : uPred (rec_to_asmUR) :=
  r2a_shared_auth_raw ps ∗ [∗ map] p↦a∈ps, r2a_shared p a.

Notation r2a_mem_map m := ([∗ map] a↦v ∈ m, a ↦m v)%I.
(* Definition r2a_mem_map (m : gmap Z (option Z)) : uPred rec_to_asmUR := *)

Definition r2a_mem_uninit (a : Z) (len : Z) : uPred rec_to_asmUR :=
  [∗ list] a ∈ seqZ a len, ∃ v, a ↦m (Some v).

Definition r2a_f2i_full (f2i : gmap string Z) : uPred rec_to_asmUR :=
  uPred_ownM (r2a_f2i_inj f2i).

(* Intuitively, [r2a_f2i_incl f2i ins] means that [f2i] is part of the
global function to address map and that it is precise on the addresses
in [ins], i.e. no functions not in f2i point to [ins]. *)
Definition r2a_f2i_incl (f2i : gmap string Z) (ins : gset Z) : uPred rec_to_asmUR :=
  ∃ f2i_full, ⌜f2i ⊆ f2i_full⌝ ∗ ⌜∀ f i, i ∈ ins → f2i_full !! f = Some i → f2i !! f = Some i⌝
  ∗ r2a_f2i_full f2i_full .

Definition r2a_statics (provs : gset prov) :=
  uPred_ownM (r2a_statics_inj (to_agree provs)).

(** ** Ghost state lemmas *)

Lemma r2a_statics_agree ps1 ps2 :
  r2a_statics ps1 -∗
  r2a_statics ps2 -∗
  ⌜ps1 = ps2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [/=]. rewrite -Some_op Some_valid to_agree_op_valid => ??.
  by fold_leibniz.
Qed.

Lemma r2a_shared_agree p a1 a2 :
  r2a_shared p a1 -∗
  r2a_shared p a2 -∗
  ⌜a1 = a2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [/= _ [/= ]]. move => /gmap_view_frag_op_valid [_ /to_agree_op_inv_L ->].
  done.
Qed.

Lemma r2a_shared_agree_big ps p a :
  ([∗ map] p↦z∈ps, r2a_shared p z) -∗
  r2a_shared p a -∗
  ⌜a = default a (ps !! p)⌝.
Proof.
  iIntros "Hps Hp".
  destruct (ps !! p) as [z'|] eqn:Hp => //=.
  iDestruct (big_sepM_lookup with "Hps") as "?"; [done|].
  iAssert ⌜z' = a⌝%I as %?; [|done].
  by iApply (r2a_shared_agree with "[$]").
Qed.

Lemma r2a_shared_alloc_raw p a inj :
  inj !! p = None →
  r2a_shared_auth_raw inj ⊢ |==>
  r2a_shared_auth_raw (<[p := a]>inj) ∗ r2a_shared p a.
Proof.
  move => ?. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  apply prod_update; [done|] => /=. apply prod_update; [|done] => /=.
  rewrite fmap_insert. apply gmap_view_alloc => //.
  by rewrite lookup_fmap fmap_None.
Qed.

Lemma r2a_shared_alloc p a inj :
  inj !! p = None →
  r2a_shared_auth inj ⊢ |==>
  r2a_shared_auth (<[p := a]>inj) ∗ r2a_shared p a.
Proof.
  iIntros (?) "[??]". iMod (r2a_shared_alloc_raw with "[$]") as "[$ #$]"; [done|].
  iModIntro. by iApply big_sepM_insert_2.
Qed.

Lemma r2a_shared_lookup_raw p a inj  :
  r2a_shared_auth_raw inj -∗
  r2a_shared p a -∗
  ⌜inj !! p = Some a⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
  rewrite -uPred.ownM_op. etrans; [apply uPred.ownM_valid|].
  iPureIntro. rewrite -pair_op => -[_ ]/=. setoid_rewrite <-pair_op.
  move => [/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma r2a_shared_lookup p a inj  :
  r2a_shared_auth inj -∗
  r2a_shared p a -∗
  ⌜inj !! p = Some a⌝.
Proof. iIntros "[? _]". by iApply r2a_shared_lookup_raw. Qed.

Lemma r2a_shared_lookup_big inj' inj  :
  r2a_shared_auth inj -∗
  ([∗map] p↦a∈inj', r2a_shared p a) -∗
  ⌜inj' ⊆ inj⌝.
Proof.
  iIntros "Ha Hl". iInduction inj' as [|] "IH" using map_ind.
  { iPureIntro. apply map_empty_subseteq. }
  iDestruct (big_sepM_insert with "Hl") as "[??]"; [done|].
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (r2a_shared_lookup with "Ha [$]") as %?.
  iPureIntro. by apply insert_subseteq_l.
Qed.

Lemma r2a_shared_alloc_big_raw inj inj' :
  inj ⊆ inj' →
  r2a_shared_auth inj ⊢ |==>
  r2a_shared_auth inj'.
Proof.
  iIntros (Hsub) "?". rewrite -(map_difference_union inj inj') //.
  have Hdisj : (inj ##ₘ inj' ∖ inj) by apply map_disjoint_difference_r'.
  rewrite map_union_comm //.
  iInduction (inj' ∖ inj) as [|] "IH" using map_ind forall (Hdisj).
  { by rewrite left_id_L. }
  move: Hdisj => /map_disjoint_insert_r[??].
  iMod ("IH" with "[%] [$]") as "?"; [done|].
  rewrite -insert_union_l.
  iMod (r2a_shared_alloc with "[$]") as "[$ _]". 2: done.
  by apply lookup_union_None.
Qed.

Lemma r2a_shared_alloc_big inj inj' :
  inj ⊆ inj' →
  r2a_shared_auth inj ⊢ |==>
  r2a_shared_auth inj' ∗ [∗ map] p↦a∈inj', r2a_shared p a.
Proof.
  iIntros (Hsub) "?".
  iMod (r2a_shared_alloc_big_raw with "[$]") as "[? ?]"; [done|].
  iModIntro. iSplit!. iFrame.
Qed.

Lemma r2a_shared_auth_shared inj :
  r2a_shared_auth inj ⊢ [∗ map] p↦a∈inj, r2a_shared p a.
Proof. iIntros "[? $]". Qed.

Global Typeclasses Opaque r2a_shared_auth.

Lemma r2a_mem_map_union m1 m2 :
  m1 ##ₘ m2 →
  r2a_mem_map (m1 ∪ m2) ⊣⊢ r2a_mem_map m1 ∗ r2a_mem_map m2.
Proof. apply big_sepM_union. Qed.

Lemma r2a_f2i_full_agree f2i1 f2i2 :
  r2a_f2i_full f2i1 -∗
  r2a_f2i_full f2i2 -∗
  ⌜f2i1 = f2i2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro. move => [/=? [/=? [/=+ ?]]].
  rewrite -Some_op. move => /Some_valid/to_agree_op_valid. done.
Qed.

Lemma r2a_f2i_incl_to_full f2i ins :
 r2a_f2i_incl f2i ins -∗
 ∃ f2i_full, ⌜r2a_f2i_full f2i_full ⊢ r2a_f2i_incl f2i ins⌝ ∗ r2a_f2i_full f2i_full.
Proof. iIntros "[% [% [% $]]]". iPureIntro. iIntros "?". iExists _. by iFrame. Qed.

Lemma r2a_f2i_incl_in_ins f i f2i ins :
  i ∈ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f2i !! f = Some i⌝.
Proof.
  iIntros (Hi) "(%f2i_full&%Hsub&%Hins&Hf2i1) (%&%Hsub2&%&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst. iPureIntro.
  apply: Hins; [done|]. apply: lookup_weaken; [|done]. by simplify_map_eq.
Qed.

Lemma r2a_f2i_incl_agree_f f i1 i2 f2i1 f2i2 ins1 ins2 :
  f2i1 !! f = Some i1 →
  f2i2 !! f = Some i2 →
  r2a_f2i_incl f2i1 ins1 -∗
  r2a_f2i_incl f2i2 ins2 -∗
  ⌜i1 = i2⌝.
Proof.
  move => Hf1 Hf2.
  iIntros "(%f2i_full&%Hsub&%Hins&Hf2i1) (%&%Hsub2&%&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst. iPureIntro.
  move: Hf1 => /(lookup_weaken _ _ _ _).
  move: Hf2 => /(lookup_weaken _ _ _ _). naive_solver.
Qed.

Lemma r2a_f2i_incl_subset_r f2i ins1 ins2 :
  ins2 ⊆ ins1 →
  r2a_f2i_incl f2i ins1 -∗ r2a_f2i_incl f2i ins2.
Proof.
  iIntros (Hsub) "(%f2i_full&%&%&?)". iExists _. iFrame.
  iPureIntro. split!. set_solver.
Qed.

Lemma r2a_f2i_incl_subset_l f2i1 f2i2 ins :
  f2i2 ⊆ f2i1 →
  (∀ i f, i ∈ ins → f2i1 !! f = Some i → f2i2 !! f = Some i) →
  r2a_f2i_incl f2i1 ins -∗ r2a_f2i_incl f2i2 ins.
Proof.
  iIntros (Hsub Hins) "(%f2i_full&%Hf2i&%Hins2&?)". iExists _. iFrame.
  iPureIntro. split!. { by etrans. } naive_solver.
Qed.

Lemma r2a_f2i_incl_union f2i1 f2i2 ins1 ins2 :
  map_agree f2i1 f2i2 →
  (∀ i f, i ∈ ins1 → f2i2 !! f = Some i → f2i1 !! f = Some i) →
  (∀ i f, i ∈ ins2 → f2i1 !! f = Some i → f2i2 !! f = Some i) →
  r2a_f2i_incl (f2i1 ∪ f2i2) (ins1 ∪ ins2) ⊣⊢
  r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2.
Proof.
  move => Hagree Hi1 Hi2. iSplit.
  - iIntros "(%f2i_full&%Hf2i&%Hins&?)". iSplit; iExists _; iFrame; iPureIntro; split.
    + by etrans; [apply map_union_subseteq_l|].
    + move => f i ??. exploit (Hins f i); [set_solver|done|].
      move => /lookup_union_Some_raw. naive_solver.
    + etrans; [|done]. by apply map_union_subseteq_agree_r.
    + move => f i ??. exploit (Hins f i); [set_solver|done|].
      move => /lookup_union_Some_raw. naive_solver.
  - iIntros "[(%f2i_full&%Hf2i1&%Hins1&Hf2i1) (%&%Hf2i2&%Hins2&Hf2i2)]".
    iDestruct (r2a_f2i_full_agree with "Hf2i2 Hf2i1") as %?. subst.
    iExists _. iFrame. iPureIntro. split.
    + by apply map_union_least.
    + move => ????. apply lookup_union_Some_agree; set_solver.
Qed.

Lemma r2a_f2i_incl_single f2i ins f i :
  f2i !! f = Some i →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅.
Proof.
  iIntros (?) "Hf".
  iApply r2a_f2i_incl_subset_l. 3: iApply (r2a_f2i_incl_subset_r with "[$]").
  - by apply map_singleton_subseteq_l.
  - set_solver.
  - set_solver.
Qed.

Lemma r2a_f2i_full_incl f2i f2i2 ins :
 r2a_f2i_full f2i -∗
 r2a_f2i_incl f2i2 ins -∗
 ⌜f2i2 ⊆ f2i⌝.
Proof.
  iIntros "Hf2i (%&%&?&Hf2i2)".
  iDestruct (r2a_f2i_full_agree with "Hf2i Hf2i2") as %?.
  iPureIntro. naive_solver.
Qed.

Lemma r2a_f2i_full_singleton f2i f i ins :
 r2a_f2i_full f2i -∗
 r2a_f2i_incl {[f := i]} ins -∗
 ⌜f2i !! f = Some i⌝.
Proof.
  iIntros "Hf2i Hincl".
  iDestruct (r2a_f2i_full_incl with "[$] [$]") as %?.
  iPureIntro. apply: lookup_weaken; [|done]. by simplify_map_eq.
Qed.

Lemma r2a_f2i_full_to_singleton f2i f i :
 f2i !! f = Some i →
 r2a_f2i_full f2i -∗
 r2a_f2i_incl {[f := i]} ∅.
Proof.
  iIntros (?) "Hf2i".
  iExists _. iFrame. iPureIntro. split; [|done].
  by apply map_singleton_subseteq_l.
Qed.

Global Instance r2a_f2i_full_pers f2i :
  Persistent (r2a_f2i_full f2i).
Proof. apply _. Qed.

Global Instance r2a_f2i_incl_pers f2i ins :
  Persistent (r2a_f2i_incl f2i ins).
Proof. apply _. Qed.

(** Trader for r2a_f2i *)
(* TODO: Make this its own UR like memUR? Not sure, if this would be useful. *)
Section trader.
  Context {PROP : bi}.
  Context (W1 : BiWeakEmbed (uPredI rec_to_asmUR) PROP) (W2 : BiWeakEmbed (uPredI rec_to_asmUR) PROP).
  Context `{!BiAffine PROP}.

  Definition r2a_f2i_trader : PROP := ∃ f2i, ⌈r2a_f2i_full f2i @ W1⌉ ∗ ⌈r2a_f2i_full f2i @ W2⌉.
  Global Instance r2a_f2i_trader_pers : Persistent r2a_f2i_trader.
  Proof using. apply _. Qed.

  Lemma r2a_f2i_trade_full f2i :
    r2a_f2i_trader -∗
    ⌈r2a_f2i_full f2i @ W1⌉ -∗
    ⌈r2a_f2i_full f2i @ W2⌉.
  Proof using BiAffine0.
    iIntros "[% [??]] ?".
    by iDestruct (r2a_f2i_full_agree with "[$] [$]") as %->.
  Qed.

  Lemma r2a_f2i_trade_incl f2i ins :
    r2a_f2i_trader -∗
    ⌈r2a_f2i_incl f2i ins @ W1⌉ -∗
    ⌈r2a_f2i_incl f2i ins @ W2⌉.
  Proof using BiAffine0.
    iIntros "[% [??]] [% [% [% ?]]]".
    iDestruct (r2a_f2i_full_agree with "[$] [$]") as %->.
    iExists _. by iFrame.
  Qed.

  Lemma r2a_f2i_trader_init f2i :
    ⌈r2a_f2i_full f2i @ W1⌉ -∗
    ⌈r2a_f2i_full f2i @ W2⌉ -∗
    r2a_f2i_trader.
  Proof using. iIntros "Hl Hr". iExists _. by iSplitL "Hl". Qed.

End trader.

Lemma r2a_f2i_trader_switch {PROP : bi} (W1 : BiWeakEmbed (uPredI rec_to_asmUR) PROP) (W2 : BiWeakEmbed (uPredI rec_to_asmUR) PROP):
  r2a_f2i_trader W1 W2 -∗ r2a_f2i_trader W2 W1.
Proof. iIntros "[% [??]]". iExists _. iFrame. Qed.

Global Typeclasses Opaque r2a_f2i_trader r2a_f2i_incl r2a_f2i_full.
Global Opaque r2a_f2i_trader.

(** ** f2i_fns_ins_wf *)
Definition f2i_fns_ins_wf (f2i : gmap string Z) (fns : gset string) (ins : gset Z) : Prop :=
  map_Forall (λ f i, i ∈ ins ↔ f ∈ fns) f2i ∧ fns ⊆ dom f2i.

Lemma f2i_fns_ins_wf_in_ins f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  i ∈ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f ∈ fns⌝.
Proof.
  iIntros ([Hall ?] ?) "Hf2i Hf".
  iDestruct (r2a_f2i_incl_in_ins with "Hf2i Hf") as %?; [done|]. iPureIntro.
  by apply/Hall.
Qed.

Lemma f2i_fns_ins_wf_in_fns f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f ∈ fns →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜i ∈ ins⌝.
Proof.
  iIntros ([Hall Hsub] Hf) "Hf2i Hf".
  have /elem_of_dom[??] : f ∈ dom f2i by set_solver.
  iDestruct (r2a_f2i_incl_agree_f with "Hf2i Hf") as %?; [done|by simplify_map_eq|].
  iPureIntro. exploit Hall; [done|]. naive_solver.
Qed.

Lemma f2i_fns_ins_wf_not_in_ins f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  i ∉ ins →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜f ∉ fns⌝.
Proof.
  iIntros (? ?) "Hf2i Hf". iIntros (Hf).
  iDestruct (f2i_fns_ins_wf_in_fns f2i with "[$] [$]") as %?; done.
Qed.

Lemma f2i_fns_ins_wf_not_in_fns f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f ∉ fns →
  r2a_f2i_incl f2i ins -∗
  r2a_f2i_incl {[f := i]} ∅ -∗
  ⌜i ∉ ins⌝.
Proof.
  iIntros (? ?) "Hf2i Hf". iIntros (Hf).
  iDestruct (f2i_fns_ins_wf_in_ins f2i with "[$] [$]") as %?; done.
Qed.

Lemma f2i_fns_ins_wf_in_fns_pure f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f2i !! f = Some i →
  f ∈ fns →
  i ∈ ins.
Proof. unfold f2i_fns_ins_wf, map_Forall. naive_solver. Qed.

Lemma f2i_fns_ins_wf_in_ins_pure f2i fns ins f i :
  f2i_fns_ins_wf f2i fns ins →
  f2i !! f = Some i →
  i ∈ ins →
  f ∈ fns.
Proof. unfold f2i_fns_ins_wf, map_Forall. naive_solver. Qed.

(** * r2a_in_inj *)
Definition r2a_val_rel (iv : val) (av : Z) : uPred rec_to_asmUR :=
  match iv with
  | ValNum z => ⌜av = z⌝
  | ValBool b => ⌜av = bool_to_Z b⌝
  | ValFn f => r2a_f2i_incl {[ f := av ]} ∅
  | ValLoc l => ∃ z, ⌜av = (z + l.2)%Z⌝ ∗ r2a_shared l.1 z
  end.

Global Instance r2a_val_rel_pers iv av : Persistent (r2a_val_rel iv av).
Proof. destruct iv; apply _. Qed.

Definition r2a_in_inj_inv (inj : gmap prov Z) (rem : list prov) :
  uPred rec_to_asmUR :=
    [∗ map] p↦a∈inj, ⌜p ∈ rem⌝ ∨
      ∃ bi bs, p ↦∗h bs ∗ r2a_mem_map (Some <$> kmap (Z.add a) bi) ∗
      [∗ map]o↦av;v∈bi;bs, r2a_val_rel v av.

Definition r2a_in_inj (rem : list prov) : uPred rec_to_asmUR :=
  ∃ inj, r2a_shared_auth inj ∗ r2a_in_inj_inv inj rem.

Lemma r2a_in_inj_inv_borrow p a rem inj :
  p ∉ rem →
  inj !! p = Some a →
  r2a_in_inj_inv inj rem -∗
  ∃ bi bs, r2a_in_inj_inv inj (p::rem) ∗
  p ↦∗h bs ∗ r2a_mem_map (Some <$> kmap (Z.add a) bi) ∗ [∗ map]o↦av;v∈bi;bs, r2a_val_rel v av.
Proof.
  iIntros (??) "Hinj".
  iDestruct (big_sepM_lookup_acc_impl with "Hinj") as "[[%|[% [% $]]] Hinj]";[done..|].
  iSplit!. iApply "Hinj". 2: by iLeft; iPureIntro; set_solver.
  iIntros "!>" (????) "[%|$]". by iLeft; iPureIntro; set_solver.
Qed.

Lemma r2a_in_inj_inv_split inj' inj :
  inj' ⊆ inj →
  r2a_in_inj_inv inj [] ⊣⊢
  r2a_in_inj_inv inj' [] ∗ r2a_in_inj_inv (inj ∖ inj') [].
Proof.
  move => ?. rewrite /r2a_in_inj_inv -big_sepM_union ?map_difference_union//.
  apply map_disjoint_difference_r'.
Qed.

Lemma r2a_in_inj_inv_combine inj' inj :
  r2a_in_inj_inv inj [] -∗
  r2a_in_inj_inv inj' [] -∗
  r2a_in_inj_inv (inj ∪ inj') [].
Proof. apply: big_sepM_union_2. Qed.

Lemma r2a_in_inj_inv_return i p bi bs a rem inj :
  rem !! i = Some p →
  inj !! p = Some a →
  r2a_in_inj_inv inj rem -∗
  p ↦∗h bs -∗
  r2a_mem_map (Some <$> kmap (Z.add a) bi) -∗
  ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av) -∗
  r2a_in_inj_inv inj (delete i rem).
Proof.
  iIntros (??) "Hinj Hs Hi Hvs".
  iDestruct (big_sepM_lookup_acc_impl with "Hinj") as "[Hprev Hinj]";
    [done|].
  iApply "Hinj".
  - iIntros "!>" (????) "[%Hin|$]". iLeft. iPureIntro.
    rewrite delete_take_drop. erewrite <-take_drop_middle in Hin; [|done].
    set_solver.
  - iRight. by iFrame.
Qed.

Lemma r2a_in_inj_inv_return0 p bi bs a rem inj :
  inj !! p = Some a →
  r2a_in_inj_inv inj (p :: rem) -∗
  p ↦∗h bs -∗
  r2a_mem_map (Some <$> kmap (Z.add a) bi) -∗
  ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av) -∗
  r2a_in_inj_inv inj rem.
Proof. iIntros (?) "???". by iApply (r2a_in_inj_inv_return 0 with "[$] [$]"). Qed.


Lemma r2a_in_inj_init :
  r2a_shared_auth ∅ -∗ r2a_in_inj [].
Proof. iIntros "$". by iApply big_sepM_empty. Qed.

Lemma r2a_in_inj_borrow p a rem :
  p ∉ rem →
  r2a_in_inj rem -∗
  r2a_shared p a -∗
  ∃ bi bs, r2a_in_inj (p :: rem) ∗
  p ↦∗h bs ∗ r2a_mem_map (Some <$> kmap (Z.add a) bi) ∗ ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av).
Proof.
  iIntros (?) "[%inj [? Hinj]] Hsh".
  iDestruct (r2a_shared_lookup with "[$] [$]") as %?.
  iDestruct (r2a_in_inj_inv_borrow with "[$]") as (??) "[$ $]" => //.
Qed.

Lemma r2a_in_inj_return i p bi bs a rem :
  rem !! i = Some p →
  r2a_in_inj rem -∗
  r2a_shared p a -∗
  p ↦∗h bs -∗
  r2a_mem_map (Some <$> kmap (Z.add a) bi) -∗
  ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av) -∗
  r2a_in_inj (delete i rem).
Proof.
  iIntros (?) "[%inj [? Hinj]] Hsh Hs Hi Hvs".
  iDestruct (r2a_shared_lookup with "[$] [$]") as %?.
  iExists _. iFrame. by iApply (r2a_in_inj_inv_return with "[$] [$] [$]").
Qed.

Lemma r2a_in_inj_return0 p bi bs a rem :
  r2a_in_inj (p :: rem) -∗
  r2a_shared p a -∗
  p ↦∗h bs -∗
  r2a_mem_map (Some <$> kmap (Z.add a) bi) -∗
  ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av) -∗
  r2a_in_inj rem.
Proof. iIntros "????". by iApply (r2a_in_inj_return 0 with "[$] [$] [$] [$]"). Qed.

Lemma r2a_in_inj_lookup h mem l a v rem:
  h_heap h !! l = Some v →
  l.1 ∉ rem →
  r2a_heapUR_inv h -∗
  r2a_memUR_inv mem -∗
  r2a_in_inj rem -∗
  r2a_shared l.1 a -∗
  ∃ av, ⌜mem !! (a + l.2)%Z = Some (Some av)⌝ ∗ r2a_val_rel v av.
Proof.
  iIntros (??) "Hinvh Hinvm Hinj ?".
  iDestruct (r2a_in_inj_borrow with "[$] [$]") as (bi bs) "[?[?[??]]]"; [done|].
  iDestruct (heapUR_lookup_block1 with "[$] [$]") as %?; [done|].
  iDestruct (big_sepM2_lookup_r with "[$]") as (?) "[% ?]"; [done|].
  iDestruct (big_sepM_lookup with "[$]") as "?". {
    apply lookup_fmap_Some. split!.
    apply/lookup_kmap_Some. by split!. }
  iDestruct (memUR_lookup with "Hinvm [$]") as %?.
  iExists _. iSplit; [done|]. done.
Qed.

Lemma r2a_in_inj_update h mem l a v av rem:
  l.1 ∉ rem →
  heap_alive h l →
  r2a_heapUR_inv h -∗
  r2a_memUR_inv mem -∗
  r2a_in_inj rem -∗
  r2a_shared l.1 a -∗
  r2a_val_rel v av ==∗
  r2a_heapUR_inv (heap_update h l v) ∗
  r2a_memUR_inv (<[a + l.2:=Some av]>mem) ∗
  r2a_in_inj rem.
Proof.
  iIntros (? [? Ha]) "Hinvh Hinvm Hinj #? Hv".
  iDestruct (r2a_in_inj_borrow with "[$] [$]") as (bi bs) "[?[?[??]]]"; [done|].
  iDestruct (heapUR_lookup_block with "Hinvh [$]") as %<-.
  iDestruct (big_sepM2_lookup_r with "[$]") as (??) "#_".
  { move: Ha. by rewrite h_block_lookup2. }
  iDestruct (big_sepM_insert_acc with "[$]") as "[? Hc]". {
    apply lookup_fmap_Some. split!.
    apply/lookup_kmap_Some. by split!. }
  iMod (heapUR_update_in_block with "[$] [$]") as "[$ ?]"; [eexists _; done|].
  iMod (memUR_update with "[$] [$]") as "[$ Hm]" => /=.
  iSpecialize ("Hc" with "Hm").
  rewrite -fmap_insert -kmap_insert.
  iModIntro.
  iApply (r2a_in_inj_return0 with "[$] [$] [$] [$]").
  by iApply (big_sepM2_insert_2 with "[Hv] [$]").
Qed.

Lemma r2a_in_inj_share p a rem bi bs :
  p ∉ rem →
  r2a_in_inj rem -∗
  p ↦∗h bs -∗
  r2a_mem_map (Some <$> kmap (Z.add a) bi) -∗
  ([∗ map]o↦av;v∈bi;bs, r2a_val_rel v av)  ==∗
  r2a_in_inj rem ∗
  r2a_shared p a.
Proof.
  iIntros (?) "[%inj[??]] ???".
  destruct (inj !! p) eqn:?. {
    iDestruct (r2a_in_inj_inv_borrow with "[$]") as (??) "[?[??]]"; [done..|].
    iDestruct (heapUR_block_excl with "[$] [$]") as %[]. }
  iMod (r2a_shared_alloc with "[$]") as "[? #$]"; [done|]. iModIntro.
  iExists _. iFrame.
  iApply big_sepM_insert; [done|]. iFrame. iRight. by iFrame.
Qed.

Lemma r2a_in_inj_free h l a rem n:
  l.1 ∉ rem →
  l.2 = 0%Z →
  heap_range h l n →
  r2a_heapUR_inv h -∗
  r2a_shared l.1 a -∗
  r2a_in_inj rem ==∗
  r2a_in_inj rem ∗
  r2a_heapUR_inv (heap_free h l) ∗
  r2a_mem_uninit a n.
Proof.
  iIntros (? Hl ?) "Hinvh #? Hinj".
  iDestruct (r2a_in_inj_borrow with "[$] [$]") as (??) "[? [? [Hm ?]]]"; [done|].
  iDestruct (heapUR_lookup_block with "Hinvh [$]") as %<-.
  iMod (heapUR_free with "[$] [$]") as "[$ ?]".
  iDestruct (big_sepM2_dom with "[$]") as %Hdom.
  iModIntro.
  iSplitR "Hm".
  - iApply (r2a_in_inj_return0 _ ∅ with "[$] [$] [$]"). 2: by iApply big_sepM2_empty.
    rewrite kmap_empty fmap_empty. by iApply big_sepM_empty.
  - rewrite /r2a_mem_uninit -(fmap_add_seqZ0 a) big_sepL_fmap.
    rewrite -(big_sepM_zero_block _ (λ n _, ∃ x, _)%I).
    rewrite big_sepM_fmap big_sepM_kmap_intro.
    iApply (big_sepM_impl_strong' with "Hm").
    iIntros "!>" (??) "Hb". iIntros (Hz%elem_of_dom_2).
    erewrite <-heap_range_dom_h_block1, <-Hdom in Hz; [|done..].
    move: Hz => /elem_of_dom[? ->].
    iExists _. iFrame.
Qed.


(** * invariants *)
Definition GUARD_PAGE_SIZE : Z := 4096.

(* gp is lower end of guard page *)
Definition r2a_guard_page (gp : Z) : uPred rec_to_asmUR :=
  r2a_mem_map (map_seqZ gp (replicate (locked Z.to_nat GUARD_PAGE_SIZE) None)).

Definition r2a_mem_stack (sp : Z) (ssz : N) : uPred rec_to_asmUR :=
  r2a_guard_page (sp - Z.of_N ssz - GUARD_PAGE_SIZE) ∗
  r2a_mem_uninit (sp - Z.of_N ssz) (Z.of_N ssz).

Definition r2a_mem_inv (sp : Z) (ssz : N) (mem : gmap Z (option Z)) : uPred rec_to_asmUR :=
  r2a_mem_stack sp ssz ∗ r2a_memUR_inv mem.

Definition r2a_heap_inv (h : heap_state) : uPred rec_to_asmUR :=
  r2a_heapUR_inv h ∗ r2a_in_inj [] ∗ r2a_statics (h_static_provs h).

Definition r2a_args (o : nat) (vs : list val) (rs : gmap string Z) : uPred rec_to_asmUR :=
  ([∗ list] i↦v∈vs, ∃ r,
      ⌜args_registers !! (o + i)%nat = Some r⌝ ∗
      r2a_val_rel v (rs !!! r)).

Definition r2a_args_pure (o : nat) (vs : list Z) (rs : gmap string Z) : Prop :=
  ∀ i v, vs !! i = Some v → ∃ r, args_registers !! (o + i)%nat = Some r ∧ rs !!! r = v.

Lemma r2a_mem_uninit_split n a l :
  0 ≤ n ≤ l →
  r2a_mem_uninit a l ⊣⊢ r2a_mem_uninit a n ∗ r2a_mem_uninit (a + n) (l - n).
Proof.
  move => ?. rewrite /r2a_mem_uninit.
  have {1} -> : l = (n + (l - n)) by lia.
  rewrite seqZ_app; [|lia..]. rewrite big_sepL_app. done.
Qed.

Lemma r2a_mem_uninit_alt1 a l :
  0 ≤ l →
  r2a_mem_uninit a l -∗ ∃ vs, ⌜length vs = Z.to_nat l⌝ ∗ r2a_mem_map (map_seqZ a (Some <$> vs)).
Proof.
  iIntros (Hl) "Hm". rewrite - {1}(Z2Nat.id l) //.
  iInduction (Z.to_nat l) as [|l'] "IH" forall (a).
  { iExists []. iSplit!. }
  rewrite /r2a_mem_uninit Nat2Z.inj_succ seqZ_cons ?Z.pred_succ /=; [|lia].
  iDestruct "Hm" as "[[%v ?] ?]". iDestruct ("IH" with "[$]") as (vs ?) "Hm".
  iExists (v :: vs) => /=. iSplit!. rewrite big_sepM_insert; [by iFrame|].
  apply lookup_map_seqZ_None. lia.
Qed.

Lemma r2a_mem_uninit_alt2 a vs :
  r2a_mem_map (map_seqZ a (Some <$> vs)) -∗
  r2a_mem_uninit a (length vs).
Proof.
  iIntros "Hvs". iInduction vs as [|v vs] "IH" forall (a); csimpl.
  { rewrite /r2a_mem_uninit /=. done. }
  rewrite big_sepM_insert; [|apply lookup_map_seqZ_None; lia].
  iDestruct "Hvs" as "[??]". iDestruct ("IH" with "[$]") as "?".
  rewrite /r2a_mem_uninit /= Nat2Z.inj_succ (seqZ_cons a) ?Z.pred_succ /=; [|lia]. by iFrame.
Qed.

Section trader.
  Context {PROP : bi}.
  Context (W1 : BiWeakEmbed (uPredI rec_to_asmUR) PROP) (W2 : BiWeakEmbed (uPredI rec_to_asmUR) PROP).
  Context `{!BiBUpd PROP} `{!BiAffine PROP} `{!BiWeakEmbedBUpd W1} `{!BiWeakEmbedBUpd W2}.

  Lemma r2a_mem_uninit_trade a len mem :
    memUR_trader W1 W2 r2a_mem r2a_mem -∗
    ⌈memUR_inv r2a_mem mem @ W2⌉ -∗
    ⌈r2a_mem_uninit a len @ W2⌉ ==∗⌈W1⌉
    memUR_trader W1 W2 r2a_mem r2a_mem ∗
    ⌈memUR_inv r2a_mem mem @ W2⌉ ∗
    ⌈r2a_mem_uninit a len @ W1⌉.
  Proof using BiAffine0 BiWeakEmbedBUpd0 BiWeakEmbedBUpd1.
    iIntros "Ht Hinv Hl".
    rewrite /r2a_mem_uninit !weak_embed_big_sepL.
    iMod (big_sepL_impl_weak_bupd_frame with "Hl [] [-]") as "[$ ?]". 2: iAccu. 2: by iFrame.
    iIntros "!>" (???) "[??] [% ?]".
    by iMod (memUR_trade_ptsto with "[$] [$] [$]") as "[$ [$ $]]".
  Qed.

  Lemma r2a_mem_stack_trade sp ssz mem :
    memUR_trader W1 W2 r2a_mem r2a_mem -∗
    ⌈memUR_inv r2a_mem mem @ W2⌉ -∗
    ⌈r2a_mem_stack sp ssz @ W2⌉ ==∗⌈W1⌉
    memUR_trader W1 W2 r2a_mem r2a_mem ∗
    ⌈memUR_inv r2a_mem mem @ W2⌉ ∗
    ⌈r2a_mem_stack sp ssz @ W1⌉.
  Proof using BiAffine0 BiWeakEmbedBUpd0 BiWeakEmbedBUpd1.
    iIntros "Ht Hinv [? Huninit]".
    iMod (memUR_trade_ptsto_big with "[$] [$] [$]") as "[? [? $]]".
    iMod (r2a_mem_uninit_trade with "[$] [$] [$]") as "?".
    by iModIntro.
  Qed.
End trader.

Lemma r2a_guard_page_lookup a sp ssz mem :
  sp - Z.of_N ssz - GUARD_PAGE_SIZE ≤ a < sp - Z.of_N ssz →
  r2a_mem_inv sp ssz mem -∗
  ⌜mem !! a = Some None⌝.
Proof.
  iIntros (?) "((Hgp&?)&Hauth)". rewrite /r2a_guard_page.
  iDestruct (memUR_lookup_big with "[$] [$]") as %Hsub.
  iPureIntro. apply: lookup_weaken; [|done]. apply lookup_map_seqZ_Some. split; [lia|].
  apply lookup_replicate. split!. unlock. lia.
Qed.

Lemma r2a_mem_lookup a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  a ↦m v -∗
  ⌜mem !! a = Some v⌝.
Proof.
  iIntros "((?&?)&Hauth) Hconst".
  by iDestruct (memUR_lookup with "Hauth Hconst") as %?.
Qed.

Lemma r2a_mem_lookup_big sp ssz m mem :
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_map m -∗
  ⌜m ⊆ mem⌝.
Proof.
  iIntros "((?&?)&Hauth) Hconst".
  by iDestruct (memUR_lookup_big with "Hauth Hconst") as %?.
Qed.

Lemma r2a_mem_range a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  a ↦m (Some v) -∗
  ⌜¬ (sp - Z.of_N ssz ≤ a < sp)⌝.
Proof.
  iIntros "Hinv Hconst" (?).
  iDestruct (r2a_mem_lookup with "[$] [$]") as %?.
  destruct (decide (sp - Z.of_N ssz ≤ a)).
  2: { iDestruct (r2a_guard_page_lookup a with "[$]") as %?; [lia|]. simplify_eq. }
  iDestruct "Hinv" as "((?&Hsp)&?)".
  iDestruct (big_sepL_lookup _ _ (Z.to_nat (a - (sp - Z.of_N ssz))) a with "Hsp") as (?) "?".
  - apply lookup_seqZ. lia.
  - iDestruct (memUR_ptsto_excl with "[$] [$]") as %[].
Qed.

Lemma r2a_mem_exists n sp ssz mem :
  0 < n ≤ GUARD_PAGE_SIZE →
  r2a_mem_inv sp ssz mem -∗
  ⌜∃ v, mem !! (sp - n) = Some v⌝.
Proof.
  iIntros (?) "Hinv".
  destruct (decide (n ≤ Z.of_N ssz)).
  - iDestruct "Hinv" as "((?&Hsp)&?)".
    iDestruct (big_sepL_lookup _ _ (Z.to_nat (Z.of_N ssz - n)) (sp - n) with "Hsp") as (?) "?".
    * apply lookup_seqZ. lia.
    * iDestruct (memUR_lookup with "[$] [$]") as %?. iSplit!.
  - iDestruct (r2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + iSplit!.
Qed.

Lemma r2a_mem_alloc n sp ssz mem v :
  mem !! (sp - n) = Some (Some v) →
  0 ≤ n ≤ GUARD_PAGE_SIZE →
  r2a_mem_inv sp ssz mem ==∗ ⌜n ≤ Z.of_N ssz⌝ ∗ r2a_mem_inv (sp - n) (ssz - Z.to_N n) mem ∗ r2a_mem_uninit (sp - n) n.
Proof.
  iIntros (? ?) "Hinv". iModIntro.
  destruct (decide (n ≤ Z.of_N ssz)).
  - iDestruct "Hinv" as "((?&?)&?)".
    rewrite (r2a_mem_uninit_split (Z.of_N ssz - n)). 2: lia.
    iDestruct!.
    have ->: (sp - Z.of_N ssz + (Z.of_N ssz - n)) = (sp - n) by lia.
    have ->: (Z.of_N ssz - (Z.of_N ssz - n)) = n by lia. iSplit!. iFrame.
    unfold r2a_mem_stack.
    have -> : (sp - n - Z.of_N (ssz - Z.to_N n) - GUARD_PAGE_SIZE) = (sp - Z.of_N ssz - GUARD_PAGE_SIZE) by lia.
    have -> : (sp - n - Z.of_N (ssz - Z.to_N n)) = (sp - Z.of_N ssz) by lia.
    have -> : (Z.of_N (ssz - Z.to_N n)) = (Z.of_N ssz - n) by lia.
    iFrame.
  - iDestruct (r2a_guard_page_lookup (sp - n) with "[$]") as %?.
    + lia.
    + simplify_eq.
Qed.

Lemma r2a_mem_update v' a v mem sp ssz:
  r2a_mem_inv sp ssz mem -∗
  a ↦m v ==∗
  r2a_mem_inv sp ssz (<[a := Some v']> mem) ∗ a ↦m (Some v').
Proof.
  iDestruct 1 as "((?&?)&Hauth)".
  iIntros "Hconst".
  iDestruct (memUR_lookup with "[$] [$]") as %?.
  iMod (memUR_update with "[$] [$]") as "[? $]". iModIntro.
  by iFrame.
Qed.

Lemma r2a_mem_update_big sp ssz mem mo mo' :
  dom mo = dom mo' →
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_map mo ==∗
  r2a_mem_map mo' ∗ r2a_mem_inv sp ssz (mo' ∪ mem).
Proof.
  iIntros (Hdom) "[$ Hmem] Hconst".
  iMod (memUR_free_big with "[$] [$]").
  iMod (memUR_alloc_big with "[$]") as "[? $]".
  { apply map_disjoint_spec => ???. rewrite !lookup_difference_Some -not_elem_of_dom Hdom not_elem_of_dom.  naive_solver. }
  iModIntro.
  by rewrite (map_difference_eq_dom_L _ mo mo') // -map_difference_union_r.
Qed.

Lemma r2a_mem_delete n mem sp ssz:
  0 ≤ n →
  r2a_mem_inv sp ssz mem -∗
  r2a_mem_uninit sp n ==∗
  r2a_mem_inv (sp + n) (ssz + Z.to_N n) mem.
Proof.
  move => ?.
  iDestruct 1 as "((?&?)&Hauth)".
  iIntros "Huninit". iModIntro. iFrame.
  rewrite /r2a_mem_stack.
  have -> : (sp + n - Z.of_N (ssz + Z.to_N n)) = sp - Z.of_N ssz by lia. iFrame.
  have -> : (Z.of_N (ssz + Z.to_N n)) = Z.of_N ssz + n by lia.
  iApply (r2a_mem_uninit_split (Z.of_N ssz)); [lia|]. iFrame.
  have -> : (sp - Z.of_N ssz + Z.of_N ssz) = sp by lia.
  have -> : (Z.of_N ssz + n - Z.of_N ssz) = n by lia.
  done.
Qed.

Lemma r2a_mem_delete_big adrs mem sp sp' ssz:
  sp ≤ sp' →
  Forall (λ a, sp ≤ a < sp') adrs →
  length adrs = Z.to_nat (sp' - sp) →
  r2a_mem_inv sp ssz mem -∗
  ([∗ list] a∈adrs, ∃ v, a ↦m (Some v)) ==∗
  r2a_mem_inv sp' (ssz + Z.to_N (sp' - sp)) mem.
Proof.
  iIntros (? Hall ?) "Hinv Ha".
  iAssert ⌜NoDup adrs⌝%I as %?. {
    rewrite NoDup_alt. iIntros (a1 a2 ???).
    destruct (decide (a1 = a2)) => //.
    rewrite (big_sepL_delete _ _ a1); [|done].
    rewrite (big_sepL_delete _ _ a2); [|done].
    iDestruct!. case_decide => //. iDestruct!.
    iDestruct (memUR_ptsto_excl with "[$] [$]") as %[].
  }
  iAssert ⌜∀ a, a ∈ adrs → a ∈ seqZ sp (sp' - sp)⌝%I as %Hsub%NoDup_submseteq => //. {
    iIntros (??).
    iDestruct (big_sepL_elem_of with "[$]") as (?) "?"; [done|].
    iDestruct (r2a_mem_range with "[$] [$]") as %?.
    iPureIntro. apply elem_of_seqZ. move: Hall => /Forall_forall. naive_solver lia.
  }
  move: Hsub => /submseteq_length_Permutation ->. 2: { rewrite length_seqZ. lia. }
  have [n [-> ->]]: ∃ n : nat, sp' - sp = Z.of_nat n ∧ sp' = sp + Z.of_nat n.
  { eexists (Z.to_nat (sp' - sp)). lia. }
  iApply (r2a_mem_delete with "[$] [$]"). lia.
Qed.

Lemma r2a_mem_swap_stack sp1 ssz1 sp2 ssz2 mem:
  r2a_mem_inv sp1 ssz1 mem -∗
  r2a_mem_stack sp2 ssz2 -∗
  r2a_mem_inv sp2 ssz2 mem ∗ r2a_mem_stack sp1 ssz1.
Proof. iIntros "[??] ?". iFrame. Qed.

Lemma r2a_heap_get_statics h :
  r2a_heap_inv h -∗ r2a_statics (h_static_provs h).
Proof. by iDestruct 1 as "[Hsh [Hs Hag]]". Qed.

Lemma r2a_heap_alloc h l n:
  heap_is_fresh h l →
  r2a_heap_inv h ==∗
  r2a_heap_inv (heap_alloc h l n) ∗ l.1 ↦∗h zero_block n.
Proof.
  iIntros ([Hl [? ?]]).
  iDestruct 1 as "[Hinv [Hsh Hag]]".
  iMod (heapUR_alloc with "Hinv") as "[Hinv $]"; [done|].
  iModIntro. iFrame. rewrite h_static_provs_heap_alloc //.
Qed.

Lemma r2a_heap_update h l v v':
  r2a_heap_inv h -∗
  l ↦h v ==∗
  r2a_heap_inv (heap_update h l v') ∗ l ↦h v'.
Proof.
  iDestruct 1 as "[Hinv [Hsh Hag]]". iIntros "Hc".
  iMod (heapUR_update with "Hinv Hc") as "[$ $]".
  iModIntro. iFrame. by rewrite h_static_provs_heap_update.
Qed.

Lemma r2a_heap_free h l b:
  is_ProvBlock l.1 →
  r2a_heap_inv h -∗
  l.1 ↦∗h b ==∗
  r2a_heap_inv (heap_free h l).
Proof.
  iDestruct 1 as "[Hinv [Hsh Hag]]". iIntros "Hc".
  iMod (heapUR_free with "Hinv Hc") as "[$ _]".
  iModIntro. iFrame. by rewrite h_static_provs_heap_free.
Qed.

Lemma r2a_heap_lookup_shared h l v z mem ss ssz:
  h_heap h !! l = Some v →
  r2a_heap_inv h -∗
  r2a_mem_inv ss ssz mem -∗
  r2a_shared l.1 z -∗
  ∃ av, ⌜mem !! (z + l.2)%Z = Some (Some av)⌝ ∗ r2a_val_rel v av.
Proof.
  iIntros (?).
  iDestruct 1 as "[Hinv [Hsh Hag]]".
  iIntros "[? Hmem] Hl".
  iApply (r2a_in_inj_lookup with "[$] [$] [$] [$]"); [done|].
  set_solver.
Qed.

Lemma r2a_heap_alloc_shared h l a n:
  heap_is_fresh h l →
  r2a_heap_inv h -∗
  ([∗ list] a'∈seqZ a n, a' ↦m (Some 0)) ==∗
  r2a_shared l.1 a ∗ r2a_heap_inv (heap_alloc h l n).
Proof.
  iIntros ([?[??]]) "Hinv Ha".
  iMod (r2a_heap_alloc _ _ n with "Hinv") as "[Hinv Hl]"; [done..|].
  iDestruct "Hinv" as "[Hinv [Hsh Hag]]".
  iMod (r2a_in_inj_share _ _ _ (const 0 <$> zero_block n) with "Hsh Hl [Ha] []") as "[Hsh $]". { set_solver. }
  3: by iFrame.
  - rewrite big_sepM_fmap big_sepM_kmap_intro big_sepM_fmap.
    rewrite big_sepM_zero_block.
    by rewrite -(fmap_add_seqZ0 a) big_sepL_fmap.
  - rewrite big_sepM2_fmap_l.
    iApply big_sepM_sepM2_diag.
    iApply big_sepM_intro.
    iIntros "!>" (??[-> ?]%zero_block_lookup_Some).
    done.
Qed.

Lemma r2a_share a h m p b:
  r2a_heap_inv h -∗
  r2a_mem_map m -∗
  p ↦∗h b -∗
  □ (∀ z v, ⌜b !! z = Some v⌝ -∗
      ∃ av, ⌜m !! (a + z)%Z = Some (Some av)⌝ ∗ r2a_val_rel v av) ==∗
  r2a_shared p a ∗ r2a_heap_inv h.
Proof.
  iIntros "Hinv Hm Hh #Hmap".
  iDestruct "Hinv" as "[Hinv [Hsh Hag]]".
  iAssert (⌜∀ z v, b !! z = Some v → ∃ av, m !! (a + z)%Z = Some (Some av)⌝)%I as %Hb. {
    iIntros (z v Hb).
    iDestruct ("Hmap" $! _ _ Hb) as (?) "[% ?]".
    iPureIntro. naive_solver. }
  iMod (r2a_in_inj_share _ _ _ (map_imap (λ i v, (m!!!(a+i))) b) with "Hsh Hh [Hm] []") as "[Hsh $]". { set_solver. }
  3: by iFrame.
  - iApply (big_sepM_subseteq with "Hm").
    apply map_subseteq_spec => ?? /lookup_fmap_Some[?[? /lookup_kmap_Some[?[? ]]]].
    rewrite map_lookup_imap => /bind_Some[? [? Htot]]. simplify_eq.
    odestruct Hb; [done|].
    erewrite (lookup_total_correct m) in Htot; [|done]. naive_solver.
  - iApply big_sepM2_intro. {
      move => ?. rewrite map_lookup_imap /is_Some. setoid_rewrite bind_Some.
      split; [naive_solver|].
      move => [? Hl]. odestruct Hb; [done|].
      split!. by apply lookup_total_correct. }
    iIntros "!>" (??? Hm Hl).
    iDestruct ("Hmap" $! _ _ Hl) as (??) "?".
    move: Hm. rewrite map_lookup_imap => /bind_Some[? [?]].
    erewrite (lookup_total_correct m); [|done] => ?. naive_solver.
Qed.

Lemma r2a_heap_free_shared h l a n:
  is_ProvBlock l.1 →
  l.2 = 0 →
  heap_range h l n →
  r2a_heap_inv h -∗
  r2a_shared l.1 a ==∗
  r2a_mem_uninit a n ∗ r2a_heap_inv (heap_free h l).
Proof.
  iIntros (Hblok Hl2 Hr).
  iDestruct 1 as "[Hinv [Hsh Hag]]". iIntros "Hl".
  iMod (r2a_in_inj_free with "[$] [$] [$]") as "[$ [$$]]"; [set_solver|done|done|].
  by rewrite h_static_provs_heap_free.
Qed.

Lemma r2a_heap_free_list_shared h ls h' adrs:
  heap_free_list ls h h' →
  Forall (λ l, l.2 = 0) ls.*1 →
  r2a_heap_inv h -∗
  ([∗ list] l;a∈ls.*1;adrs, r2a_shared l.1 a) ==∗
  ([∗ list] a∈mjoin (zip_with (λ a n, seqZ a n) adrs ls.*2), ∃ v, a ↦m (Some v)) ∗
    r2a_heap_inv h'.
Proof.
  elim: ls h h' adrs => /=.
  { iIntros (??? -> ?) "? Hs". iDestruct (big_sepL2_nil_inv_l with "Hs") as %->. iModIntro. by iFrame. }
  move => [l n] ls IH h h' [|a adrs]; try by [iIntros]; csimpl => [[?[??]]] /Forall_cons[??]; iIntros "Hh [Hl Hs]".
  iMod (r2a_heap_free_shared with "Hh Hl") as "[$ ?]"; [done..|].
  by iApply (IH with "[$]").
Qed.

Lemma r2a_heap_update_shared h l v z mem ss av ssz:
  heap_alive h l →
  r2a_heap_inv h -∗
  r2a_mem_inv ss ssz mem -∗
  r2a_shared l.1 z -∗
  r2a_val_rel v av ==∗
  r2a_heap_inv (heap_update h l v) ∗ r2a_mem_inv ss ssz (<[z + l.2 := Some av]>mem).
Proof.
  iIntros (?).
  iDestruct 1 as "[Hinv [Hsh Hag]]".
  iIntros "[? Hmem] Hl Hv".
  iMod (r2a_in_inj_update with "[$] [$] [$] [$] [$]") as "[$ [$ $]]"; [set_solver| done |].
  iFrame.
  by rewrite h_static_provs_heap_update.
Qed.

Lemma r2a_res_init' provs f2i :
  satisfiable (r2a_memUR_inv ∅ ∗
               r2a_heapUR_inv ∅ ∗
               r2a_shared_auth ∅ ∗
               r2a_statics provs ∗
               r2a_f2i_full f2i).
Proof.
  apply: (satisfiable_init (Some (to_agree provs),
              (gmap_view_auth (DfracOwn 1) (to_agree <$> ∅),
                (Some (to_agree f2i) :> (optionUR (agreeR (leibnizO (gmap string Z)))),
                  (heapUR_init, memUR_init))))). {
    split; [done|] => /=.
    split; [by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1))|].
    split; [done|] => /=.
    split; [apply heapUR_init_valid|].
    apply memUR_init_valid.
  }
  rewrite (pair_split (Some _)) uPred.ownM_op.
  rewrite (pair_split (gmap_view_auth _ _)) pair_op_2 uPred.ownM_op.
  rewrite (pair_split (Some (to_agree f2i) :> (optionUR (agreeR (leibnizO (gmap string Z)))))) !pair_op_2  uPred.ownM_op.
  rewrite (pair_split (heapUR_init)) !pair_op_2 uPred.ownM_op.
  iIntros!. rewrite -!heapUR_init_own -!memUR_init_own /r2a_shared_auth big_sepM_empty. by iFrame.
Qed.

Lemma r2a_res_init mem h f2i:
  satisfiable (r2a_memUR_inv mem ∗ ([∗ map] a↦v∈mem, a ↦m v) ∗
   r2a_heap_inv h ∗ ([∗ map] p↦b ∈ h_blocks h, p ↦∗h b) ∗
   r2a_f2i_full f2i).
Proof.
  apply: satisfiable_bmono; [apply (r2a_res_init' (h_static_provs h) f2i)|].
  iIntros "[Hmem [Hh [Hsh [$ $]]]]".
  iDestruct (r2a_in_inj_init with "[$]") as "$".
  iMod (memUR_alloc_big with "Hmem") as "[? $]".
  { apply map_disjoint_empty_r. } rewrite right_id_L. iFrame.
  iMod (heapUR_alloc_blocks with "Hh") as "[? $]".
  { set_solver. } rewrite right_id_L heap_from_blocks_h_blocks.
  by iFrame.
Qed.

Definition r2a_mem_stack_mem (sp : Z) (ssz : N) : gmap Z (option Z) :=
  map_seqZ (sp - Z.of_N ssz - GUARD_PAGE_SIZE) (replicate (locked Z.to_nat GUARD_PAGE_SIZE) None) ∪
  map_seqZ (sp - Z.of_N ssz) (Some <$> replicate (N.to_nat $ ssz) 0).

Lemma r2a_mem_stack_init ssz sp:
  r2a_mem_map (r2a_mem_stack_mem sp ssz) -∗
  r2a_mem_stack sp ssz.
Proof.
  iIntros "Hm". rewrite /r2a_mem_stack_mem big_sepM_union.
  2: { apply map_disjoint_spec => ???. rewrite !lookup_map_seqZ_Some.
       rewrite list_lookup_fmap fmap_Some. setoid_rewrite lookup_replicate. unlock. lia. }
  iDestruct "Hm" as "[$ ?]".
  have {3} ->: (Z.of_N ssz) = length $ replicate (N.to_nat ssz) 0.
  { rewrite length_replicate. lia. }
  by iApply r2a_mem_uninit_alt2.
Qed.

Lemma r2a_args_nil o rs:
  r2a_args o [] rs ⊣⊢ True.
Proof. done. Qed.

Lemma r2a_args_cons1 o v vs rs:
  r2a_args o (v::vs) rs ⊣⊢ (∃ r, ⌜args_registers !! o = Some r⌝ ∗ r2a_val_rel v (rs !!! r)) ∗ r2a_args (S o) vs rs.
Proof.
  rewrite /r2a_args. setoid_rewrite Nat.add_succ_l. setoid_rewrite <-Nat.add_succ_r => /=.
  f_equiv. setoid_rewrite Nat.add_0_r. iSplit; iIntros!; iSplit!.
Qed.

Lemma r2a_args_cons o v vs rs r:
  args_registers !! o = Some r →
  r2a_args o (v::vs) rs ⊣⊢ r2a_val_rel v (rs !!! r) ∗ r2a_args (S o) vs rs.
Proof. move => ?. rewrite r2a_args_cons1. iSplit; iIntros!; iSplit!. Qed.

Lemma r2a_args_pure_mono o avs rs rs':
  map_preserved args_registers rs rs' →
  r2a_args_pure o avs rs →
  r2a_args_pure o avs rs'.
Proof.
  move => Hrs Ha ???. have [?[??]]:= Ha _ _ ltac:(done). split!.
  etrans; [|done].
  symmetry. apply: Hrs. by apply: elem_of_list_lookup_2.
Qed.

Lemma r2a_args_mono o vs rs rs':
  map_preserved (drop o args_registers) rs rs' →
  r2a_args o vs rs -∗
  r2a_args o vs rs'.
Proof.
  iIntros (Hpre) "Hargs". iApply (big_sepL_impl with "Hargs").
  iIntros "!>" (???) "[% [% ?]]". iExists _. iFrame. iSplit; [done|].
  rewrite ->Hpre; [done|].
  apply elem_of_list_lookup. setoid_rewrite lookup_drop. naive_solver.
Qed.

Lemma r2a_args_intro o vs avs rs:
  r2a_args_pure o avs rs →
  ([∗ list] v;av∈vs;avs, r2a_val_rel v av) -∗
  r2a_args o vs rs.
Proof.
  iIntros (Hpure) "Hvs".
  iInduction vs as [|v vs] "IH" forall (avs o Hpure). { by rewrite r2a_args_nil. }
  iDestruct (big_sepL2_cons_inv_l with "Hvs") as (???) "[??]". simplify_eq.
  have [?[]]:= Hpure 0%nat _ ltac:(done). rewrite Nat.add_0_r => ??. simplify_eq.
  rewrite r2a_args_cons; [|done].
  iDestruct ("IH" with "[%] [$]") as "$". 2: by iSplit!.
  move => ???. rewrite Nat.add_succ_l -Nat.add_succ_r. by apply Hpure.
Qed.

Lemma r2a_args_elim o vs rs:
  r2a_args o vs rs -∗
  ∃ avs, ⌜r2a_args_pure o avs rs⌝ ∗ ([∗ list] v;av∈vs;avs, r2a_val_rel v av).
Proof.
  iIntros "Hvs".
  iInduction vs as [|v vs] "IH" forall (o). { iExists []. by iSplit!. }
  iDestruct (r2a_args_cons1 with "Hvs") as "[??]". iDestruct!.
  iDestruct ("IH" with "[$]") as (? Hpure) "?".
  iExists (_::_). iSplit!; [|done..].
  move => i ? /lookup_cons_Some[[??]|[??]]; simplify_eq.
  - rewrite Nat.add_0_r. split!.
  - destruct i; [lia|]. rewrite Nat.add_succ_r -Nat.add_succ_l . apply Hpure.
    simplify_eq/=. rewrite ->Nat.sub_0_r in *. done.
Qed.

(** * Definition of [rec_to_asm] *)
Record rec_to_asm_stack_item := R2AI {
  r2as_extern : bool;
  r2as_ret : Z;
  r2as_regs : gmap string Z;
}.
Add Printing Constructor rec_to_asm_stack_item.

Record rec_to_asm_state := R2A {
  r2a_calls : list rec_to_asm_stack_item;
  r2a_last_regs : gmap string Z;
}.
Add Printing Constructor rec_to_asm_state.

Definition rec_to_asm_pre (ins : gset Z)
 (e : asm_event) (s : rec_to_asm_state) :
 prepost (rec_event * rec_to_asm_state) rec_to_asmUR :=
  match e with
  | (i, EAJump rs mem) =>
    (* env chooses if this is a function call or return *)
    pp_quant $ λ b : bool,
    pp_prop (i = Incoming) $
    pp_quant $ λ h,
    pp_quant $ λ ssz,
    pp_quant $ λ vs,
    pp_quant $ λ avs,
    pp_star (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv h ∗ [∗ list] v;av∈vs;avs, r2a_val_rel v av) $
    if b then
      (* env chooses function name *)
      pp_quant $ λ f,
      (* env chooses arguments *)
      pp_prop (r2a_args_pure 0 avs rs) $
      (* env proves that pc is in ins *)
      pp_prop  (rs !!! "PC" ∈ ins) $
      (* env proves it calls the right address *)
      pp_star (r2a_f2i_incl {[ f := rs !!! "PC" ]} ∅) $
      (* env proves that ret is not in ins *)
      pp_prop (rs !!! "R30" ∉ ins) $
      (* track the registers and return address (false means ret belongs to env) *)
      pp_end ((i, ERCall f vs h), R2A ((R2AI false (rs !!! "R30") rs)::s.(r2a_calls)) rs)
    else
      (* env chooses return value *)
      pp_quant $ λ v,
      pp_quant $ λ av,
      pp_prop (vs = [v] ∧ avs = [av]) $
      (* env chooses old registers *)
      pp_quant $ λ rsold,
      (* env chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (true means pc belongs to the program) *)
      pp_prop (s.(r2a_calls) = (R2AI true (rs !!! "PC") rsold)::cs') $
      (* env proves that rs is updated correctly *)
      pp_prop (r2a_regs_ret rs rsold av) $
      pp_end ((i, ERReturn v h), R2A cs' rs)
  | _ => pp_prop False $ pp_quant $ λ e, pp_end e
  end.

Definition rec_to_asm_post (ins : gset Z)
           (e : rec_event) (s : rec_to_asm_state) : prepost (asm_event * rec_to_asm_state) rec_to_asmUR :=
  pp_prop (e.1 = Outgoing) $
  pp_quant $ λ rs,
  pp_quant $ λ mem,
  pp_quant $ λ ssz,
  pp_quant $ λ avs,
  pp_star (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv (heap_of_event e.2)  ∗
             [∗ list] v;av∈(vals_of_event e.2);avs, r2a_val_rel v av) $
  match e with
  | (i, ERCall f vs h) =>
      (* program chooses new physical blocks *)
      pp_prop (r2a_args_pure 0 avs rs) $
      (* program proves that this instruction is external *)
      pp_prop (rs !!! "PC" ∉ ins) $
      (* program proves that the address is correct *)
      pp_star (r2a_f2i_incl {[ f := rs !!! "PC" ]} ∅) $
      (* program proves that ret is in ins *)
      pp_prop (rs !!! "R30" ∈ ins) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(r2a_last_regs) rs) $
      (* track the registers and return address (true means ret belongs to program) *)
      pp_end ((Outgoing, EAJump rs mem), (R2A ((R2AI true (rs !!! "R30") rs)::s.(r2a_calls)) s.(r2a_last_regs)))
  | (i, ERReturn v h) =>
      (* program chooses old registers *)
      pp_quant $ λ rsold,
      (* program chooses rest of cs *)
      pp_quant $ λ cs',
      (* get registers from stack (false means pc belongs to the env) *)
      pp_prop (s.(r2a_calls) = (R2AI false (rs !!! "PC") rsold)::cs') $
      (* prog proves that rs is updated correctly *)
      pp_prop (r2a_regs_ret rs rsold (avs !!! 0%nat)) $
      (* program proves it only touched a specific set of registers *)
      pp_prop (map_scramble touched_registers s.(r2a_last_regs) rs) $
      pp_end ((Outgoing, EAJump rs mem), (R2A cs' s.(r2a_last_regs)))
  end.

Definition rec_to_asm_trans (ins : gset Z) (f2i : gmap string Z)
           (m : mod_trans rec_event) : mod_trans asm_event :=
  prepost_trans (rec_to_asm_pre ins) (rec_to_asm_post ins) m.

Definition rec_to_asm (ins : gset Z) (f2i : gmap string Z) (mo : gmap Z (option Z)) (h0 : gmap prov (gmap Z val))
           (m : module rec_event) : module asm_event :=

  Mod (rec_to_asm_trans ins f2i m.(m_trans))
      (SMFilter, m.(m_init), (PPOutside, R2A [] ∅, uPred_shrink (
      r2a_mem_map mo ∗ ([∗ map] p↦b∈ h0, p ↦∗h b) ∗
        r2a_f2i_incl f2i ins )%I)).

Lemma rec_to_asm_trefines mo m m' ins f2i h0 `{!VisNoAng m.(m_trans)}:
  trefines m m' →
  trefines (rec_to_asm ins f2i mo h0 m) (rec_to_asm ins f2i mo h0 m').
Proof. move => ?. by apply: prepost_mod_trefines. Qed.

(** * Horizontal compositionality of [rec_to_asm] *)
Inductive rec_to_asm_combine_stacks (ins1 ins2 : gset Z) :
  seq_product_case → list seq_product_case →
  list rec_to_asm_stack_item → list rec_to_asm_stack_item → list rec_to_asm_stack_item →
 Prop :=
| RAC_nil :
  rec_to_asm_combine_stacks ins1 ins2 None [] [] [] []
| RAC_cons s s' ret rs ics cs cs1 cs2 cs' cs1' cs2':
  rec_to_asm_combine_stacks ins1 ins2 s ics cs cs1 cs2 →
  s ≠ s' →
  cs' = (if s is None then (R2AI false ret rs) :: cs else if s' is None then (R2AI true ret rs) :: cs else cs) →
  cs1' = (if s is Some SPLeft then (R2AI true ret rs) :: cs1 else if s' is Some SPLeft then (R2AI false ret rs) :: cs1 else cs1) →
  cs2' = (if s is Some SPRight then (R2AI true ret rs) :: cs2 else if s' is Some SPRight then (R2AI false ret rs) :: cs2 else cs2) →
  match s with
  | None => ret ∉ ins1 ∧ ret ∉ ins2
  | Some SPLeft => ret ∈ ins1
  | Some SPRight => ret ∈ ins2
  end →
  rec_to_asm_combine_stacks ins1 ins2 s' (s :: ics) cs' cs1' cs2'.

Local Ltac go := repeat match goal with | x : asm_ev |- _ => destruct x end;
                 destruct!/=; destruct!/=.
Local Ltac go_i := tstep_i; intros; go.
Local Ltac go_s := tstep_s; go.

Local Ltac r2a_split_go :=
  idtac; (* this idtac is important as otherwise the match is evaluated eagerly *)
  match goal with
  | |- r2a_regs_ret _ _ _ => eassumption
  | |- r2a_args_pure _ _ _ => eassumption
  | |- map_scramble ?r ?a ?b =>
      assert_fails (has_evar r); assert_fails (has_evar a); assert_fails (has_evar b); by etrans
  end.
Local Tactic Notation "r2a_split!" := split_tac ltac:(r2a_split_go).

Lemma rec_to_asm_combine ins1 ins2 fns1 fns2 f2i1 f2i2 mo1 mo2 h01 h02 m1 m2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  ins1 ## ins2 →
  fns1 ## fns2 →
  mo1 ##ₘ mo2 →
  h01 ##ₘ h02 →
  f2i_fns_ins_wf f2i1 fns1 ins1 →
  f2i_fns_ins_wf f2i2 fns2 ins2 →
  map_agree f2i1 f2i2 →
  map_Forall (λ f i, i ∉ ins2 ∨ f2i2 !! f = Some i) f2i1 →
  map_Forall (λ f i, i ∉ ins1 ∨ f2i1 !! f = Some i) f2i2 →
  trefines (asm_link ins1 ins2 (rec_to_asm ins1 f2i1 mo1 h01 m1) (rec_to_asm ins2 f2i2 mo2 h02 m2))
           (rec_to_asm (ins1 ∪ ins2) (f2i1 ∪ f2i2) (mo1 ∪ mo2) (h01 ∪ h02) (rec_link fns1 fns2 m1 m2)).
Proof.
  move => Hdisji Hdisjf Hdisjm Hdisjh Hwf1 Hwf2 /map_agree_spec Hagree Hincl1 Hincl2.
  unshelve apply: prepost_link. { exact (λ ips '(R2A cs1 lr1) '(R2A cs2 lr2) '(R2A cs lr) x1 x2 x s ics,
  rec_to_asm_combine_stacks ins1 ins2 ips ics cs cs1 cs2 ∧ s = None ∧
  ((ips = None ∧ (x ⊣⊢ x1 ∗ x2 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)) ∨
  ((ips = Some SPLeft ∧ x1 = (x ∗ x2 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)%I
      ∧ map_scramble touched_registers lr lr1) ∨
  (ips = Some SPRight ∧ x2 = (x ∗ x1 ∗ r2a_f2i_incl f2i1 ins1 ∗ r2a_f2i_incl f2i2 ins2)%I
      ∧ map_scramble touched_registers lr lr2)))). }
  { move => ?? [] /=*; naive_solver. }
  { split!. econs. rewrite !big_sepM_union //.
    rewrite r2a_f2i_incl_union. 2: by apply map_agree_spec.
    2: { move => *. unfold map_Forall in *. naive_solver. }
    2: { move => *. unfold map_Forall in *. naive_solver. }
    iSplit; iIntros!.
    all: iDestruct select (r2a_f2i_incl f2i1 ins1) as "#?".
    all: iDestruct select (r2a_f2i_incl f2i2 ins2) as "#?".
    all: iFrame "#∗". }
  all: move => [cs1 lr1] [cs2 lr2] [cs lr] x1 x2 x ? ics.
  - move => e ? e' /= ? ??.
    destruct!.
    destruct e as [rs mem| |]; destruct!/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. split; [done|]. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => f Hargs Hin /not_elem_of_union[??] ? ?.
      repeat case_bool_decide => //.
      have ? : (f ∈ fns1). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        by iSatStop.
      }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *. destruct!.
      repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; simplify_eq/= => //. 2: { exfalso. set_solver. }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => e ? e' /= ? ??.
    destruct!.
    destruct e as [rs mem| |]; destruct!/=.
    move => b *. apply pp_to_all_forall => ra ya Hra xa Hxa. split; [done|]. eexists b.
    move: ra ya Hra xa Hxa. apply: pp_to_all_forall_2. destruct b => /=.
    + move => f Hargs Hin /not_elem_of_union[??] ??.
      repeat case_bool_decide => //.
      have ? : (f ∈ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + move => *. destruct!. repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; simplify_eq/= => //.
      r2a_split!.
      1: { setoid_subst. iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct!/=; split; [done|].
    + do 2 case_bool_decide => //. eexists true => /=.
      have ? : (f ∈ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: naive_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + repeat case_bool_decide => //. eexists false => /=.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". simplify_eq/=. iFrame. }
  - move => [? [f vs h|v h]] ? ? ? /= *.
    all: destruct!/=.
    + do 2 case_bool_decide => //.
      have ? : (f ∉ fns1 ∪ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        iSatStop. set_solver. }
      r2a_split!.
      1: repeat case_bool_decide => //; set_solver.
      1: set_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iFrame. }
  - move => [? [f vs h|v h]] ? /= *.
    all: destruct!/=; split; [done|].
    + case_bool_decide; [|by case_bool_decide]. eexists true.
      have ? : (f ∈ fns1). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        by iSatStop. }
      r2a_split!.
      1: naive_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by simpl_map_decide.
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //. eexists false.
      r2a_split!.
      1: { iSatMono. iIntros!. iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". simplify_eq/=. iFrame. }
  - move => [? [f vs h|v h]] ? /= ? *.
    all: destruct!/=.
    + do 2 case_bool_decide => //.
      have ? : (f ∉ fns1 ∪ fns2). {
        setoid_subst. iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i1 with "[$] [$]") as %?; [done..|].
        iDestruct (f2i_fns_ins_wf_not_in_ins f2i2 with "[$] [$]") as %?; [done..|].
        iSatStop. set_solver. }
      r2a_split!.
      1: repeat case_bool_decide => //; set_solver.
      1: set_solver.
      1: set_solver.
      1: { iSatMono. iIntros!. iFrame. }
      1: by econs.
    + repeat case_bool_decide => //.
      revert select (rec_to_asm_combine_stacks _ _ _ _ _ _ _) => Hstack.
      inversion Hstack; repeat case_match; destruct!/= => //.
      r2a_split!.
      1: { iSatMono. iIntros!. iFrame. }
Qed.

(** * Proof technique for [rec_to_asm] *)

Lemma rec_to_asm_proof INV ins fns ins_dom f2i mo h0 :
  ins_dom = dom ins →
  f2i_fns_ins_wf f2i (dom fns) ins_dom →
  (∀ mem sp ssz h,
   r2a_mem_inv sp ssz mem -∗
   r2a_heap_inv h -∗
   r2a_mem_map mo -∗
   r2a_f2i_incl f2i ins_dom -∗
   ([∗ map] p↦b ∈ h0, p ↦∗h b) ==∗
   INV ∗ r2a_mem_inv sp ssz mem ∗ r2a_heap_inv h) →
  (∀ n i rs mem K f fn vs h cs pc ssz rf rc lr,
      rs !!! "PC" = pc →
      ins !! pc = Some i →
      fns !! f = Some fn →
      f2i !! f = Some pc →
      satisfiable (r2a_mem_inv (rs !!! "SP") ssz mem ∗ r2a_heap_inv h ∗ r2a_f2i_incl f2i ins_dom ∗ r2a_args 0 vs rs ∗ INV ∗ rf ∗ rc) →
      length vs = length (fd_args fn) →
      map_scramble touched_registers lr rs →
      (* Call *)
      (∀ K' rs' mem' f' es vs pc' ssz' h' lr' rf' r',
          Forall2 (λ e v, e = Val v) es vs →
          rs' !!! "PC" = pc' →
          (* We sadly don't have a good way to frame the r2a_f2i_incl
          f2i ins_dom. (We could put it in rc, but this would require
          the client to thread around rc). *)
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                      r2a_args 0 vs rs' ∗ r2a_f2i_incl {[f' := pc']} ∅ ∗
                      r2a_f2i_incl f2i ins_dom ∗ INV ∗ rf' ∗ r') →
          is_Some (ins !! (rs' !!! "R30")) →
          map_scramble touched_registers lr' rs' →
          (∀ rs'' ssz'' mem'' av v h'' rf'' lr'',
              rs'' !!! "PC" = rs' !!! "R30" →
              satisfiable (r2a_mem_inv (rs'' !!! "SP") ssz'' mem'' ∗ r2a_heap_inv h'' ∗
                           r2a_val_rel v av ∗ INV ∗ rf'' ∗ r') →
              r2a_regs_ret rs'' rs' av →
              map_scramble touched_registers lr'' rs'' →
              AsmState (ARunning []) rs'' mem'' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (expr_fill K' (Val v))) h'' fns, (PPInside, R2A cs lr'', uPred_shrink rf''))) →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (expr_fill K' (rec.Call (Val (ValFn f')) es))) h' fns, (PPInside, R2A cs lr', uPred_shrink rf'))) →
      (* Return *)
      (∀ rs' mem' ssz' av v h' lr' rf',
          rs' !!! "PC" = rs !!! "R30" →
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                      r2a_val_rel v av ∗ INV ∗ rf' ∗ rc) →
          r2a_regs_ret rs' rs av →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K (Val v)) h' fns, (PPInside, R2A cs lr', uPred_shrink rf'))) →
      AsmState (ARunning []) rs mem ins ⪯{asm_trans, rec_to_asm_trans ins_dom f2i rec_trans, n, false}
               (SMProg, Rec (expr_fill K (AllocA fn.(fd_vars) $ subst_static f fn.(fd_static_vars) $ subst_l fn.(fd_args) vs fn.(fd_body))) h fns, (PPInside, R2A cs lr, uPred_shrink rf))
) →
  trefines (asm_mod ins) (rec_to_asm ins_dom f2i mo h0 (rec_mod fns)).
Proof.
  move => ? Hwf HINV Hf. subst.
  etrans. 2: {
    apply (mod_prepost_impl_prop _ _ _ _ (INV ∗ r2a_f2i_incl f2i (dom ins))); [apply _|] => -[? []] //= ? ? [] //=.
    move => *. iIntros!.
    iDestruct select (r2a_f2i_incl f2i _) as "#?".
    iMod (HINV with "[$] [$] [$] [$] [$]") as "[$ [$ $]]". by iFrame. }
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((AsmState i1 rs1 mem1 ins'1), (σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1)))
                        '((AsmState i2 rs2 mem2 ins'2), (σfs2, Rec e2 h2 fns'2, (t2, R2A cs2 lr2, r2))),
      ∃ K rr1 rr2,
        i2 = AWaiting ∧ ins'2 = ins ∧ e2 = expr_fill K (Waiting (bool_decide (d ≠ 0%nat))) ∧ fns'2 = fns ∧
        t2 = PPOutside ∧ σfs2 = SMFilter ∧ (d = 0%nat ↔ cs2 = []) ∧
        r1 = uPred_shrink rr1 ∧ r2 = uPred_shrink rr2 ∧
        (∃ rr2', rr2 ⊣⊢ INV ∗ r2a_f2i_incl f2i (dom ins) ∗ rr2') ∧
      if b then
        e2 = e1 ∧
        cs2 = cs1 ∧
        rr1 = rr2
      else
        True
  ). }
  { simpl. exact (λ  '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1))
                     '(AsmState i2 rs2 mem2 ins'2) '(σfs2, Rec e2 h2 fns'2, (t2, R2A cs2 lr2, r2)),
    ∃ i K av v pc lr' ssz rr1 rr2,
      r1 = uPred_shrink rr1 ∧ r2 = uPred_shrink rr2 ∧
      rs2 !!! "PC" = pc ∧
      ins !! pc = Some i ∧
      satisfiable (r2a_mem_inv (rs2 !!! "SP") ssz mem2 ∗ r2a_heap_inv h2 ∗ r2a_val_rel v av ∗ rr1 ∗ rr2) ∧
      r2a_regs_ret rs2 lr' av ∧
      i2 = ARunning [] ∧
      ins'1 = ins'2 ∧
      σfs2 = SMProg ∧
      e1 = expr_fill K (Waiting true) ∧
      e2 = expr_fill K (Val v) ∧
      fns'1 = fns'2 ∧
      t2 = PPInside ∧
      cs1 = R2AI true pc lr' :: cs2 ∧
      lr2 = rs2
). }
  { move => ??? *. destruct!. repeat case_match; naive_solver. }
  { move => /= *. destruct!. repeat case_match. naive_solver. }
  { move => /=. eexists []. split!. iSplit; iIntros!; iFrame. iAccu. }
  move => /= n [i rs mem ins'] [[?[???]][[?[cs ?]]r]] d ? ? Hstay Hcall Hret. destruct!/=.
  tstep_i => ??????.
  go_s. split!.
  go_s => -[] ? /=.
  - move => ?????? /elem_of_dom[??] /not_elem_of_dom ? ??.
    go_s.
    iSatStart. iIntros!. setoid_subst.
    rename select (_ ⊣⊢ _) into Hrr2.
    rewrite Hrr2. iDestruct!. iDestruct select (r2a_f2i_incl f2i _ ) as "#Hincl".
    iDestruct (f2i_fns_ins_wf_in_ins f2i with "[$] [$]") as %Hfi; [done|by apply elem_of_dom|].
    move: Hfi => /elem_of_dom[??]. iSatStop.
    split!. tstep_s. left. split! => ?.
    (* This inner loop deals with calls inside of the module. We use
    Hf both for calls triggered from inside and outside the module. *)
    unshelve eapply tsim_remember. { exact (λ n '(AsmState i1 rs1 mem1 ins'1) '(σfs1, Rec e1 h1 fns'1, (t1, R2A cs1 lr1, r1)),
       ∃ K' pc i f fn vs r' ssz rr1,
         r1 = uPred_shrink rr1 ∧
         rs1 !!! "PC" = pc ∧
         ins !! pc = Some i ∧
         fns !! f = Some fn ∧
         ins'1 = ins ∧
         fns'1 = fns ∧
         satisfiable (r2a_mem_inv (rs1 !!! "SP") ssz mem1 ∗ r2a_heap_inv h1 ∗
                      r2a_f2i_incl f2i (dom ins) ∗ r2a_f2i_incl {[f := pc]} ∅ ∗
                      r2a_args 0 vs rs1 ∗ INV ∗ r' ∗ rr1) ∧
         i1 = ARunning [] ∧
         e1 = expr_fill K' (AllocA fn.(fd_vars) $ subst_static f fn.(fd_static_vars) $ subst_l fn.(fd_args) vs fn.(fd_body)) ∧
         map_scramble touched_registers lr1 rs1 ∧
         length vs = length (fd_args fn) ∧
         t1 = PPInside ∧
         σfs1 = SMProg ∧
         (∀ rs' mem' ssz' av v h' lr' rf',
          rs' !!! "PC" = rs1 !!! "R30" →
          satisfiable (r2a_mem_inv (rs' !!! "SP") ssz' mem' ∗ r2a_heap_inv h' ∗
                      r2a_f2i_incl f2i (dom ins) ∗
                      r2a_val_rel v av ∗ INV ∗ r' ∗ rf') →
          r2a_regs_ret rs' rs1 av  →
          map_scramble touched_registers lr' rs' →
          AsmState (ARunning []) rs' mem' ins ⪯{asm_trans, rec_to_asm_trans (dom ins) f2i rec_trans, n, true}
               (SMProg, Rec (expr_fill K' (Val v)) h' fns, (PPInside, R2A cs1 lr', uPred_shrink rf'))) ). }
    { eexists (ReturnExtCtx _:: _). split! => //. {
        iSatMono. iIntros!. iFrame "∗#".
        iDestruct (r2a_args_intro with "[$]") as "$"; [done|].
        iAccu. }
      iSatClear. move => *.
      tstep_s.
      tstep_i => ??. simplify_map_eq'.
      tstep_s. split!. { instantiate (1:=[_]). done. } {
        iSatMono. iIntros!. iFrame. iAssert rr2 with "[-]" as "?"; [|iAccu].
        rewrite Hrr2. iFrame. }
      apply Hstay; [done|]. by split!.
    }
    { move => ?? [????] [[?[???]][[?[??]]?]] ??. destruct!. split!; [done..|].
      move => *. apply: tsim_mono; [naive_solver|]. etrans; [|done]. apply o_le_S. }
    iSatClear.
    move => n' /= Hn' IH [i' rs' mem' ins'] [[?[???]][[?[??]]?]] ?. destruct!.
    apply: Hf; [try done..| |]. {
      iSatStart. iIntros!.
      iDestruct (r2a_f2i_incl_in_ins _ _ f2i with "[$] [$]") as %?. { by apply elem_of_dom. }
      by iSatStop.
    }
    { iSatMono. iIntros!.
      iDestruct select (r2a_f2i_incl f2i _) as "#Hf2i".
      iFrame "∗#". iDestruct "Hf2i" as "-#Hf2i". iAccu. }
    + iSatClear.
      move => K'' rs'' mem'' f'' es vs'' pc'' ssz'' h'' lr rf'' r'' Hall ???? Hret'.
      have ?: es = Val <$> vs''. { clear -Hall. elim: Hall; naive_solver. } subst.
      destruct (ins !! (rs'' !!! "PC")) eqn:Hi.
      * iSatStart. iIntros!.
        iDestruct (f2i_fns_ins_wf_in_ins with "[$] [$]") as %Hf''; [done|by apply elem_of_dom|].
        move: Hf'' => /elem_of_dom[??]. iSatStop.
        tstep_s. left. split! => ?/=.
        apply IH; [done|]. split! => //.
        { iSatMono. iIntros!. iFrame. iAccu. }
        iSatClear. move => *.
        rewrite expr_fill_app.
        apply: Hret' => //.
        iSatMono. iIntros!. iFrame.
      * have ?: fns !! f'' = None. {
          iSatStart. iIntros!.
          iDestruct (f2i_fns_ins_wf_not_in_ins with "[$] [$]") as %?; [done|by apply not_elem_of_dom|].
          iSatStop. by apply not_elem_of_dom.
        }
        tstep_i => ??. simplify_map_eq.
        tstep_s. right. split!.
        tstep_s.
        iSatStart. iIntros!.
        iDestruct (r2a_args_elim with "[$]") as (??) "?". iSatStop.
        r2a_split!. { by apply not_elem_of_dom. } { by apply elem_of_dom. }
        { iSatMono. iFrame. iAccu. }
        apply Hcall. { etrans; [|done]. apply o_le_S. } {
          split!; [done|]. iSplit; iIntros!; iFrame; iAccu. }
        iSatClear.
        move => [i2 rs2 mem2 ins'2] [[?[???]][[?[??]]?]].
        move => [i3 rs3 mem3 ins'3] [[?[???]][[?[??]]?]].
        move => ??. destruct!.
        simplify_eq.
        repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
        destruct!.
        rewrite !expr_fill_app /=.
        eapply Hret' => //.
        iSatMono. iIntros!. iFrame.
    + iSatClear. move => *.
      apply: H15 => //.
      iSatMono. iIntros!. iFrame.
  - move => *.
    tstep_s. simplify_eq. destruct d; [exfalso; naive_solver|]. split!.
    apply Hret; [done..| |].
    + by split!.
    + split!; [|done..]. destruct!/=.
      iSatMono. iIntros!. iFrame.
Qed.
