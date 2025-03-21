From iris.algebra.lib Require Import gmap_view.
From iris.algebra Require Import agree gset.
From dimsum.core Require Export proof_techniques prepost.
From dimsum.core Require Import link.
From dimsum.core Require Import axioms.
From dimsum.examples Require Export rec.
From dimsum.examples Require Export heapUR.

Set Default Proof Using "Type".

(** * rec_heap_inj *)
(** [rec_heap_inj] allows injections of memory when proving a
refinement between two Rec modules. *)

(** * Camera definition *)
Definition heap_injUR : ucmra :=
  prodUR (optionO (agree (gset prov)))
 (prodUR (gmap_viewUR prov (agreeR locO))
 (prodUR heapUR
 (heapUR))).

Global Instance heap_injUR_shrink : Shrink heap_injUR.
Proof. solve_shrink. Qed.

Global Instance heap_injUR_discrete : CmraDiscrete heap_injUR.
Proof. apply _. Qed.

Program Definition own_heap_s : BiOwn (uPredI heap_injUR) heapUR := {|
  bi_own r := uPred_ownM (None, (ε, (r, ε)))
|}.
Next Obligation.
  move => /= ?. etrans; [apply uPred.ownM_valid|]. iPureIntro.
  by move => [_ [_ []]].
Qed.
Next Obligation. move => ??/=. by rewrite -!uPred.ownM_op -!pair_op_2 -pair_op_1. Qed.
Next Obligation.
  move => ???/=. apply uPred.bupd_ownM_update.
  by repeat (apply prod_update; [done|] => /=).
Qed.
Next Obligation. solve_proper. Qed.

Program Definition own_heap_i : BiOwn (uPredI heap_injUR) heapUR := {|
  bi_own r := uPred_ownM (None, (ε, (ε, r)))
|}.
Next Obligation.
  move => /= ?. etrans; [apply uPred.ownM_valid|]. iPureIntro.
  by move => [_ [_ []]].
Qed.
Next Obligation. move => ??/=. by rewrite -!uPred.ownM_op -!pair_op_2 -?pair_op_1. Qed.
Next Obligation.
  move => ???/=. apply uPred.bupd_ownM_update.
  by repeat (apply prod_update; [done|] => /=).
Qed.
Next Obligation. solve_proper. Qed.

Definition heap_injUR_statics_inj (r : agree (gset prov)) : heap_injUR := ((Some r), (ε, ε)).
Definition heap_injUR_shared_inj (r : (gmap_viewUR prov (agreeR locO))) : heap_injUR
  := (None, (r, ε)).


(** * ghost theory *)
(** ** Ghost state definitions *)
Definition heap_inj_shared_auth_raw (ps : gmap prov loc) : uPred (heap_injUR) :=
  uPred_ownM (heap_injUR_shared_inj $ gmap_view_auth (DfracOwn 1) (to_agree <$> ps)).
Definition heap_inj_shared (ps : prov) (li : loc) : uPred (heap_injUR) :=
  uPred_ownM (heap_injUR_shared_inj $ gmap_view_frag ps DfracDiscarded (to_agree li)).
Definition heap_inj_statics (provs : gset prov) :=
  uPred_ownM (heap_injUR_statics_inj (to_agree provs)).

Definition heap_inj_shared_auth (ps : gmap prov loc) : uPred (heap_injUR) :=
  heap_inj_shared_auth_raw ps ∗ [∗ map] ps↦li0∈ps, heap_inj_shared ps li0.

Notation heap_inj_inv_s := (heapUR_inv own_heap_s).
Notation heap_inj_inv_i := (heapUR_inv own_heap_i).

Notation "l '↦hs' dq v" := (heapUR_ptsto own_heap_s l dq v)
  (at level 20, dq custom dfrac, format "l  ↦hs dq  v") : bi_scope.
Notation "l '↦hi' dq v" := (heapUR_ptsto own_heap_i l dq v)
  (at level 20, dq custom dfrac,format "l  ↦hi dq  v") : bi_scope.

Notation "p '⤚hs' dq d" := (heapUR_dom own_heap_s p dq d)
  (at level 20, dq custom dfrac at level 1, format "p  '⤚hs' dq  d") : bi_scope.
Notation "p '⤚hi' dq d" := (heapUR_dom own_heap_i p dq d)
  (at level 20, dq custom dfrac at level 1, format "p  '⤚hi' dq  d") : bi_scope.

Notation "p '↦∗hs' dq b" := (heapUR_block own_heap_s p dq b)
  (at level 20, dq custom dfrac at level 1, format "p  '↦∗hs' dq  b") : bi_scope.
Notation "p '↦∗hi' dq b" := (heapUR_block own_heap_i p dq b)
  (at level 20, dq custom dfrac at level 1, format "p  '↦∗hi' dq  b") : bi_scope.

(** ** Ghost state lemmas *)
Lemma heap_inj_statics_eq h1 h2 :
  heap_inj_statics h1 -∗
  heap_inj_statics h2 -∗
  ⌜h1 = h2⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id. rewrite -uPred.ownM_op.
  etrans; [apply uPred.ownM_valid|]. iPureIntro.
  move => [/=]. rewrite -Some_op Some_valid to_agree_op_valid => ??.
  by fold_leibniz.
Qed.

Lemma heap_inj_shared_alloc_raw ps li0 inj :
  inj !! ps = None →
  heap_inj_shared_auth_raw inj ⊢ |==>
  heap_inj_shared_auth_raw (<[ps := li0]>inj) ∗ heap_inj_shared ps li0.
Proof.
  move => ?. rewrite -uPred.ownM_op. apply uPred.bupd_ownM_update.
  apply prod_update; [done|] => /=. apply prod_update; [|done] => /=.
  rewrite fmap_insert. apply gmap_view_alloc => //.
  by rewrite lookup_fmap fmap_None.
Qed.

Lemma heap_inj_shared_alloc ps li0 inj :
  inj !! ps = None →
  heap_inj_shared_auth inj ⊢ |==>
  heap_inj_shared_auth (<[ps := li0]>inj) ∗ heap_inj_shared ps li0.
Proof.
  iIntros (?) "[??]". iMod (heap_inj_shared_alloc_raw with "[$]") as "[$ #$]"; [done|].
  iModIntro. by iApply big_sepM_insert_2.
Qed.

Lemma heap_inj_shared_lookup_raw ps li0 inj  :
  heap_inj_shared_auth_raw inj -∗
  heap_inj_shared ps li0 -∗
  ⌜inj !! ps = Some li0⌝.
Proof.
  apply bi.wand_intro_r. apply bi.wand_intro_r. rewrite left_id.
  rewrite -uPred.ownM_op. etrans; [apply uPred.ownM_valid|].
  iPureIntro. rewrite -pair_op => -[_ ]/=. setoid_rewrite <-pair_op.
  move => [/(gmap_view_both_dfrac_valid_discrete_total _ _ _)+ _].
  move => [? [_ [_ [/lookup_fmap_Some[?[??]] [? +]]]]]. subst.
  move => /to_agree_included_L. naive_solver.
Qed.

Lemma heap_inj_shared_lookup ps li0 inj  :
  heap_inj_shared_auth inj -∗
  heap_inj_shared ps li0 -∗
  ⌜inj !! ps = Some li0⌝.
Proof. iIntros "[? _]". by iApply heap_inj_shared_lookup_raw. Qed.

Lemma heap_inj_shared_lookup_big inj' inj  :
  heap_inj_shared_auth inj -∗
  ([∗map] ps↦li0∈inj', heap_inj_shared ps li0) -∗
  ⌜inj' ⊆ inj⌝.
Proof.
  iIntros "Ha Hl". iInduction inj' as [|] "IH" using map_ind.
  { iPureIntro. apply map_empty_subseteq. }
  iDestruct (big_sepM_insert with "Hl") as "[??]"; [done|].
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (heap_inj_shared_lookup with "Ha [$]") as %?.
  iPureIntro. by apply insert_subseteq_l.
Qed.

Lemma heap_inj_shared_alloc_big_raw inj inj' :
  inj ⊆ inj' →
  heap_inj_shared_auth inj ⊢ |==>
  heap_inj_shared_auth inj'.
Proof.
  iIntros (Hsub) "?". rewrite -(map_difference_union inj inj') //.
  have Hdisj : (inj ##ₘ inj' ∖ inj) by apply map_disjoint_difference_r'.
  rewrite map_union_comm //.
  iInduction (inj' ∖ inj) as [|] "IH" using map_ind forall (Hdisj).
  { by rewrite left_id_L. }
  move: Hdisj => /map_disjoint_insert_r[??].
  iMod ("IH" with "[%] [$]") as "?"; [done|].
  rewrite -insert_union_l.
  iMod (heap_inj_shared_alloc with "[$]") as "[$ _]". 2: done.
  by apply lookup_union_None.
Qed.

Lemma heap_inj_shared_alloc_big inj inj' :
  inj ⊆ inj' →
  heap_inj_shared_auth inj ⊢ |==>
  heap_inj_shared_auth inj' ∗ [∗ map] ps↦li0∈inj', heap_inj_shared ps li0.
Proof.
  iIntros (Hsub) "?".
  iMod (heap_inj_shared_alloc_big_raw with "[$]") as "[? ?]"; [done|].
  iModIntro. iSplit!. iFrame.
Qed.

Lemma heap_inj_shared_auth_shared inj :
  heap_inj_shared_auth inj ⊢ [∗ map] ps↦li0∈inj, heap_inj_shared ps li0.
Proof. iIntros "[? $]". Qed.

Global Typeclasses Opaque heap_inj_shared_auth.

(** * val_in_inj *)
Definition loc_in_inj (li ls : loc) : uPred heap_injUR :=
  ∃ li0, ⌜li = li0 +ₗ ls.2⌝ ∗ heap_inj_shared ls.1 li0.

Global Instance loc_in_inj_Persistent li ls : Persistent (loc_in_inj li ls).
Proof. apply _. Qed.

Definition val_in_inj (vi vs : val) : uPred heap_injUR :=
  match vi, vs with
  | ValNum n1, ValNum n2 => ⌜n1 = n2⌝
  | ValBool b1, ValBool b2 => ⌜b1 = b2⌝
  | ValFn f1, ValFn f2 => ⌜f1 = f2⌝
  | ValLoc l1, ValLoc l2 => loc_in_inj l1 l2
  | _, _ => False
  end.

Global Instance val_in_inj_Persistent vi vs : Persistent (val_in_inj vi vs).
Proof. destruct vi, vs => /=; apply _. Qed.

Lemma big_sepL2_ValNum_inv_r vl zl :
  ([∗ list] y1;y2 ∈ vl;(ValNum <$> zl), val_in_inj y1 y2) -∗
  ⌜vl = (ValNum <$> zl)⌝.
Proof.
  iIntros "Hvl".
  iInduction vl as [|v] "IH" forall (zl); csimpl.
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. done. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[Hv ?]"; subst.
  destruct zl; simplify_eq/=. destruct v => //=. iDestruct "Hv" as %?.
  iDestruct ("IH" with "[$]") as %?.
  naive_solver.
Qed.

Lemma eval_binop_inj o v1 v2 v1' v2' v:
  eval_binop o v1 v2 = Some v →
  val_in_inj v1' v1 -∗
  val_in_inj v2' v2 -∗
  ∃ v', ⌜eval_binop o v1' v2' = Some v'⌝ ∗ val_in_inj v' v.
Proof.
  iIntros (?) "??".
  destruct o, v1, v2, v1', v2' => //= *; unfold loc_in_inj; iDestruct!; iSplit!; unfold loc_in_inj; iSplit!.
  2: done. apply offset_loc_assoc.
Qed.

(** * heap_in_inj *)
(* TODO: make this actually an injection. See
b611b0e2cb0e6c903638048347ff51d618f995f6 for a version that is not
vertically compositional. Try the following version that should be vertically
compositional (note the 1/2 fraction for the dom):

Definition heap_in_inj_inv (inj : gmap prov loc) (rem : list prov) :
  uPred heap_injUR :=
    [∗ map] ps↦li0∈inj, ⌜ps ∈ rem⌝ ∨
      ∃ d, heap_inj_dom_s ps (1/2) d ∗
      [∗ map] o∈d, ∃ vi vs, (li0 +ₗ o) ↦hi vi ∗ (p, o) ↦hs vs ∗ val_in_inj vi vs.

 *)
Definition heap_in_inj_inv (inj : gmap prov loc) (rem : list prov) :
  uPred heap_injUR :=
    [∗ map] ps↦li0∈inj, ⌜ps ∈ rem⌝ ∨
      ∃ bi bs, ⌜li0.2 = 0%Z⌝ ∗ li0.1 ↦∗hi bi ∗ ps ↦∗hs bs ∗
      [∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs.

Definition heap_in_inj (rem : list prov) : uPred heap_injUR :=
  ∃ inj, heap_inj_shared_auth inj ∗ heap_in_inj_inv inj rem.

Lemma heap_in_inj_inv_borrow ps li0 rem inj :
  ps ∉ rem →
  inj !! ps = Some li0 →
  heap_in_inj_inv inj rem -∗
  ∃ bi bs, ⌜li0.2 = 0%Z⌝ ∗ heap_in_inj_inv inj (ps::rem) ∗
  li0.1 ↦∗hi bi ∗ ps ↦∗hs bs ∗ [∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs.
Proof.
  iIntros (??) "Hinj".
  iDestruct (big_sepM_lookup_acc_impl with "Hinj") as "[[%|[% [% [% $]]]] Hinj]";[done..|].
  iSplit!. iApply "Hinj". 2: by iLeft; iPureIntro; set_solver.
  iIntros "!>" (????) "[%|$]". by iLeft; iPureIntro; set_solver.
Qed.

Lemma heap_in_inj_inv_split inj' inj :
  inj' ⊆ inj →
  heap_in_inj_inv inj [] ⊣⊢
  heap_in_inj_inv inj' [] ∗ heap_in_inj_inv (inj ∖ inj') [].
Proof.
  move => ?. rewrite /heap_in_inj_inv -big_sepM_union ?map_difference_union//.
  apply map_disjoint_difference_r'.
Qed.

Lemma heap_in_inj_inv_combine inj' inj :
  heap_in_inj_inv inj [] -∗
  heap_in_inj_inv inj' [] -∗
  heap_in_inj_inv (inj ∪ inj') [].
Proof. apply: big_sepM_union_2. Qed.

Lemma heap_in_inj_inv_return i ps bi bs li0 rem inj :
  rem !! i = Some ps →
  inj !! ps = Some li0 →
  li0.2 = 0%Z →
  heap_in_inj_inv inj rem -∗
  li0.1 ↦∗hi bi -∗
  ps ↦∗hs bs -∗
  ([∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs) -∗
  heap_in_inj_inv inj (delete i rem).
Proof.
  iIntros (???) "Hinj Hi Hs Hvs".
  iDestruct (big_sepM_lookup_acc_impl with "Hinj") as "[Hprev Hinj]";
    [done|].
  iApply "Hinj".
  - iIntros "!>" (????) "[%Hin|$]". iLeft. iPureIntro.
    rewrite delete_take_drop. erewrite <-take_drop_middle in Hin; [|done].
    set_solver.
  - iRight. by iFrame.
Qed.

Lemma heap_in_inj_inv_return0 ps bi bs li0 rem inj :
  inj !! ps = Some li0 →
  li0.2 = 0%Z →
  heap_in_inj_inv inj (ps :: rem) -∗
  li0.1 ↦∗hi bi -∗
  ps ↦∗hs bs -∗
  ([∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs) -∗
  heap_in_inj_inv inj rem.
Proof. iIntros (??) "????". by iApply (heap_in_inj_inv_return 0 with "[$] [$] [$]"). Qed.


Lemma heap_in_inj_init :
  heap_inj_shared_auth ∅ -∗ heap_in_inj [].
Proof. iIntros "$". by iApply big_sepM_empty. Qed.

Lemma heap_in_inj_borrow ps li0 rem :
  ps ∉ rem →
  heap_in_inj rem -∗
  heap_inj_shared ps li0 -∗
  ∃ bi bs, ⌜li0.2 = 0%Z⌝ ∗ heap_in_inj (ps :: rem) ∗
  li0.1 ↦∗hi bi ∗ ps ↦∗hs bs ∗ [∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs.
Proof.
  iIntros (?) "[%inj [? Hinj]] Hsh".
  iDestruct (heap_inj_shared_lookup with "[$] [$]") as %?.
  iDestruct (heap_in_inj_inv_borrow with "[$]") as (???) "[$ [$ $]]" => //.
  by iFrame.
Qed.

Lemma heap_in_inj_return i ps bi bs li0 rem :
  rem !! i = Some ps →
  li0.2 = 0%Z →
  heap_in_inj rem -∗
  heap_inj_shared ps li0 -∗
  li0.1 ↦∗hi bi -∗
  ps ↦∗hs bs -∗
  ([∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs) -∗
  heap_in_inj (delete i rem).
Proof.
  iIntros (??) "[%inj [? Hinj]] Hsh Hi Hs Hvs".
  iDestruct (heap_inj_shared_lookup with "[$] [$]") as %?.
  iExists _. iFrame. by iApply (heap_in_inj_inv_return with "[$] [$] [$]").
Qed.

Lemma heap_in_inj_return0 ps bi bs li0 rem :
  li0.2 = 0%Z →
  heap_in_inj (ps :: rem) -∗
  heap_inj_shared ps li0 -∗
  li0.1 ↦∗hi bi -∗
  ps ↦∗hs bs -∗
  ([∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs) -∗
  heap_in_inj rem.
Proof. iIntros (?) "????". by iApply (heap_in_inj_return 0 with "[$] [$] [$] [$]"). Qed.


Lemma heap_in_inj_range hi hs l1 l2 z rem:
  l2.2 = 0%Z →
  heap_range hs l2 z →
  l2.1 ∉ rem →
  heap_inj_inv_i hi -∗
  heap_inj_inv_s hs -∗
  heap_in_inj rem -∗
  loc_in_inj l1 l2 -∗
  ⌜heap_range hi l1 z⌝.
Proof.
  iIntros (? Hr ?) "Hinv1 Hinv2 ? [% [% ?]]". subst.
  iDestruct (heap_in_inj_borrow with "[$] [$]") as (bi bs ?) "[?[?[??]]]"; [done|].
  iDestruct (heapUR_lookup_block with "Hinv1 [$]") as %<-.
  iDestruct (heapUR_lookup_block with "Hinv2 [$]") as %<-.
  iDestruct (big_sepM2_dom with "[$]") as %Heq.
  iPureIntro.
  move: Hr => /heap_range_dom_h_block1 Hr.
  apply heap_range_dom_h_block => /=; [lia|].
  by rewrite Heq Hr.
Qed.

Lemma heap_in_inj_lookup hi hs l1 l2 v rem:
  h_heap hs !! l2 = Some v →
  l2.1 ∉ rem →
  heap_inj_inv_i hi -∗
  heap_inj_inv_s hs -∗
  heap_in_inj rem -∗
  loc_in_inj l1 l2 -∗
  ∃ v', ⌜h_heap hi !! l1 = Some v'⌝ ∗ val_in_inj v' v.
Proof.
  iIntros (??) "Hinvi ? Hh [% [-> ?]]".
  iDestruct (heap_in_inj_borrow with "[$] [$]") as (bi bs Hl0) "[?[?[??]]]"; [done|].
  iDestruct (heapUR_lookup_block1 with "[$] [$]") as %?; [done|].
  iDestruct (big_sepM2_lookup_r with "[$]") as (??) "$"; [done|].
  iDestruct (heapUR_lookup_block with "Hinvi [$]") as %<-.
  iPureIntro. by rewrite /offset_loc Hl0 Z.add_0_l -h_block_lookup.
Qed.

Lemma heap_in_inj_update h1 h2 l1 l2 v1 v2 rem:
  l2.1 ∉ rem →
  heap_alive h2 l2 →
  heap_inj_inv_i h1 -∗
  heap_inj_inv_s h2 -∗
  heap_in_inj rem -∗
  loc_in_inj l1 l2 -∗
  val_in_inj v1 v2 ==∗
  heap_inj_inv_i (heap_update h1 l1 v1) ∗
  heap_inj_inv_s (heap_update h2 l2 v2) ∗
  heap_in_inj rem.
Proof.
  iIntros (? [? Ha]) "Hinvi Hinvs Hinj [% [-> #?]] Hv".
  iDestruct (heap_in_inj_borrow with "[$] [$]") as (bi bs Hli0) "[?[Hli[??]]]"; [done|].
  iDestruct (heapUR_lookup_block with "Hinvs [$]") as %<-.
  iDestruct (heapUR_lookup_block with "Hinvi [$]") as %<-.
  iMod (heapUR_update_in_block with "[$] [$]") as "[$ ?]"; [eexists _; done|].
  iDestruct (big_sepM2_lookup_r with "[$]") as (??) "#_".
  { move: Ha. by rewrite h_block_lookup2. }
  iMod (heapUR_update_in_block with "[$] [Hli]") as "[$ ?]" => /=.
  { eexists _. by rewrite h_block_lookup2 /= Hli0 Z.add_0_l. } { done. }
  iModIntro. rewrite Hli0 Z.add_0_l.
  iApply (heap_in_inj_return0 with "[$] [$] [$] [$]"); [done|].
  by iApply (big_sepM2_insert_2 with "[Hv] [$]").
Qed.

Lemma heap_in_inj_share li ls rem bi bs :
  ls.1 ∉ rem →
  li.2 = 0%Z →
  ls.2 = 0%Z →
  heap_in_inj rem -∗
  li.1 ↦∗hi bi -∗
  ls.1 ↦∗hs bs -∗
  ([∗ map] o↦vi;vs∈bi;bs, val_in_inj vi vs) ==∗
  heap_in_inj rem ∗
  loc_in_inj li ls.
Proof.
  iIntros (? ? Hl0) "[%inj[??]] ???".
  destruct (inj !! ls.1) eqn:?. {
    iDestruct (heap_in_inj_inv_borrow with "[$]") as (???) "[? [?[??]]]"; [done..|].
    iDestruct (heapUR_block_excl with "[$] [$]") as %[]. }
  iMod (heap_inj_shared_alloc with "[$]") as "[? #$]"; [done|]. iModIntro.
  iSplit. 2: { iPureIntro. by rewrite Hl0 offset_loc_0. } iFrame.
  iApply big_sepM_insert; [done|]. iFrame. iRight. by iFrame.
Qed.

Lemma heap_in_inj_free hi hs li ls rem:
  ls.1 ∉ rem →
  ls.2 = 0%Z →
  heap_inj_inv_i hi -∗
  heap_inj_inv_s hs -∗
  loc_in_inj li ls -∗
  heap_in_inj rem ==∗
  heap_in_inj rem ∗
  heap_inj_inv_i (heap_free hi li) ∗
  heap_inj_inv_s (heap_free hs ls).
Proof.
  iIntros (? Hls2) "Hinvi Hinvs [% [-> #Hl]] Hinj".
  rewrite Hls2 offset_loc_0.
  iDestruct (heap_in_inj_borrow with "[$] [$]") as (???) "[? [? [??]]]"; [done|].
  iDestruct (heapUR_lookup_block with "Hinvi [$]") as %<-.
  iDestruct (heapUR_lookup_block with "Hinvs [$]") as %<-.
  iMod (heapUR_free with "[$] [$]") as "[$ ?]".
  iMod (heapUR_free with "[$] [$]") as "[$ ?]". iModIntro.
  iApply (heap_in_inj_return0 with "[$] [$] [$] [$]"); [done|].
  by iApply big_sepM2_empty.
Qed.

(** * heap_inj_inv *)
Definition heap_inj_inv (hi hs : heap_state) (rem : list prov) : uPred heap_injUR :=
  heap_inj_inv_i hi ∗
  heap_inj_inv_s hs ∗
  heap_in_inj rem ∗
  heap_inj_statics (h_static_provs hi) ∗
  heap_inj_statics (h_static_provs hs).


Lemma heap_inj_inv_lookup hi hs li ls v rem:
  h_heap hs !! ls = Some v →
  ls.1 ∉ rem →
  heap_inj_inv hi hs rem -∗
  loc_in_inj li ls -∗
  ∃ v', ⌜h_heap hi !! li = Some v'⌝ ∗ val_in_inj v' v.
Proof.
  iIntros (??) "[Hinvi [Hinvs[?[??]]]]".
  by iApply (heap_in_inj_lookup with "[$] [$] [$]").
Qed.

Lemma heap_inj_inv_alive hi hs li ls rem:
  heap_alive hs ls →
  ls.1 ∉ rem →
  heap_inj_inv hi hs rem -∗
  loc_in_inj li ls -∗
  ⌜heap_alive hi li⌝.
Proof.
  iIntros ([??]?) "??".
  iDestruct (heap_inj_inv_lookup with "[$] [$]") as (??) "?"; [done..|].
  iPureIntro. by eexists _.
Qed.

Lemma heap_inj_inv_lookup_dom_i p hi hs d rem dq:
  heap_inj_inv hi hs rem -∗
  p ⤚hi{dq} d -∗
  ⌜dom (h_block hi p) = d⌝.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  by iApply (heapUR_lookup_dom with "Hinvi").
Qed.

Lemma heap_inj_inv_lookup_dom_s p hi hs d rem dq:
  heap_inj_inv hi hs rem -∗
  p ⤚hs{dq} d -∗
  ⌜dom (h_block hs p) = d⌝.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  by iApply (heapUR_lookup_dom with "Hinvs").
Qed.

Lemma heap_inj_inv_lookup_block_i p hi hs b rem dq:
  heap_inj_inv hi hs rem -∗
  p ↦∗hi{dq} b -∗
  ⌜h_block hi p = b⌝.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  by iApply (heapUR_lookup_block with "Hinvi").
Qed.

Lemma heap_inj_inv_lookup_block_s p hi hs b rem dq:
  heap_inj_inv hi hs rem -∗
  p ↦∗hs{dq} b -∗
  ⌜h_block hs p = b⌝.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  by iApply (heapUR_lookup_block with "Hinvs").
Qed.

Lemma heap_inj_inv_update hi hs li ls vi vs rem :
  ls.1 ∉ rem →
  heap_alive hs ls →
  heap_inj_inv hi hs rem -∗
  loc_in_inj li ls -∗
  val_in_inj vi vs ==∗
  heap_inj_inv (heap_update hi li vi) (heap_update hs ls vs) rem.
Proof.
  iIntros (??) "(Hinvi&Hinvs&?&?&?) ? ?".
  iMod (heap_in_inj_update with "[$] [$] [$] [$] [$]") as "[$ [$ $]]"; [done..|].
  iModIntro. rewrite !h_static_provs_heap_update. iFrame.
Qed.

Lemma heap_inj_inv_update_in_block_i hi hs li v rem b :
  heap_alive hi li →
  heap_inj_inv hi hs rem -∗
  li.1 ↦∗hi b ==∗
  heap_inj_inv (heap_update hi li v) hs rem ∗
  li.1 ↦∗hi (<[li.2 :=v]> b).
Proof.
  iIntros (?) "(?&$&$&?&$) ?".
  iMod (heapUR_update_in_block with "[$] [$]") as "[$ $]"; [done|].
  by rewrite h_static_provs_heap_update.
Qed.

Lemma heap_inj_inv_update_in_block_s hi hs ls vs rem b :
  heap_alive hs ls →
  heap_inj_inv hi hs rem -∗
  ls.1 ↦∗hs b ==∗
  heap_inj_inv hi (heap_update hs ls vs) rem ∗
  ls.1 ↦∗hs (<[ls.2:=vs]> b).
Proof.
  iIntros (?) "($&Hinvs&$&$&?) ?".
  iMod (heapUR_update_in_block with "[$] [$]") as "[$ $]"; [done|].
  by rewrite h_static_provs_heap_update.
Qed.

Lemma heap_inj_inv_alloc_i hi hs li n rem:
  heap_is_fresh hi li →
  heap_inj_inv hi hs rem ==∗
  heap_inj_inv (heap_alloc hi li n) hs rem ∗
  li.1 ↦∗hi (zero_block n).
Proof.
  iIntros (Hf) "(?&$&$&?&$)". iMod (heapUR_alloc with "[$]") as "[$ $]"; [done|].
  rewrite h_static_provs_heap_alloc //. by destruct Hf as [?[??]].
Qed.

Lemma heap_inj_inv_alloc_s hi hs ls n rem:
  heap_is_fresh hs ls →
  heap_inj_inv hi hs rem ==∗
  heap_inj_inv hi (heap_alloc hs ls n) rem ∗
  ls.1 ↦∗hs (zero_block n).
Proof.
  iIntros (Hf) "($&?&$&$&?)". iMod (heapUR_alloc with "[$]") as "[$ $]"; [done|].
  rewrite h_static_provs_heap_alloc //. by destruct Hf as [?[??]].
Qed.

Lemma heap_inj_inv_alloc hi hs li ls n rem:
  heap_is_fresh hi li →
  heap_is_fresh hs ls →
  ls.1 ∉ rem →
  heap_inj_inv hi hs rem ==∗
  heap_inj_inv (heap_alloc hi li n) (heap_alloc hs ls n) rem ∗
  loc_in_inj li ls.
Proof.
  iIntros (Hi Hs ?) "?". have Hli0 : li.2 = 0 by destruct Hi as [?[??]].
  iMod (heap_inj_inv_alloc_i with "[$]") as "[? ?]"; [done|].
  iMod (heap_inj_inv_alloc_s with "[$]") as "[Hinv ?]"; [done|].
  iDestruct "Hinv" as "($ & $ &?& $ & $)".
  iMod (heap_in_inj_share with "[$] [$] [$] []") as "[$ $]"; [done..| | |done].
  { destruct Hs. naive_solver. }
  iApply big_sepM_sepM2_diag. iApply big_sepM_intro.
  iIntros "!>" (??[-> ?]%zero_block_lookup_Some). done.
Qed.

Lemma heap_inj_inv_alloc_list hi hs hi' hs' xs lsi lss:
  heap_alloc_list xs lsi hi hi' →
  heap_alloc_list xs lss hs hs' →
  heap_inj_inv hi hs [] ==∗
  heap_inj_inv hi' hs' [] ∗
  ([∗ list] li;ls∈lsi;lss, loc_in_inj li ls).
Proof.
  iIntros (Hi Hs) "Hinv".
  iInduction xs as [] "IH" forall (lsi lss hi hi' hs hs' Hi Hs); simplify_eq/=; destruct!/=.
  { by iFrame. }
  iMod (heap_inj_inv_alloc with "Hinv") as "[Hinv $]"; [done..|set_solver|].
  by iApply "IH".
Qed.

Lemma heap_inj_inv_free_i l hi hs b rem:
  heap_inj_inv hi hs rem -∗
  l.1 ↦∗hi b ==∗
  heap_inj_inv (heap_free hi l) hs rem ∗ l.1 ↦∗hi ∅.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  iMod (heapUR_free with "Hinvi [$]") as "[$ $]". iFrame.
  by rewrite h_static_provs_heap_free.
Qed.

Lemma heap_inj_inv_free_s l hi hs b rem:
  heap_inj_inv hi hs rem -∗
  l.1 ↦∗hs b ==∗
  heap_inj_inv hi (heap_free hs l) rem ∗ l.1 ↦∗hs ∅.
Proof.
  iIntros "[Hinvi [Hinvs[?[??]]]] ?".
  iMod (heapUR_free with "Hinvs [$]") as "[$ $]". iFrame.
  by rewrite h_static_provs_heap_free.
Qed.

Lemma heap_inj_inv_free hi hs li ls rem n:
  ls.1 ∉ rem →
  li.2 = 0%Z →
  ls.2 = 0%Z →
  heap_range hs ls n →
  heap_inj_inv hi hs rem -∗
  loc_in_inj li ls ==∗
  heap_inj_inv (heap_free hi li) (heap_free hs ls) rem.
Proof.
  iIntros (? ?? ?) "[Hinvi [Hinvs [? [? ?]]]] Hl".
  iMod (heap_in_inj_free with "[$] [$] [$] [$]") as "[$ [$ $]]"; [done..|].
  rewrite !h_static_provs_heap_free. by iFrame.
Qed.

Lemma heap_inj_inv_free_list hi hs hs' lis lss lis' lss' xsi xss hi0 hi0' hs0 hs0':
  heap_free_list lss hs hs' →
  lis.*2 = lss.*2 →
  lis' = lis.*1 →
  lss' = lss.*1 →
  heap_alloc_list xsi lis' hi0 hi0' →
  heap_alloc_list xss lss' hs0 hs0' →
  heap_inj_inv hi hs [] -∗
  ([∗ list] li;ls∈lis';lss', loc_in_inj li ls) ==∗
  ∃ hi', ⌜heap_free_list lis hi hi'⌝ ∗ heap_inj_inv hi' hs' [].
Proof.
  iIntros (Hf Hl2 -> -> Hai Has) "Hinv Hls".
  iInduction lss as [|[ls ?] lss] "IH" forall (hi hs hs' lis xsi xss hi0 hs0 Hf Hl2 Hai Has);
      simplify_eq/=; destruct lis as [|[li ?] lis], xsi, xss => //; destruct!/=.
  { iModIntro. iSplit!. }
  unfold heap_is_fresh in *; destruct!/=.
  iDestruct "Hls" as "[Hl Hls]".
  iAssert ⌜heap_range hi l0 z⌝%I as %?. {
    iDestruct "Hinv" as "(?&?&?&?)".
    iApply (heap_in_inj_range with "[$] [$] [$] [$]"); [done..| set_solver].
  }
  iMod (heap_inj_inv_free with "[$] [$]") as "[??]"; [set_solver|done..|].
  iMod ("IH" with "[//] [//] [//] [//] [$] [$]") as (??) "?". iModIntro. by iFrame.
Qed.

(* specialized to the same provenance and heap on both sides for now
since this suffices for statics *)
Lemma heap_inj_inv_share hi hs p h:
  heap_inj_inv hi hs [] -∗
  p ↦∗hi h -∗
  p ↦∗hs h -∗
  ([∗ map] v∈h, val_in_inj v v) ==∗
  heap_inj_inv hi hs [] ∗ loc_in_inj (p, 0%Z) (p, 0%Z).
Proof.
  iIntros "($&$&?&$&$) Hi Hs #Hv".
  iMod (heap_in_inj_share (p, 0%Z) (p, 0%Z) with "[$] [$] [$] []") as "[$ $]"; [set_solver|done|done| |done].
  by iApply (big_sepM_sepM2_diag).
Qed.

Lemma heap_inj_inv_share_big hi hs m:
  heap_inj_inv hi hs [] -∗
  ([∗ map] p↦h∈m, p ↦∗hi h) -∗
  ([∗ map] p↦h∈m, p ↦∗hs h) -∗
  ([∗ map] p↦h∈m, [∗ map] v∈h, val_in_inj v v) ==∗
  heap_inj_inv hi hs [] ∗ ([∗ map] p↦h∈m, loc_in_inj (p, 0%Z) (p, 0%Z)).
Proof.
  iIntros "Hinv Hi Hs Hv".
  iInduction m as [|???] "IH" using map_ind. { iModIntro. by iFrame. }
  rewrite !big_sepM_insert //.
  iDestruct!. iMod (heap_inj_inv_share with "[$] [$] [$] [$]") as "[? $]".
  by iApply ("IH" with "[$] [$] [$] [$]").
Qed.

Definition rec_heap_inj_init (h0 : gmap prov (gmap Z val)) : uPred heap_injUR :=
  (([∗ map]p↦v∈h0, p ↦∗hi v) ∗ ([∗ map]p↦v∈h0, p ↦∗hs v)).

Lemma rec_heap_inj_init_union h1 h2:
  h1 ##ₘ h2 →
  rec_heap_inj_init (h1 ∪ h2) ⊣⊢ rec_heap_inj_init h1 ∗ rec_heap_inj_init h2.
Proof.
  move => Hdisj. rewrite /rec_heap_inj_init.
  rewrite !big_sepM_union //. iSplit; iIntros!; iFrame.
Qed.

Lemma heap_inj_inv_share_init hi hs f statics :
  heap_inj_inv hi hs [] -∗
  rec_heap_inj_init (fd_init_heap f statics) ==∗
  ([∗ list] l ∈ static_locs f statics, loc_in_inj l l) ∗ heap_inj_inv hi hs [].
Proof.
  iIntros "Hinv [Hi Hs]".
  iMod (heap_inj_inv_share_big with "Hinv Hi Hs []") as "[$ ?]". {
    iApply big_sepM_intro. iIntros "!>" (??[?[?[?[??]]]]%fd_init_heap_lookup_Some).
    simplify_eq. iApply big_sepM_intro.
    iIntros "!>" (??[??]%zero_block_lookup_Some); by simplify_eq/=.
  }
  iModIntro. rewrite /fd_init_heap.
  rewrite big_sepM_list_to_map. 2: {
    apply NoDup_alt => ???. rewrite !list_lookup_fmap_Some.
    setoid_rewrite lookup_zip_with_Some.
    setoid_rewrite static_provs_lookup_Some.
    naive_solver. }
  rewrite big_sepL_zip_with /= /static_locs big_sepL_fmap.
  iApply (big_sepL_impl with "[$]"). iIntros "!>" (???%static_provs_lookup_Some) "?".
  case_match eqn: Heq => //. apply lookup_ge_None in Heq. lia.
Qed.

Lemma heap_inj_inv_share_inits hi hs fns :
  heap_inj_inv hi hs [] -∗
  rec_heap_inj_init (fds_init_heap fns) ==∗
  ([∗ map] f↦fn∈fns, [∗ list] l ∈ static_locs f fn, loc_in_inj l l) ∗ heap_inj_inv hi hs [].
Proof.
  iIntros "Hinv Hinit".
  iInduction fns as [|f fn fns Hf] "IH" using map_ind forall (hi hs).
  { iModIntro. iFrame. done. }
  rewrite fds_init_heap_insert // rec_heap_inj_init_union.
  2: by apply fds_init_heap_map_disjoint.
  iDestruct "Hinit" as "[? Hinit2]".
  iMod ("IH" with "Hinv Hinit2") as "[? Hinv]".
  iMod (heap_inj_inv_share_init with "[$] [$]") as "[??]".
  iModIntro. rewrite big_sepM_insert //. iFrame.
Qed.


Lemma heap_inj_init ps :
  satisfiable (heap_inj_shared_auth ∅ ∗ heap_inj_statics ps
                 ∗ heap_inj_inv_i ∅ ∗ heap_inj_inv_s ∅).
Proof.
  apply: (satisfiable_init (Some (to_agree ps),
              (gmap_view_auth (DfracOwn 1) ∅,
              (heapUR_init, heapUR_init)))). {
    split; [done|] => /=.
    split; [by eapply (gmap_view_auth_dfrac_valid _ (DfracOwn 1))|].
    split; apply heapUR_init_valid. }
  rewrite (pair_split (Some _)) uPred.ownM_op.
  rewrite (pair_split (gmap_view_auth _ _)) pair_op_2 uPred.ownM_op.
  rewrite (pair_split (heapUR_init)) !pair_op_2 uPred.ownM_op.
  iIntros!. rewrite -!heapUR_init_own /heap_inj_shared_auth big_sepM_empty. by iFrame.
Qed.

Lemma heap_inj_inv_init bs :
  satisfiable (heap_inj_inv (heap_from_blocks bs) (heap_from_blocks bs) [] ∗ rec_heap_inj_init bs).
Proof.
  apply: satisfiable_bmono; [apply heap_inj_init|].
  iIntros "(? & #? & Hinvi & Hinvs)".
  iMod (heapUR_alloc_blocks with "Hinvi") as "[Hinvi $]"; [set_solver|].
  iMod (heapUR_alloc_blocks with "Hinvs") as "[Hinvs $]"; [set_solver|].
  iModIntro. rewrite right_id. iFrame "Hinvi Hinvs #".
  by iApply heap_in_inj_init.
Qed.

(** * Definition of [rec_heap_inj] *)
Definition rec_heap_inj_pre (e : rec_event) (s : unit) : prepost (rec_event * unit) heap_injUR :=
  let vsi := vals_of_event e.2 in
  let hi := heap_of_event e.2 in
  pp_quant $ λ vss,
  pp_quant $ λ hs,
  pp_star (heap_inj_inv hi hs [] ∗ [∗ list] v1;v2∈vsi;vss, val_in_inj v1 v2) $
  pp_end ((e.1, event_set_vals_heap e.2 vss hs), tt).

Definition rec_heap_inj_post (e : rec_event) (s : unit) : prepost (rec_event * unit) heap_injUR :=
  let vss := vals_of_event e.2 in
  let hs := heap_of_event e.2 in
  pp_quant $ λ vsi,
  pp_quant $ λ hi,
  pp_star (heap_inj_inv hi hs [] ∗ [∗ list] v1;v2∈vsi;vss, val_in_inj v1 v2) $
  pp_end ((e.1, event_set_vals_heap e.2 vsi hi), tt).

Definition rec_heap_inj_trans (m : mod_trans rec_event) : mod_trans rec_event :=
  prepost_trans rec_heap_inj_pre rec_heap_inj_post m.

Definition rec_heap_inj (h0 : gmap prov (gmap Z val)) (m : module rec_event) : module rec_event :=
  Mod (rec_heap_inj_trans m.(m_trans)) (SMFilter, m.(m_init), (PPOutside, tt,
   uPred_shrink (rec_heap_inj_init h0))).

Lemma rec_heap_inj_trefines m m' h0 `{!VisNoAng m.(m_trans)}:
  trefines m m' →
  trefines (rec_heap_inj h0 m) (rec_heap_inj h0 m').
Proof. move => ?. by apply: prepost_mod_trefines. Qed.

(** ** rec_heap_inj_N *)
Definition rec_heap_inj_N n h0 (m: module rec_event) : module rec_event :=
  Nat.iter n (rec_heap_inj h0) m.

Global Instance rec_heap_inj_N_vis_no_all n m h0 `{!VisNoAng m.(m_trans)} :
  VisNoAng (rec_heap_inj_N n h0 m).(m_trans).
Proof. elim: n => //= ??. apply _. Qed.

(** * Proof techniques for [rec_heap_inj] *)
Definition rec_heap_inj_call (n : ordinal) (fns1 fns2 : gmap string fndef) INV :=
  (∀ n' f es1' es2' K1' K2' es1 es2 vs1' vs2' h1' h2' b r rf',
      RecExprFill es1' K1' (Call (Val (ValFn f)) es1) →
      RecExprFill es2' K2' (Call (Val (ValFn f)) es2) →
      n' ⊆ n →
      Forall2 (λ e v, e = Val v) es1 vs1' →
      Forall2 (λ e v, e = Val v) es2 vs2' →
      satisfiable (heap_inj_inv h1' h2' [] ∗ ([∗ list] v1;v2∈vs1';vs2', val_in_inj v1 v2) ∗ INV ∗ r ∗ rf') →
      (∀ v1'' v2'' h1'' h2'' rf'',
        satisfiable (heap_inj_inv h1'' h2'' [] ∗ val_in_inj v1'' v2'' ∗ INV ∗ r ∗ rf'') →
        Rec (expr_fill K1' (Val v1'')) h1'' fns1
            ⪯{rec_trans, rec_heap_inj_trans rec_trans, n', true}
        (SMProg, Rec (expr_fill K2' (Val v2'')) h2'' fns2, (PPInside, tt, uPred_shrink rf''))) →
      Rec es1' h1' fns1
          ⪯{rec_trans, rec_heap_inj_trans rec_trans, n', b}
      (SMProg, Rec es2' h2' fns2, (PPInside, tt, uPred_shrink rf'))).

Definition rec_heap_inj_return n fns1 fns2 Ki Ks r INV :=
  (∀ n' v1 v2 h1' h2' rf' b,
      n' ⊆ n →
      satisfiable (heap_inj_inv h1' h2' [] ∗ val_in_inj v1 v2 ∗ INV ∗ r ∗ rf') →
      Rec (expr_fill Ki (Val v1)) h1' fns1
        ⪯{rec_trans, rec_heap_inj_trans rec_trans, n', b}
      (SMProg, Rec (expr_fill Ks (Val v2)) h2' fns2, (PPInside, (), uPred_shrink rf'))).

Lemma rec_heap_inj_call_mono n n' fns1 fns2 INV :
  rec_heap_inj_call n fns1 fns2 INV →
  n' ⊆ n →
  rec_heap_inj_call n' fns1 fns2 INV .
Proof.
  intros Hprf ???????????????????????.
  eapply Hprf; eauto. by etrans.
Qed.

Lemma rec_heap_inj_return_mono n n' fns1 fns2 K1 K2 r INV:
  rec_heap_inj_return n fns1 fns2 K1 K2 r INV →
  n' ⊆ n →
  rec_heap_inj_return n' fns1 fns2 K1 K2 r INV.
Proof.
  intros Hprf ??????????.
  eapply Hprf; eauto. by etrans.
Qed.

Lemma rec_heap_inj_proof INV fns1 fns2 h0 :
  dom fns1 = dom fns2 →
  (∀ f fn1, fns1 !! f = Some fn1 → ∃ fn2, fns2 !! f = Some fn2
                                          ∧ length (fd_args fn1) = length (fd_args fn2)
                                          ∧ fd_static_vars fn1 = fd_static_vars fn2) →
  (∀ hi hs, rec_heap_inj_init h0 -∗ heap_inj_inv hi hs [] ==∗ INV ∗ heap_inj_inv hi hs []) →
  (∀ n K1 K2 f fn1 fn2 vs1 vs2 h1 h2 r rf,
      fns1 !! f = Some fn1 →
      fns2 !! f = Some fn2 →
      length vs1 = length (fd_args fn1) →
      length vs2 = length (fd_args fn2) →
      satisfiable (heap_inj_inv h1 h2 [] ∗ ([∗ list] v1;v2∈vs1;vs2, val_in_inj v1 v2) ∗ INV ∗ r ∗ rf) →

      rec_heap_inj_call n fns1 fns2 INV →
      rec_heap_inj_return n fns1 fns2 K1 K2 r INV →

      Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f (fd_static_vars fn1) $ subst_l fn1.(fd_args) vs1 (fd_body fn1))) h1 fns1
          ⪯{rec_trans, rec_heap_inj_trans rec_trans, n, false}
      (SMProg, Rec (expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f (fd_static_vars fn2) $ subst_l fn2.(fd_args) vs2 (fd_body fn2))) h2 fns2, (PPInside, tt, uPred_shrink rf))) →
  trefines (rec_mod fns1) (rec_heap_inj h0 (rec_mod fns2)).
Proof.
  move => Hdom Hlen Hinit Hf.
  rewrite (lock (dom _)) in Hdom. unfold rec_heap_inj.
  etrans. 2: {
    apply (mod_prepost_impl_prop _ _ _ _ INV); [apply _| ] => /=.
    iIntros (???) "? [[? ?] $]".
    iMod (Hinit with "[$] [$]") as "[$ $]". by iFrame. }
  pose (R := λ (b : bool) (s1 s2 : (unit * uPred heap_injUR)), (if b then s1.2 ≡ s2.2 else True) ∧ (s2.2 ⊢ INV ∗ (INV -∗ s2.2))).
  apply: (rec_prepost_proof R); unfold R; [| | naive_solver.. |].
  { destruct b.
    - move => ??? [-> ?] //.
    - move => //. }
  { split!. iIntros "$". iIntros "$". }
  move => n K1 K2 f fn1 vs1 h1 [] r1 /= [_ Hstat] Hfn1 /= vs2 h2 rf Hsat.
  iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
  have [?[??]]:= (Hlen _ _ ltac:(done)).
  split!. move => ?. split; [lia|].
  move => Hcall Hret.
  unshelve eapply tsim_remember'. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(σfs, Rec e2 h2 fns2', (t1, _, rf')),
     ∃ K1 K2 f vs1 vs2 fn1 fn2 r rrf',
       rf' = uPred_shrink rrf' ∧
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       fns1 !! f = Some fn1 ∧
       fns2 !! f = Some fn2 ∧
       e1 = expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f (fd_static_vars fn1) $ subst_l (fd_args fn1) vs1 (fd_body fn1)) ∧
       e2 = expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f (fd_static_vars fn2) $ subst_l (fd_args fn2) vs2 (fd_body fn2)) ∧
       length vs1 = length (fd_args fn1) ∧
       σfs = SMProg ∧
       t1 = PPInside ∧
       satisfiable (heap_inj_inv h1 h2 []
            ∗ ([∗ list] v1;v2∈vs1;vs2, val_in_inj v1 v2)
            ∗ INV
            ∗ r ∗ rrf') ∧
       rec_heap_inj_return n' fns1 fns2 K1 K2 r INV). }
  { move => /= ??. split! => //; [lia|..]. {
      iSatMono. iFrame. iStopProof.
      etrans; [apply Hstat|]. iIntros!. iFrame. iAccu. } iSatClear.
    move => ?????????. apply: tsim_mono; [|done]. apply: Hret; [done|]. eexists [_]. split!.
    iSatMono. iIntros!. iFrame. iDestruct select (INV -∗ _)%I as "H". by iApply "H". }
  iSatClear. move => n' /= ? IH [e1 {}h1 ?] [[σfs [e2 {}h2 ?]] [[?[]]?]] ?. destruct!. simplify_eq/=.
  have [?[??]]:= (Hlen _ _ ltac:(done)).
  iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
  apply: Hf => //; [lia|..]. { iSatMono. iFrame. }
  - iSatClear. move => ? f1 es1 es2 ?? es1' es2' vs1' vs2' ????? [?] [?] ? Hall1 Hall2 ? Hret'.
    have ?: es1' = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
    have ?: es2' = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
    destruct (fns1 !! f1) eqn: ?.
    + tstep_both. split; [|naive_solver].
      move => ??. have [?[??]]:= (Hlen _ _ ltac:(done)). tstep_s. left. split! => ?. tend.
      iSatStart. iIntros!. iDestruct (big_sepL2_length with "[$]") as %?. iSatStop.
      split; [lia|].
      apply: IH; [done|]. move => ??.
      split! => //; [lia|..]. { iSatMono. iFrame. iAccu. }
      move => *. apply: tsim_mono_to_true; [naive_solver|]. etrans; [|done]. by econs.
    + apply: Hcall; [by etrans|done|..].
      { apply not_elem_of_dom. unlock in Hdom. rewrite -Hdom. by apply not_elem_of_dom. }
      1,2: by apply Forall2_fmap_l, Forall_Forall2_diag, Forall_true.
      split!. 2: { iSatMono. iIntros!. iFrame. iAccu. }
      { by iIntros "[$ $] $". }
      iSatClear. move => ????[??]????. setoid_subst. split!.
      apply: tsim_mono_b. apply: Hret'. iSatMono. iIntros!. iFrame.
      iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". by simplify_eq.
Qed.

(** * Properties of [rec_heap_inj] *)
(** ** Horizontal compositionality *)
Lemma rec_heap_inj_combine fns1 fns2 m1 m2 h01 h02 h0 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  h01 ##ₘ h02 →
  h0 = h01 ∪ h02 →
  trefines (rec_link fns1 fns2 (rec_heap_inj h01 m1) (rec_heap_inj h02 m2))
           (rec_heap_inj h0 (rec_link fns1 fns2 m1 m2)).
Proof.
  move => Hdisj ->.
  unshelve apply: prepost_link. { exact
      (λ ips s1 s2 s x1 x2 x ics1 ics2,
        ics1 = ics2 ∧
        match ips with
        | None => x ⊣⊢ x1 ∗ x2
        | Some SPLeft => x1 = (x ∗ x2)%I
        | Some SPRight => x2 = (x ∗ x1)%I
        end
      ). }
  { move => ?? [] /=*; naive_solver. }
  { split!. rewrite /rec_heap_inj_init !big_sepM_union //. iSplit; iIntros!; iFrame. }
  all: move => [] [] [] P1 P2 P ics1 ics2.
  - move => e ics' e' /= ? ? *; destruct!/=.
    setoid_subst.
    split!.
    { iSatMono. iIntros!. iFrame. }
    { by destruct e. }
  - move => e ics' e' /= ? ? *; destruct!/=.
    setoid_subst.
    split!.
    { iSatMono; iIntros!; iFrame. }
    { by destruct e. }
  - move => [? e] /= ? Hr *. destruct!/=.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    split!.
    { iSatMono; iIntros!. iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    { by destruct e. }
    { by destruct e. }
  - move => [? e] /= *; destruct!/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
  - move => [? e] /= ? *; destruct!/=.
    split!.
    all: rewrite ?heap_of_event_event_set_vals_heap; split!.
    { iSatMono; iIntros!; iFrame.
      iDestruct (big_sepL2_length with "[$]") as %?. rewrite vals_of_event_event_set_vals_heap //. }
    1: by destruct e.
    1: by destruct e.
  - move => [? e] /= ? *; destruct!/=.
    split!.
    1: by destruct e.
    { iSatMono; iIntros!; iFrame. }
Qed.

(** ** Reflexivity *)
Lemma rec_heap_inj_sim_call_bind args vs' ws' es ei Ks Ki vss vsi vfi vfs n b hi hs fns1 fns2 rf r INV
  `{Hfill2: !RecExprFill ei Ki (Call (Val vfi) ((Val <$> vs') ++ (subst_map vsi <$> args)))}
  `{Hfill1: !RecExprFill es Ks (Call (Val vfs) ((Val <$> ws') ++ (subst_map vss <$> args)))}:
    satisfiable (heap_inj_inv hi hs [] ∗ ([∗ map] vi;vs ∈ vsi; vss, val_in_inj vi vs) ∗ ([∗ list] v; w ∈ vs'; ws', val_in_inj v w) ∗ val_in_inj vfi vfs ∗ INV ∗ r ∗ rf) →
    dom vss ⊆ dom vsi →
    rec_heap_inj_call n fns1 fns2 INV →
    (∀ vs ws hi' hs' b' n' rf' f,
      n' ⊆ n →
      satisfiable (heap_inj_inv hi' hs' [] ∗ ([∗ map] vi;vs ∈ vsi; vss, val_in_inj vi vs) ∗ ([∗ list] v; w ∈ vs' ++ vs; ws' ++ ws, val_in_inj v w) ∗ INV ∗ r ∗ rf') →
      Rec (expr_fill Ki (Call (Val (ValFn f)) (Val <$> (vs' ++ vs)))) hi' fns1
        ⪯{rec_trans, rec_heap_inj_trans rec_trans, n', b'}
      (SMProg, Rec (expr_fill Ks (Call (Val (ValFn f)) (Val <$> (ws' ++ ws)))) hs' fns2, (PPInside, (), uPred_shrink rf'))
    ) →
    Forall
    (λ e : expr,
       ∀ es ei hi hs n b Ki Ks r rf,
         RecExprFill es Ks (subst_map vss e)
         → RecExprFill ei Ki (subst_map vsi e)
             → rec_heap_inj_call n fns1 fns2 INV
                  → satisfiable
                      (heap_inj_inv hi hs [] ∗
                      ([∗ map] v1;v2 ∈ vsi;vss, val_in_inj v1 v2) ∗ INV ∗ r ∗
                      rf)
                      → rec_heap_inj_return n fns1 fns2 Ki Ks r INV
                     → Rec ei hi fns1 ⪯{rec_trans,
                     rec_heap_inj_trans rec_trans, n, b}
                     (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf))) args →
    Rec ei hi fns1
      ⪯{rec_trans, rec_heap_inj_trans rec_trans, n, b}
    (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  intros Hsat Hdom Hfuns Hcont Hargs; destruct Hfill1 as [->], Hfill2 as [->].
  induction args as [|e args IH] in n, b, vs', ws', hs, hi, Hsat, Hcont, Hargs, Hfuns, rf |-*; simpl.
 - specialize (Hcont [] []). rewrite !app_nil_r in Hcont.
   rewrite !app_nil_r. tstep_s => ??. simplify_eq/=.
   iSatStart. iIntros!. destruct vfi => //=. iDestruct!. iSatStop.
   eapply Hcont; [done|]. iSatMono. iFrame.
 - eapply Forall_cons_1 in Hargs as [Harg Hall].
   apply: Harg.
  + eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end.
  + eapply rec_expr_fill_expr_fill, (rec_expr_fill_expr_fill _ [CallCtx _ _ _]), rec_expr_fill_end.
  + done.
  + iSatMono. iIntros "(Hinj & #Hvals & #Hvals' & Hf & Hs & r & rf)". iFrame.
    iFrame "Hvals". iCombine "Hvals Hvals' Hf r" as "r". iExact "r".
  + simpl. iSatClear. intros n' v w h1' h2' rf' b' Hsub Hsat'. simpl.
    rewrite !cons_middle !app_assoc. change ([Val v]) with (Val <$> [v]).
    change ([Val w]) with (Val <$> [w]). rewrite -!fmap_app.
    specialize (IH (vs' ++ [v]) (ws' ++ [w]) n' b' h1' h2' rf').
    eapply IH; eauto.
    * iSatMono. iIntros!. by iFrame.
    * by apply: rec_heap_inj_call_mono.
    * intros vs ws hi' hs' b'' n'' rf'' Hsub' Hsat. rewrite -!app_assoc.
      clear IH Hall Hsat'. eapply Hcont; first by etrans.
Qed.

Lemma rec_heap_inj_sim_refl_static INV vss vsi e es ei hi hs n b Ki Ks fns1 fns2 r rf
  `{Hfill1: !RecExprFill es Ks (subst_map vss e)}
  `{Hfill2: !RecExprFill ei Ki (subst_map vsi e)}:
  dom vss ⊆ dom vsi →
  rec_heap_inj_call n fns1 fns2 INV →
  rec_heap_inj_return n fns1 fns2 Ki Ks r INV →
  is_static_expr false e →
  satisfiable (heap_inj_inv hi hs [] ∗ ([∗ map] v1;v2 ∈ vsi; vss, val_in_inj v1 v2) ∗ INV ∗ r ∗ rf) →
  Rec ei hi fns1 ⪯{rec_trans, rec_heap_inj_trans rec_trans, n, b} (SMProg, Rec es hs fns2, (PPInside, (), uPred_shrink rf)).
Proof.
  induction e as [x|v|e1 op e2 IH1 IH2|e IH|e1 e2 IH1 IH2|e e1 e2 IH IH1 IH2| x e1 e2 IH1 IH2| f args IH| | | |] in vss, vsi, hi, hs, n, b, Ks, Ki, es, ei, Hfill1, Hfill2, r, rf |-*;
    intros Hsub Hcall Hcont Hstatic Hsat;
    destruct Hfill1 as [->], Hfill2 as [->].
  - simpl. destruct (vss !! x) as [v|] eqn: Hlook; last first.
    + tstep_s. done.
    + eapply elem_of_dom_2 in Hlook as Hel.
      eapply elem_of_weaken in Hel; last done.
      eapply elem_of_dom in Hel as [w Hlook'].
      rewrite Hlook'. eapply Hcont; simpl.
      { done. }
      { iSatMono. iIntros "($ & Hm & $ & $)". iApply (big_sepM2_lookup with "Hm"); done. }
  - simpl. eapply Hcont; first done.
    iSatMono. iIntros "($ & Hm & $ & $)". destruct v; done.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstat2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: IH2; simpl; eauto; last first.
    { iSatMono. iIntros "($ & #Hv & $ & [#Hm r] & $)". iFrame "Hm". iCombine "Hm Hv r " as "r". iExact "r". }
    2: { by apply: rec_heap_inj_call_mono. }
    iSatClear. intros n'' wi ws hi'' hs'' rf'' b'' Hn'' Hsat; simpl.
    tstep_s. intros w Heval. iSatStart.
    iIntros "(Hinv & Hw & HINV & (Hsub & Hv & r) & rf)".
    iDestruct (eval_binop_inj with "Hv Hw") as "[%u [% Hu]]"; first done.
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame.
  - simpl. simpl in Hstatic.
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. intros l v' -> Hlook. iSatStart.
    iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)".
    destruct vi; try done; simpl.
    iDestruct (heap_inj_inv_lookup with "Hinv Hv") as "[%w [% #Hw]]"; [done|set_solver|].
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame. iFrame "Hw".
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstat2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
      iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: IH2; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hv & $ & (#Hm & r) & $)". iFrame "Hm". iCombine "Hm Hv r " as "r". iExact "r". }
    2: { by apply: rec_heap_inj_call_mono. }
    iSatClear. intros n'' wi ws hi'' hs'' rf'' b'' Hn'' Hsat; simpl.
    tstep_s. intros w -> Halive. iSatStartBupd.
    iIntros "(Hinv & #Hw & HINV & (Hsub & Hv & r) & rf)".
    destruct vi; try done.
    iDestruct (heap_inj_inv_alive with "Hinv Hv") as "%"; [done|set_solver|].
    iMod (heap_inj_inv_update with "Hinv Hv Hw") as "Hinv"; [set_solver|done|]. iModIntro.
    iSatStop. tstep_i. split!. eapply Hcont; first by etrans.
    iSatMono. iFrame. iFrame "Hw".
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic Hstatic2].
    eapply andb_True in Hstatic as [Hstatic Hstatic1].
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. intros cond ->. iSatStart.
    iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)".
    destruct vi; try done; simpl. iDestruct "Hv" as "->". iSatStop.
    tstep_i. destruct cond.
    + apply: IH1; simpl; eauto.
      { by apply: rec_heap_inj_call_mono. }
      { by apply: rec_heap_inj_return_mono. }
      iSatMono. iFrame.
    + apply: IH2; simpl; eauto.
      { by apply: rec_heap_inj_call_mono. }
      { by apply: rec_heap_inj_return_mono. }
      iSatMono. iFrame.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstatic2].
    apply: IH1; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    tstep_s. tstep_i. rewrite -!subst_subst_map_delete.
    apply: IH2; simpl; eauto.
    { set_solver. }
    { by apply: rec_heap_inj_call_mono. }
    { by apply: rec_heap_inj_return_mono. }
    iSatMono. iIntros "(Hinv & Hv & HINV & (Hsub & r) & rf)". iFrame.
    iApply (big_sepM2_insert_2 with "[Hv]"); by iFrame.
  - simpl. simpl in Hstatic. eapply andb_True in Hstatic as [Hstatic1 Hstatic2].
    apply: IH; simpl; [eauto..|]; last first.
    { iSatMono. iIntros "($ & #Hm & $ & r & $)". iFrame "Hm". iCombine "Hm r" as "r". iExact "r". }
    iSatClear. intros n' vi vs hi' hs' rf' b' Hn' Hsat; simpl.
    apply: (rec_heap_inj_sim_call_bind args nil nil); simpl; eauto.
    + iSatMono. iIntros!. iFrame. iAccu.
    + by apply: rec_heap_inj_call_mono.
    + clear Hsat vs hi' hs' b' rf'. intros vs ws hi' hs' b' n'' rf' f' Hn'' Hsat'.
      apply: Hcall; simpl; eauto.
      * by etrans.
      * by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall.
      * by eapply Forall2_fmap_l, Forall_Forall2_diag, Forall_forall.
      * iSatMono. iIntros "($ & ? & $ & $)".
      * move => *. apply Hcont; [by etrans|done].
    + eapply Forall_forall. intros x Hx.
      eapply Forall_forall in H; last done.
      intros ???????????????. eapply H; eauto.
      simpl in Hstatic2. by eapply forallb_True, Forall_forall in Hstatic2.
  - done.
  - done.
  - done.
  - done.
Qed.

Lemma rec_heap_inj_refl fns:
  trefines (rec_mod fns) (rec_heap_inj (fds_init_heap (fd_static_vars <$> fns)) (rec_mod fns)).
Proof.
  pose (INV := ([∗ map] f↦fn∈fns, [∗ list] l ∈ static_locs f (fd_static_vars fn), loc_in_inj l l)%I).
  apply: (rec_heap_inj_proof INV).
  { done. } { naive_solver. } {
    rewrite /INV. iIntros (??) "Hinit Hinv".
    iMod (heap_inj_inv_share_inits with "Hinv Hinit"). by rewrite big_sepM_fmap.
  }
  move => n K1 K2 f fn1 fn2 vs1 v2 h1 h2 r rf ????? Hcall Hret. simplify_eq.
  rewrite !subst_l_subst_map //.
  tstep_s. pose proof (heap_alloc_list_fresh (fd_vars fn1).*2 ∅ h2) as [??].
  split!; [done|]. move => ?.
  tstep_i => ???. split!.
  have Hlen1 := (heap_alloc_list_length _ (heap_fresh_list _ _ _) _ _ ltac:(done)).
  have Hlen2 := (heap_alloc_list_length _ _ _ _ ltac:(done)).
  rewrite length_fmap in Hlen1, Hlen2.
  rewrite /subst_static !subst_l_subst_map ?length_fmap ?length_imap ?length_fmap -?subst_map_subst_map //.
  apply: (rec_heap_inj_sim_refl_static INV); last first.
  - iSatMonoBupd. iIntros "(? & Hvs & #HINV & r & $)".
    iMod (heap_inj_inv_alloc_list with "[$]") as "[$ Hl]"; [done..|iDestruct "Hl" as "#Hl"].
    iModIntro.
    rewrite -!list_to_map_app. iFrame "HINV".
    iCombine "Hl r" as "r". iSplitR "r"; [| iAccu].
    iApply big_sepM2_list_to_map_2;
      rewrite ?fmap_app ?fst_zip ?snd_zip ?length_fmap ?length_imap ?length_fmap //; try lia.
    iApply (big_sepL2_app with "[Hvs]"); [done|].
    iApply big_sepL2_app; [| by rewrite big_sepL2_fmap_l !big_sepL2_fmap_r].
    iClear "Hl". iApply big_sepL_sepL2_diag.
    rewrite big_sepL_fmap /=.
    rewrite /INV. by iDestruct (big_sepM_lookup with "HINV") as "?".
  - apply fd_static.
  - iSatClear. move => /= ?????????.
    tstep_s => hs' Hfrees.
    tstep_i.
    iSatStartBupd. iIntros!.
    iMod (heap_inj_inv_free_list with "[$] [$]") as (??) "?"; [done|..]; last (iModIntro; iSatStop; split!; [done|]).
    all: rewrite ?snd_zip ?fst_zip ?length_fmap //; try lia.
    apply: Hret; [done|].
    iSatMono. iFrame.
  - done.
  - rewrite !dom_union_L !dom_list_to_map_L !fst_zip ?length_fmap ?length_imap ?length_fmap //; lia.
Qed.

(** ** Adequacy *)

Lemma rec_heap_inj_rec_closed hinit bs m :
  hinit ⊆ bs →
  let h := (heap_from_blocks bs) in
  trefines (rec_closed h (rec_heap_inj hinit m)) (rec_closed h m).
Proof.
  move => Hh h.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { simpl. exact (λ _
          '(σm1, (σf, σ1, (pp, _, r)), σc1)
          '(σm2, σ2, σc2),
           ∃ rr, r = uPred_shrink rr ∧ σ1 = σ2 ∧ σc1 = σc2 ∧
             ((σc1 = RCStart h ∧ σf = SMFilter ∧ pp = PPOutside ∧ σm1 = σm2 ∧ σm2 = SMFilter ∧ rr = rec_heap_inj_init hinit) ∨
              ( ((∃ e, σf = SMProgRecv e ∧ σm2 = SMProgRecv e) ∨ (σf = SMProg ∧ σm2 = SMProg)
                 ) ∧ σm1 = SMProg ∧ σc1 = RCRunning ∧ pp = PPInside))
                             ). }
  { split!. } { done. }
  move => {}n _ /= Hloop [[σm1 [[σf σ1] [[pp []] r]]] σc1] [[σm2 σ2] σc2] ?.
  destruct!/=.
  - tstep_i. apply steps_impl_step_end => ???. inv_all/= @m_step. split!.
    tstep_s. eexists (Some (SMEEmit _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
    tstep_s. eexists (Some (SMEReturn _)). split!. apply: steps_spec_step_end; [econs|] => ??. simplify_eq/=.
    tstep_i => ??; simplify_eq/=.
    tstep_i. eexists (ValNum <$> vs), h. split!.
    { apply: satisfiable_mono; [by apply (heap_inj_inv_init bs)|]. iIntros "[$ [Hi Hs]]".
      iSplitL.
      - iSplitL "Hi"; by iApply big_sepM_subseteq.
      - iSplitL; [|iAccu]. rewrite big_sepL2_fmap_l big_sepL2_fmap_r. iApply big_sepL2_intro; [done|].
        iIntros "!>" (?????). by simplify_eq/=. }
    apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. case_match => *; simplify_eq.
    + tstep_s.  eexists (Some _). split; [done|]. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
    + tstep_s. eexists None. apply: steps_spec_step_end; [done|] => ??. tend. split!; [done|].
      apply: Hloop; [done|]. split!.
  - tstep_both. apply steps_impl_step_end => κ ??. tstep_s. eexists _. apply: steps_spec_step_end; [done|] => ??.
    destruct κ as [e|]; tend; (split!; [done|]). 2: { apply: Hloop; [done|]. split!. }
    tstep_i => ? vs *. tstep_both => *.
    apply steps_impl_step_end => ???. inv_all @m_step => ?; simplify_eq.
    + destruct e as [? [? vs' |]]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=. tend.
      split!.
      tstep_both. apply steps_impl_step_end => ???. inv_all @m_step.
      tstep_s. eexists (None). apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=. tend.
      iSatStart.
      iIntros!. iDestruct (big_sepL2_ValNum_inv_r with "[$]") as %?. subst.
      iSatStop.
      split!; [done|].
      tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEEmit _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i. apply steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEReturn _)). split!. apply: steps_spec_step_end; [econs|] => /=? ->.
      tstep_i => ? <-.
      tstep_i. eexists [ValNum _]. split!.
      { iSatMono. iIntros!. iFrame. iSplitR; [by iPureIntro|]. instantiate (1:=True%I). done. }
      apply: Hloop; [done|]. split!.
    + destruct e as [? []]; simplify_eq/=.
      tstep_s. eexists (Some _). split!.
      apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=.
      tstep_s. eexists None. apply: steps_spec_step_end; [econs|]=> /=??. destruct!/=.
      iSatStart. iIntros!.
      iDestruct (big_sepL2_cons_inv_r with "[$]") as ([]??) "[??]"; subst => //=; iDestruct!.
      iSatStop.
      tend. split!.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step. split!.
      tstep_s. eexists (Some (SMEEmit _)). split!.
      apply: steps_spec_step_end; [econs|]=> /=? ->.
      tstep_i. apply: steps_impl_step_end => ???. inv_all @m_step.
Qed.

(** ** [rec_heap_inj] is adequate wrt. contextual refinement *)
(** Follows from the lemmas above. *)
Lemma rec_heap_inj_trefines_implies_ctx_refines fnsi fnss :
  dom fnsi = dom fnss →
  fd_static_vars <$> fnsi = fd_static_vars <$> fnss →
  trefines (rec_mod fnsi) (rec_heap_inj (fds_init_heap (fd_static_vars <$> fnss)) (rec_mod fnss)) →
  rec_ctx_refines fnsi fnss.
Proof.
  move => Hdom Hs Href C HC. rewrite /rec_syn_link map_difference_union_r (map_difference_union_r fnss).
  etrans. 2: {
    by apply (rec_heap_inj_rec_closed (fds_init_heap (fd_static_vars <$> fnss ∪ C ∖ fnss))).
  }
  rewrite !map_fmap_union Hs. rewrite {1}(map_difference_eq_dom_L C fnsi fnss) //.
  apply seq_map_mod_trefines. { apply _. } { apply _. }
  etrans. { apply rec_syn_link_refines_link. apply map_disjoint_difference_r'. }
  etrans. { eapply rec_link_trefines. 1,2: apply _. 1: done. 1: apply rec_heap_inj_refl. }
  etrans. { apply rec_heap_inj_combine. 1,2: apply _. 2: done.
            apply fds_init_heap_disj. apply map_disjoint_fmap.
            rewrite (map_difference_eq_dom_L C fnsi fnss) //. apply map_disjoint_difference_r'. }
  rewrite fds_init_heap_union. 2: { apply map_disjoint_fmap. apply map_disjoint_difference_r'. }
  rewrite {1}(map_difference_eq_dom_L C fnsi fnss) //.
  apply rec_heap_inj_trefines. 1: apply _.
  etrans. 2: { apply rec_link_refines_syn_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  erewrite map_difference_eq_dom_L => //.
  apply _.
Qed.

(** * Exercising [rec_heap_inj] *)
Module rec_heap_inj_example.

Local Open Scope Z_scope.

Definition inj_alloc : fndef := {|
  fd_args := [];
  fd_vars := [("tmp", 1)];
  fd_static_vars := [];
  fd_body := (LetE "_" (Store (Var "tmp") (Val 1))
             (LetE "_" (Call (Val (ValFn "ext")) [])
             (Load (Var "tmp"))));
  fd_static := I;
|}.

Definition inj_alloc_opt : fndef := {|
  fd_args := [];
  fd_vars := [];
  fd_static_vars := [];
  fd_body := (LetE "_" (Call (Val (ValFn "ext")) [])
             (Val 1));
  fd_static := I;
|}.

Lemma inj_alloc_opt_refines :
  trefines (rec_mod (<["f" := inj_alloc_opt]> ∅))
           (rec_heap_inj ∅ (rec_mod (<["f" := inj_alloc]> ∅))).
Proof.
  apply: (rec_heap_inj_proof True). { compute_done. }
  { move => ??. setoid_rewrite lookup_insert_Some. setoid_rewrite lookup_empty. naive_solver. }
  { iIntros!. by iFrame. }
  move => n K1 K2 f fn1 fn2 vs1 vs2 h1 h2 r rf Hf1 ???? Hcall Hret.
  move: Hf1. rewrite !lookup_insert_Some => ?; destruct!; simplify_map_eq/=.
  destruct vs1, vs2 => //.
  tstep_s. split!; [apply (heap_fresh_is_fresh ∅)|]. move => _.
  tstep_i => ??[??]. simplify_eq. split!.
  tstep_s => ???. simplify_eq.
  tstep_s. set (l := heap_fresh ∅ h2) in *.
  have ? : heap_is_fresh h2 l by apply (heap_fresh_is_fresh ∅). clearbody l.
  apply: Hcall; [done|econs|econs|..].
  { iSatMonoBupd. iIntros!. iFrame.
    iMod (heap_inj_inv_alloc_s _ _ l with "[$]") as "[? ?]"; [done|].
    iMod (heap_inj_inv_update_in_block_s with "[$] [$]") as "[$ ?]"; [done|].
    iModIntro. iAccu. }
  iSatClear.
  move => v1'' v2'' h1'' h2'' rf'' ? /=.
  iSatStart. simplify_eq/=. iIntros!.
  iDestruct (heap_inj_inv_lookup_block_s with "[$] [$]") as %Hl.
  iSatStop.
  tstep_i. tstep_i. split!.
  tstep_s.
  tstep_s => ???. simplify_eq. rewrite h_block_lookup2 Hl /= => ?. simplify_map_eq.
  tstep_s => ?[? [? ?]]. simplify_eq.
  apply Hret; [done|].
  iSatMonoBupd.
  iMod (heap_inj_inv_free_s with "[$] [$]") as "[$ ?]".
  iModIntro. by iFrame.
Qed.


Lemma inj_alloc_ctx_refines :
  rec_ctx_refines (<["f" := inj_alloc_opt]> ∅) (<["f" := inj_alloc]> ∅).
Proof.
  apply: rec_heap_inj_trefines_implies_ctx_refines; [compute_done..|].
  have -> : (fds_init_heap (fd_static_vars <$> <["f":=inj_alloc]> ∅)) = ∅ by compute_done.
  apply inj_alloc_opt_refines.
Qed.
End rec_heap_inj_example.
