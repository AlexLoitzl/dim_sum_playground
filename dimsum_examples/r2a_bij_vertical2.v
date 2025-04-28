From dimsum.examples Require Import rec_to_asm2 rec_heap_inj.
From dimsum.core.iris Require Import weak_embed sat.

Set Default Proof Using "Type".
Open Scope Z_scope.

(** ** Definitions for combining and splitting injections *)
(** abbreviation: r2av: rec_to_asm_vertical *)
(** inj: source (rec) -> impl (asm), injb: source (rec) -> middle (rec), inja: middle (rec) -> impl (asm) *)

(** [r2av_combine inja injb] combines the small injections [inja] and
[injb] into a large injection *)
Definition r2av_combine (inja : gmap prov Z) (injb : gmap prov loc) : gmap prov Z :=
  omap (λ l, (λ ai, ai + l.2) <$> inja !! l.1) injb.

(** [r2av_core_b inja injb] computes the part of [injb] that is also
used by the large injection *)
Definition r2av_core_b (inja : gmap prov Z) (injb : gmap prov loc) : gmap prov loc :=
  filter (λ x, is_Some (inja !! x.2.1)) injb.

(** [r2av_core_b inja injb] computes the part of [inja] that is also
used by the large injection *)
Definition r2av_core_a (inja : gmap prov Z) (injb : gmap prov loc) : gmap prov Z :=
  filter (λ x, x.1 ∈ set_map (D:=gset _) fst (map_img (SA:=gset loc) injb)) inja.

(** [r2av_proj_b inj inja injb X] projects a new b injection [injb'] injection
from the large injection [inj]. It preserves the previous [injb] and
allocates new provenances in the middle from outside [X]. *)
Definition r2av_proj_b (inj inja : gmap prov Z) (injb : gmap prov loc) (X : gset prov) : gmap prov loc :=
  injb ∪ ((λ p, (p, 0%Z)) <$> fresh_map (dom inj) X).

(** [r2av_proj_a inj inja injb X] projects a new a injection [inja'] injection
from the large injection [inj]. It preserves the previous [inja] and
allocates new provenances in the middle from outside [X]. *)
Definition r2av_proj_a (inj inja : gmap prov Z) (injb : gmap prov loc) (X : gset prov) : gmap prov Z :=
  inja ∪ kmap (λ p, fresh_map (dom inj) X !!! p) (inj ∖ gset_to_gmap 0 (dom injb)).

(** [r2av_residual] is what is left in the middle heap after the
small injections are converted to large injection. *)
Definition r2av_residual {Σ} `{!satG Σ heap_injUR} `{!satG Σ rec_to_asmUR} (γa γb : sat_name _) (l : loc) : iProp Σ :=
  ∃ b, ⌜l.2 = 0⌝ ∗ ⌈l.1 ↦∗hi b @ sat γb⌉ ∗ ⌈l.1 ↦∗h b @ sat γa⌉.

(** *** Lookup lemmas *)
Lemma r2av_combine_lookup_Some inja injb ps ai0:
  r2av_combine inja injb !! ps = Some ai0 ↔
   ∃ l ai', injb !! ps = Some l ∧ inja !! l.1 = Some ai' ∧ ai0 = ai' + l.2.
Proof.
  rewrite /r2av_combine lookup_omap_Some. f_equiv => ? /=.
  rewrite fmap_Some. naive_solver.
Qed.

Lemma r2av_core_b_lookup_Some inja injb p l :
  r2av_core_b inja injb !! p = Some l ↔
   injb !! p = Some l ∧ is_Some (inja !! l.1).
Proof. by rewrite /r2av_core_b map_lookup_filter_Some. Qed.

Lemma r2av_core_b_lookup_None inja injb p :
  r2av_core_b inja injb !! p = None ↔
   (∀ l, injb !! p = Some l → inja !! l.1 = None).
Proof.
  rewrite eq_None_not_Some /is_Some.
  setoid_rewrite r2av_core_b_lookup_Some. split.
  2: rewrite /is_Some; naive_solver.
  move => Hl l ?. apply eq_None_not_Some. naive_solver.
Qed.

Lemma r2av_core_a_lookup_Some inja injb p a :
  r2av_core_a inja injb !! p = Some a ↔
   inja !! p = Some a ∧ ∃ ps lm, injb !! ps = Some lm ∧ lm.1 = p.
Proof.
  rewrite /r2av_core_a map_lookup_filter_Some /=.
  rewrite elem_of_map. setoid_rewrite elem_of_map_img.
  naive_solver.
Qed.

Lemma r2av_proj_b_lookup_Some inj inja injb X p (l : loc) :
  r2av_proj_b inj inja injb X !! p = Some l ↔
   injb !! p = Some l ∨ injb !! p = None ∧
     fresh_map (dom inj) X !! p = Some l.1 ∧ l.2 = 0.
Proof.
  rewrite /r2av_proj_b lookup_union_Some_raw. do 2 f_equiv.
  rewrite lookup_fmap_Some. destruct l; naive_solver.
Qed.

Lemma r2av_proj_a_lookup_Some inj inja injb X p a :
  r2av_proj_a inj inja injb X !! p = Some a ↔
   inja !! p = Some a ∨ inja !! p = None ∧
     ∃ ps, inj !! ps = Some a ∧ injb !! ps = None ∧ fresh_map (dom inj) X !! ps = Some p.
Proof.
  rewrite /r2av_proj_a lookup_union_Some_raw. do 2 f_equiv.
  rewrite lookup_kmap_Some_strong. 2: {
    move => i j [?/lookup_difference_Some[??]] [?/lookup_difference_Some[??]].
    rewrite !lookup_total_alt.
    destruct (fresh_map (dom inj) X !! i) eqn:Heq. 2: {
      move: Heq => /fresh_map_lookup_None/not_elem_of_dom. naive_solver. }
    destruct (fresh_map (dom inj) X !! j) eqn:Heq2. 2: {
      move: Heq2 => /fresh_map_lookup_None/not_elem_of_dom. naive_solver. }
    move => ?. simplify_eq/=. apply (fresh_map_bij _ _ _ _ _ Heq Heq2).
  }
  f_equiv => ?. rewrite lookup_difference_Some lookup_gset_to_gmap_None not_elem_of_dom.
  split => -[??]; destruct!; split!; subst.
  - apply lookup_lookup_total. by apply fresh_map_lookup_is_Some, elem_of_dom.
  - by erewrite lookup_total_correct.
Qed.


(** *** Lemmas about the definitions  *)
(** [r2av_combine] is monotonic. *)
Lemma r2av_combine_subseteq inja injb inja' injb':
  inja ⊆ inja' →
  injb ⊆ injb' →
  r2av_combine inja injb ⊆ r2av_combine inja' injb'.
Proof.
  move => Hsuba Hsubb. apply map_subseteq_spec => ??.
  rewrite !r2av_combine_lookup_Some.
  move => [? [? [/(lookup_weaken _ _ _ _)/(_ Hsubb)? [/(lookup_weaken _ _ _ _)/(_ Hsuba) ??]]]].
  naive_solver.
Qed.

(** [r2av_core_a] is smaller than [inja] *)
Lemma r2av_core_a_subseteq inja injb :
  r2av_core_a inja injb ⊆ inja.
Proof. apply map_subseteq_spec => ?? /r2av_core_a_lookup_Some. naive_solver. Qed.

(** [r2av_core_b] is smaller than [inja] *)
Lemma r2av_core_b_subseteq inja injb :
  r2av_core_b inja injb ⊆ injb.
Proof. apply map_subseteq_spec => ?? /r2av_core_b_lookup_Some. naive_solver. Qed.

(** [r2av_proj_a] is bigger than [inja] *)
Lemma r2av_proj_a_subseteq inj inja injb X :
  inja ⊆ r2av_proj_a inj inja injb X.
Proof. apply map_union_subseteq_l. Qed.

(** [r2av_proj_b] is bigger than [injb] *)
Lemma r2av_proj_b_subseteq inj inja injb X :
  injb ⊆ r2av_proj_b inj inja injb X.
Proof. apply map_union_subseteq_l. Qed.

(** We can convert the new large injection [inj] as a combination of
the projections. *)
Lemma r2av_combine_proj inj inja injb X :
  (** inj only grew *)
  r2av_combine inja injb ⊆ inj →
  (** inj does have provs that are already in injb (except for those in the core) *)
  (** We do not need a similar assumption for inja since it is fine to map multiple
    source provs to the same target *)
  dom inj ## dom (injb ∖ r2av_core_b inja injb) →
  (** newly allocated provs must be disjoint from the existing ones in inja and injb *)
  dom inja ⊆ X →
  map_img (fst <$> injb) ⊆ X →
  inj = r2av_combine (r2av_proj_a inj inja injb X) (r2av_proj_b inj inja injb X).
Proof.
  move => Hsub Hdisj HXa HXb.
  apply map_eq => p. apply option_eq => li.
  rewrite r2av_combine_lookup_Some.
  setoid_rewrite r2av_proj_a_lookup_Some.
  setoid_rewrite r2av_proj_b_lookup_Some.
  split => Hp.
  - have : (injb ∖ r2av_core_b inja injb) !! p = None.
    { apply not_elem_of_dom. apply: Hdisj. by apply elem_of_dom. }
    move => /lookup_difference_None[?|[?/r2av_core_b_lookup_Some[?[??]]]].
    + have [??]: is_Some (fresh_map (dom inj) X !! p) by apply fresh_map_lookup_is_Some, elem_of_dom.
      eexists (_, _), _. split!. 2: by rewrite Z.add_0_r. right.
      split! => //. exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      apply eq_None_not_Some => -[?]. contradict Hnotin. apply HXa.
      by apply elem_of_dom.
    + move: Hsub =>/map_subseteq_spec Hsub.
      exploit Hsub. { apply r2av_combine_lookup_Some. naive_solver. }
      naive_solver.
  - destruct!.
    + move: Hsub =>/map_subseteq_spec Hsub. apply Hsub.
      apply r2av_combine_lookup_Some. naive_solver.
    + exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      contradict Hnotin. apply HXa. by apply elem_of_dom.
    + exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      contradict Hnotin. apply HXb, elem_of_map_img. eexists _.
      apply lookup_fmap_Some. naive_solver.
    + have ? : p = ps by apply: fresh_map_bij. rewrite H5 Z.add_0_r. naive_solver.
Qed.

(** The core of a only grows. *)
Lemma r2av_core_a_proj_subseteq inja injb inj X :
  r2av_core_a inja injb ⊆ r2av_core_a (r2av_proj_a inj inja injb X) (r2av_proj_b inj inja injb X).
Proof.
  apply map_subseteq_spec => ?? /r2av_core_a_lookup_Some [? [? [? [??]]]].
  apply r2av_core_a_lookup_Some. split.
  - apply r2av_proj_a_lookup_Some. naive_solver.
  - eexists _, _. split; [|done]. apply r2av_proj_b_lookup_Some. naive_solver.
Qed.


(** The core of b only grows. *)
Lemma r2av_core_b_proj_subseteq inja injb inj X :
  r2av_core_b inja injb ⊆ r2av_core_b (r2av_proj_a inj inja injb X) (r2av_proj_b inj inja injb X).
Proof.
  apply map_subseteq_spec => ?? /r2av_core_b_lookup_Some [? [??]].
  apply r2av_core_b_lookup_Some. split.
  - apply r2av_proj_b_lookup_Some. naive_solver.
  - eexists _. apply r2av_proj_a_lookup_Some. naive_solver.
Qed.


(** This lemma allows us to build the new a injection [inja'] by
replacing the core of [inja]. (Technically, we only need the right to
left inclusion.) *)
Lemma r2av_recombine_a inja injb inja' injb' inj' X :
  inja' = r2av_proj_a inj' inja injb X →
  injb' = r2av_proj_b inj' inja injb X →
  (inja ∖ r2av_core_a inja injb ∪ r2av_core_a inja' injb') = inja'.
Proof.
  move => -> ->.
  apply map_eq => pm. apply option_eq => li.
  rewrite lookup_union_Some_raw lookup_difference_Some lookup_difference_None.
  split.
  - move => [[??]| [? /r2av_core_a_lookup_Some [??]]] //.
    apply: lookup_weaken; [done|]. apply r2av_proj_a_subseteq.
  - move => /r2av_proj_a_lookup_Some[?|[?[?[?[??]]]]].
    + destruct (r2av_core_a inja injb !! pm) eqn:Heq; [|naive_solver]. split!.
      apply: lookup_weaken. 2: apply r2av_core_a_proj_subseteq.
      move: (Heq) => /r2av_core_a_lookup_Some. naive_solver.
    + split!. by left. apply r2av_core_a_lookup_Some. split.
      * apply r2av_proj_a_lookup_Some. naive_solver.
      * eexists _, (_, _). split!. apply r2av_proj_b_lookup_Some. by right.
Qed.

(** This lemma allows us to build the new a injection [injb'] by
replacing the core of [injb]. (Technically, we only need the right to
left inclusion.) *)
Lemma r2av_recombine_b inja injb inja' injb' inj' X :
  inja' = r2av_proj_a inj' inja injb X →
  injb' = r2av_proj_b inj' inja injb X →
  dom inja ⊆ X →
  (injb ∖ r2av_core_b inja injb ∪ r2av_core_b inja' injb') = injb'.
Proof.
  move => -> -> HXa.
  apply map_eq => ps. apply option_eq => lm.
  rewrite lookup_union_Some_raw lookup_difference_Some lookup_difference_None.
  rewrite r2av_core_b_lookup_None r2av_core_b_lookup_Some.
  split.
  - move => [[??]|[?[??]]] //. apply: lookup_weaken; [done|].
    apply r2av_proj_b_subseteq.
  - move => /r2av_proj_b_lookup_Some[?|[?[??]]].
    + destruct (inja !! lm.1) eqn:?.
      * right. split!. { eexists _. apply r2av_core_b_lookup_Some. naive_solver. }
        { apply r2av_proj_b_lookup_Some. naive_solver. }
        eexists _. apply r2av_proj_a_lookup_Some. by left.
      * left. split!. move => ??. unfold loc in *. by simplify_eq.
    + split!. by left.
      * apply r2av_proj_b_lookup_Some. naive_solver.
      * exploit @fresh_map_lookup_Some; [done|].
        move => [/elem_of_dom[??] Hnotin]. eexists _.
        apply r2av_proj_a_lookup_Some. right. split! => //.
        apply eq_None_not_Some => -[?]. contradict Hnotin. apply HXa.
        by apply elem_of_dom.
Qed.

(** [r2av_combine_to_b] allows us to express [r2av_combine] in terms of [r2av_core_b]. *)
Lemma r2av_combine_to_b inja injb :
  r2av_combine inja injb = (λ l, inja !!! l.1 + l.2) <$> r2av_core_b inja injb.
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite r2av_combine_lookup_Some.
  rewrite lookup_fmap_Some. setoid_rewrite r2av_core_b_lookup_Some.
  rewrite /is_Some. split => ?; destruct!/=; split!.
  - by erewrite lookup_total_correct.
  - by erewrite lookup_total_correct.
Qed.

(** provs in the new core that are not in the old core are fresh *)
Lemma r2av_core_b_proj_fresh inj inja injb X p (l : loc):
  map_img (fst <$> injb) ⊆ X →
  (r2av_core_b (r2av_proj_a inj inja injb X) (r2av_proj_b inj inja injb X) ∖
     r2av_core_b inja injb) !! p = Some l →
  fresh_map (dom inj) X !! p = Some l.1 ∧ l.2 = 0.
Proof.
  move => HXb /lookup_difference_Some[/r2av_core_b_lookup_Some[/r2av_proj_b_lookup_Some Horb [? /r2av_proj_a_lookup_Some Hora]] /r2av_core_b_lookup_None?].
  destruct Horb as [|[?[??]]]; [|done].
  destruct Hora as [|[? [?[? [??]]]]]; [naive_solver|].
  exploit @fresh_map_lookup_Some; [done|]. move => [? Hnotin]. contradict Hnotin. apply HXb. apply elem_of_map_img.
  setoid_rewrite lookup_fmap_Some. naive_solver.
Qed.

Section vertical.
Context {Σ} `{!satG Σ heap_injUR} `{!satG Σ rec_to_asmUR}.

(** Combine the value relation. *)
Lemma r2av_combine_val inja' injb' γa γb γ vi vm vs:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈r2a_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ r2av_combine inja' injb', r2a_shared ps li0 @ sat γ⌉ -∗
  ⌈r2a_val_rel vm vi @ sat γa⌉ -∗
  ⌈val_in_inj vm vs @ sat γb⌉ -∗
  ⌈r2a_val_rel vs vi @ sat γ⌉.
Proof.
  iIntros "Ht Ha Hb H Hva Hvb".
  iDestruct (r2a_f2i_trader_switch with "Ht") as "Ht".
  destruct vm, vs => /=; rewrite ?weak_embed_pure //; iDestruct! => //.
  - iApply (r2a_f2i_trade_incl with "[$] [$]").
  - iDestruct "Hva" as (??) "Hla".
    iDestruct "Hvb" as (??) "Hlb". subst => /=.
    iDestruct (r2a_shared_lookup with "Ha [$]") as %?.
    iDestruct (heap_inj_shared_lookup with "Hb [$]") as %?.
    rewrite weak_embed_big_sepM.
    iDestruct (big_sepM_lookup with "[$]") as "?".
    { apply r2av_combine_lookup_Some. by split!. }
    rewrite /loc_in_inj weak_embed_exist.
    iExists _. iFrame. by rewrite Z.add_assoc.
Qed.

Lemma r2av_combine_val_list inja' injb' γa γb γ vi vm vs:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈r2a_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ r2av_combine inja' injb', r2a_shared ps li0 @ sat γ⌉ -∗
  ⌈[∗ list] v1;v2∈vm;vi, r2a_val_rel v1 v2 @ sat γa⌉ -∗
  ⌈[∗ list] v1;v2∈vm;vs, val_in_inj v1 v2 @ sat γb⌉ -∗
  ⌈[∗ list] v1;v2∈vs;vi, r2a_val_rel v1 v2 @ sat γ⌉.
Proof.
  iIntros "#? Haa Hab ? Him Hms".
  iInduction vm as [|] "IH" forall (vi vs). {
    iDestruct (big_sepL2_nil_inv_l (PROP:=uPred rec_to_asmUR) with "Him") as %->.
    iDestruct (big_sepL2_nil_inv_l (PROP:=uPred heap_injUR) with "Hms") as %->.
    simpl. by iPureIntro.
  }
  iDestruct (big_sepL2_cons_inv_l (PROP:=uPred heap_injUR) with "Hms") as (?? ->) "[??]".
  iDestruct (big_sepL2_cons_inv_l (PROP:=uPred rec_to_asmUR) with "Him") as (?? ->) "[??]".
  simpl.
  iDestruct (r2av_combine_val with "[$] Haa Hab [$] [$] [$]") as "#?".
  iSplit; [done|]. iApply ("IH" with "[$] [$] [$] [$] [$]").
Qed.

Lemma r2av_combine_val_map `{Countable K} inja' injb' γa γb γ (vi vm vs : gmap K _):
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈r2a_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ r2av_combine inja' injb', r2a_shared ps li0 @ sat γ⌉ -∗
  ⌈[∗ map] v1;v2∈vi;vm, r2a_val_rel v2 v1 @ sat γa⌉ -∗
  ⌈[∗ map] v1;v2∈vm;vs, val_in_inj v1 v2 @ sat γb⌉ -∗
  ⌈[∗ map] v1;v2∈vi;vs, r2a_val_rel v2 v1 @ sat γ⌉.
Proof.
  iIntros "#? Haa Hab ? Him Hms".
  iInduction vm as [|] "IH" using map_ind forall (vi vs). {
    iDestruct (big_sepM2_empty_l (PROP:=uPred rec_to_asmUR) with "Him") as %->.
    iDestruct (big_sepM2_empty_r (PROP:=uPred heap_injUR) with "Hms") as %->.
    by rewrite big_sepM2_empty.
  }
  iDestruct (big_sepM2_delete_l (PROP:=uPred heap_injUR) with "Hms") as (??) "[??]".
  { apply lookup_insert. }
  iDestruct (big_sepM2_delete_r (PROP:=uPred rec_to_asmUR) with "Him") as (??) "[??]".
  { apply lookup_insert. }
  rewrite delete_insert //.
  iDestruct (r2av_combine_val with "[$] Haa Hab [$] [$] [$]") as "#?".
  erewrite <-(insert_delete vi) at 2; [|done].
  erewrite <-(insert_delete vs) at 2; [|done].
  rewrite big_sepM2_insert; simplify_map_eq => //.
  iSplit; [done|]. iApply ("IH" with "[$] [$] [$] [$] [$]").
Qed.

(** Split the value relation. *)
Lemma r2av_split_val inja' injb' γa γb γ vi vs:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈[∗ map] ps↦li0 ∈ inja', r2a_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈r2a_shared_auth (r2av_combine inja' injb') @ sat γ⌉ -∗

  ⌈r2a_val_rel vs vi @ sat γ⌉ -∗
  ∃ vm, ⌈r2a_val_rel vm vi @ sat γa⌉ ∗ ⌈val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "? Ha Hb H Hv".
  destruct vs => /=; rewrite ?weak_embed_pure //; iDestruct!.
  - iExists (ValNum _) => /=. by iPureIntro.
  - iExists (ValBool _) => /=. by iPureIntro.
  - iExists (ValFn _) => /=. iSplit; [|done]. iApply (r2a_f2i_trade_incl with "[$] [$]").
  - iDestruct "Hv" as (li ?) "Hl".
    iDestruct (r2a_shared_lookup with "H [$]") as %[lm[li'[?[??]]]]%r2av_combine_lookup_Some.
    iDestruct (big_sepM_lookup (PROP:=uPred rec_to_asmUR) with "Ha") as "?"; [done|].
    iDestruct (big_sepM_lookup (PROP:=uPred heap_injUR) with "Hb") as "?"; [done|].
    subst. iExists (ValLoc (lm +ₗ l.2)) => /=. iFrame. iSplit; [|done].
    unfold loc_in_inj. simpl. iFrame. by rewrite Z.add_assoc.
Qed.

Lemma r2av_split_val_list inja' injb' γa γb γ vis vss:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈[∗ map] ps↦li0 ∈ inja', r2a_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈r2a_shared_auth (r2av_combine inja' injb') @ sat γ⌉ -∗

  ⌈[∗ list] vi;vs∈vss;vis, r2a_val_rel vi vs @ sat γ⌉ -∗
  ∃ vms, ⌈[∗ list] vi;vm∈vms;vis, r2a_val_rel vi vm @ sat γa⌉ ∗
         ⌈[∗ list] vm;vs∈vms;vss, val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "#? Ha Hb H Hv".
  iInduction vis as [|] "IH" forall (vss). {
    iDestruct (big_sepL2_nil_inv_r (PROP:=uPred rec_to_asmUR) with "Hv") as %->.
    iExists []. by simpl.
  }
  iDestruct (big_sepL2_cons_inv_r (PROP:=uPred rec_to_asmUR) with "Hv") as (?? ->) "[??]".
  iDestruct (r2av_split_val with "[$] Ha Hb [$] [$]") as (?) "#[??]".
  iDestruct ("IH" with "Ha Hb [$] [$]") as (?) "#[??]".
  iExists (_::_) => /=. by repeat iSplit.
Qed.

Lemma r2av_split_val_map {A} `{Countable A} inja' injb' γa γb γ (vis vss : gmap A _):
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈[∗ map] ps↦li0 ∈ inja', r2a_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈r2a_shared_auth (r2av_combine inja' injb') @ sat γ⌉ -∗

  ⌈[∗ map] vi;vs∈vis;vss, r2a_val_rel vs vi @ sat γ⌉ -∗
  ∃ vms, ⌈[∗ map] vi;vm∈vis;vms, r2a_val_rel vm vi @ sat γa⌉ ∗
         ⌈[∗ map] vm;vs∈vms;vss, val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "#? Ha Hb H Hv".
  iInduction vis as [|] "IH" using map_ind forall (vss). {
    iDestruct (big_sepM2_empty_r (PROP:=uPred rec_to_asmUR) with "Hv") as %->.
    iExists ∅. by rewrite !big_sepM2_empty.
  }
  iDestruct (big_sepM2_delete_l (PROP:=uPred rec_to_asmUR) with "Hv") as (??) "[??]".
  { apply lookup_insert. }
  rewrite delete_insert //.
  iDestruct (r2av_split_val with "[$] Ha Hb [$] [$]") as (?) "#[? ?]".
  iEval (erewrite <-(insert_delete vss); [|done]).
  iDestruct ("IH" with "[$] [$] [$] [$]") as (vms) "[??]".
  iExists (<[_:=_]>vms). iSplit.
  - by iApply (big_sepM2_insert_2 (PROP:=uPred rec_to_asmUR)); [done|].
  - by iApply (big_sepM2_insert_2 (PROP:=uPred heap_injUR)); [done|].
Qed.

(** Allocate the residual for the new provs in the middle heap. *)
Lemma r2av_alloc_residual (m : gmap prov loc) hm γa γb:
  map_img (fst <$> m) ## h_provs hm →
  (∀ i j k, (fst <$> m) !! i = Some k → (fst <$> m) !! j = Some k → i = j) →
  (∀ i k, m !! i = Some k → k.2 = 0%Z) →
  (filter is_ProvStatic (map_img (SA:=gset _) (fst <$> m)) = ∅) →
  ⌈{sat γa}⌉ -∗ ⌈{sat (M:=heap_injUR) γb}⌉ -∗
  ⌈r2a_heapUR_inv hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ ==∗
  ∃ hm', ([∗ map] li0 ∈ m, r2av_residual γa γb li0) ∗
  ⌈{sat γa}⌉ ∗ ⌈{sat γb}⌉ ∗
  ⌈r2a_heapUR_inv hm' @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm' @ sat γb⌉ ∗
  ⌜h_static_provs hm' = h_static_provs hm⌝.
Proof.
  iIntros (? Hinj Hm0 Hs) "?? Hinva Hinvb".

  set bs : gmap prov (gmap Z val) := gset_to_gmap ∅ (map_img (fst <$> m)).
  have ? : dom bs ## h_provs hm by rewrite dom_gset_to_gmap.

  iApply (weak_embed_bupd_intro (sat γa) with "[$]").
  iMod (heapUR_alloc_blocks r2a_heap bs with "Hinva") as "[? Ha]" => //.
  iIntros "!> ?".
  iApply (weak_embed_bupd_intro (sat γb) with "[$]").
  iMod (heapUR_alloc_blocks own_heap_i bs with "Hinvb") as "[? Hb]" => //.
  iIntros "!> ? !>". iFrame. iSplit. 2: {
    iPureIntro. rewrite h_static_provs_heap_merge h_static_provs_heap_from_blocks.
    rewrite dom_gset_to_gmap Hs. set_solver.
  }
  rewrite !big_sepM_gset_to_gmap !big_sepS_map_img_1 // !big_sepM_fmap.
  rewrite !weak_embed_big_sepM.
  iDestruct (big_sepM_sep_2 with "Ha Hb") as "?".
  iApply (big_sepM_impl with "[$]"). iIntros "!>" (???) "[??]". iExists _. iFrame.
  iPureIntro. by apply: Hm0.
Qed.

(** This lemma allows us to integrate the [big_sepM] over
[r2av_core_a] into the [big_sepM] for [r2av_core_b]. This is useful
since then we only need to do an induction over [r2av_core_b].
However, this only holds if [r2av_core_b] is an injection, i.e. it
maps different source provenances to different provenances in the
middle heap. (Otherwise, we would need to reuse the same [Φa l.1 li]
for multiple elements of [r2av_core_b]./) *)
Lemma big_sepM_r2av_core_a_b_1 {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP} `{!BiPureForall PROP}:
  (** Check that r2av_core_b is injective *)
  (∀ p1 p2 l1 l2, ⌜l1.1 = l2.1⌝ -∗ Φb p1 l1 -∗ Φb p2 l2 -∗ False) -∗
  ([∗ map] p↦l ∈ r2av_core_a inja injb, Φa p l) -∗
  ([∗ map] p↦l ∈ r2av_core_b inja injb, Φb p l) -∗
  ([∗ map] p↦l ∈ r2av_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜r2av_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li).
Proof.
  iIntros "Hf ? Hb".
  iAssert ⌜∀ p1 p2 l1 l2, l1.1 = l2.1 → r2av_core_b inja injb !! p1 = Some l1 → r2av_core_b inja injb !! p2 = Some l2 → p1 = p2⌝%I as %Himpl. {
    iIntros (p1 p2 l1 l2 ? ??). destruct (decide (p1 = p2)) => //.
    rewrite (big_sepM_delete _ (r2av_core_b _ _)); [|done]. iDestruct "Hb" as "[? Hb]".
    iDestruct (big_sepM_lookup with "Hb") as "?". { apply lookup_delete_Some. naive_solver. }
    iDestruct ("Hf" with "[//] [$] [$]") as %[].
  }
  iApply big_sepM_sep. iFrame.
  iApply (big_sepM_impl_rel (λ pa la pb lb, pa = lb.1) with "[$]").
  move => ?? /r2av_core_b_lookup_Some[?[??]].
  split!.
  - apply r2av_core_a_lookup_Some. naive_solver.
  - iIntros "$". iPureIntro. apply r2av_core_a_lookup_Some. naive_solver.
  - move => ????. apply: Himpl; [done| |done]. apply r2av_core_b_lookup_Some. naive_solver.
Qed.

Lemma big_sepM_r2av_core_a_b_2 {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP}:
  ([∗ map] p↦l ∈ r2av_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜r2av_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li) ⊢
  ([∗ map] p↦l ∈ r2av_core_a inja injb, Φa p l) ∗
  ([∗ map] p↦l ∈ r2av_core_b inja injb, Φb p l).
Proof.
  iIntros "Hb".
  iDestruct (big_sepM_sep with "Hb") as "[$ ?]".
  iApply (big_sepM_impl_rel (λ pb lb pa la, pa = lb.1) with "[$]").
  move => ?? /r2av_core_a_lookup_Some[?[? [? [??]]]].
  split!.
  - done.
  - apply r2av_core_b_lookup_Some. naive_solver.
  - iIntros "(%& %Ha & ?)". move: Ha => /r2av_core_a_lookup_Some[?[?[?[??]]]]. by simplify_eq.
  - naive_solver.
Qed.

Lemma big_sepM_r2av_core_a_b {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP} `{!BiPureForall PROP}:
  (∀ p1 p2 l1 l2, l1.1 = l2.1 → Φb p1 l1 -∗ Φb p2 l2 -∗ False) →
  ([∗ map] p↦l ∈ r2av_core_a inja injb, Φa p l) ∗
  ([∗ map] p↦l ∈ r2av_core_b inja injb, Φb p l) ⊣⊢
  ([∗ map] p↦l ∈ r2av_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜r2av_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li).
Proof.
  move => Hf. iSplit.
  - iIntros "[??]". iApply (big_sepM_r2av_core_a_b_1 with "[] [$] [$]"). iIntros. by iApply (Hf with "[$] [$]").
  - iIntros "?". by iApply big_sepM_r2av_core_a_b_2.
Qed.

(** Create the large invariant and the residual from the two small invariants. *)
Lemma r2av_shared_from_ab inja' injb' γa γb γ ha hb hm:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  memUR_trader (sat γ) (sat γa) r2a_mem r2a_mem -∗
  heapUR_trader (sat γ) (sat γb) r2a_heap own_heap_s -∗
  ⌈r2a_memUR_inv ha @ sat γa⌉ -∗
  ⌈r2a_heapUR_inv hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ -∗
  ⌈heap_inj_inv_s hb @ sat γb⌉ -∗
  ⌈r2a_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ r2av_combine inja' injb', r2a_shared ps li0 @ sat γ⌉ -∗

  (** interesting part starts here *)
  ⌈r2a_in_inj_inv (r2av_core_a inja' injb') [] @ sat γa⌉ -∗
  ⌈heap_in_inj_inv (r2av_core_b inja' injb') [] @ sat γb⌉ ==∗⌈sat γ⌉
  (⌈r2a_in_inj_inv (r2av_combine inja' injb') [] @ sat γ⌉ ∗
  ([∗ map] ps↦li0 ∈ r2av_core_b inja' injb', r2av_residual γa γb li0)) ∗
  (** interesting part ends here *)

  memUR_trader (sat γ) (sat γa) r2a_mem r2a_mem ∗
  heapUR_trader (sat γ) (sat γb) r2a_heap own_heap_s ∗
  ⌈r2a_memUR_inv ha @ sat γa⌉ ∗
  ⌈r2a_heapUR_inv hm @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ ∗
  ⌈heap_inj_inv_s hb @ sat γb⌉ ∗
  ⌈r2a_shared_auth inja' @ sat γa⌉ ∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉.
Proof.
  iIntros "#????????? #? ? ?". rewrite /heap_in_inj_inv /r2a_in_inj_inv.
  have Hempty : ∀ k, k ∈ [] ↔ False by set_solver.
  setoid_rewrite Hempty. setoid_rewrite bi.False_or.
  iEval (rewrite r2av_combine_to_b big_sepM_fmap).
  rewrite (weak_embed_big_sepM _ _ (r2av_core_a _ _)).
  rewrite !(weak_embed_big_sepM _ _ (r2av_core_b _ _)).
  iDestruct (big_sepM_r2av_core_a_b_1 with "[] [$] [$]") as "?".
  { iIntros (???? ->) "(%&%&?&?&?) (%&%&?&?&?)". iDestruct (heapUR_block_excl own_heap_i with "[$] [$]") as %[]. }
  rewrite -big_sepM_sep.
  iMod (big_sepM_impl_weak_bupd_frame with "[$] [] [-]") as "[$ ?]".
  2: iAccu. 2: by iFrame.
  iIntros "!>" (???). iIntros "(Hta & Htb & ? & Hma & Hmb & ? & Hsha & Hshb)".
  iIntros "[(% & % & %Heq0 & ? & ? & Hvb) Ha]".

  iDestruct "Ha" as (?[??]%r2av_core_a_lookup_Some) "(%&%&?&?&Hva)" => //=.
  iMod (heapUR_trade_block with "Htb [$] [$]") as "[? [??]]".
  iMod (memUR_trade_ptsto_big with "Hta [$] [$]") as "[? [??]]".
  iDestruct (heapUR_lookup_block (PROP:=uPred rec_to_asmUR) with "Hma [$]") as %?.
  iDestruct (heapUR_lookup_block (PROP:=uPred heap_injUR) with "Hmb [$]") as %?.
  simplify_eq.
  iDestruct (r2av_combine_val_map with "[$] Hsha Hshb [$] Hva Hvb") as "#?". iFrame.
  iModIntro. erewrite lookup_total_correct => //. rewrite Heq0 Z.add_0_r. iFrame.
  repeat iSplit => //.
Qed.

(** Create the two small invariants from the large invariant and the residual. *)
Lemma r2av_shared_to_ab inja' injb' γa γb γ ha hb hm:
  r2a_f2i_trader (sat γ) (sat γa) -∗
  ⌈{sat γa}⌉ -∗ ⌈{sat γb}⌉ -∗
  memUR_trader (sat γa) (sat γ) r2a_mem r2a_mem -∗
  heapUR_trader (sat γb) (sat γ) own_heap_s r2a_heap -∗
  ⌈r2a_memUR_inv ha @ sat γ⌉ -∗
  ⌈r2a_heapUR_inv hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ -∗
  ⌈r2a_heapUR_inv hb @ sat γ⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ inja', r2a_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈r2a_shared_auth (r2av_combine inja' injb') @ sat γ⌉ -∗

  (** interesting part starts here *)
  ⌈r2a_in_inj_inv (r2av_combine inja' injb') [] @ sat γ⌉ -∗
  ([∗ map] ps↦li0 ∈ r2av_core_b inja' injb', r2av_residual γa γb li0) ==∗
  ∃ hm',
  (⌈r2a_in_inj_inv (r2av_core_a inja' injb') [] @ sat γa⌉ ∗
  ⌈heap_in_inj_inv (r2av_core_b inja' injb') [] @ sat γb⌉) ∗
  (** interesting part ends here *)

  ⌈{sat γa}⌉ ∗ ⌈{sat γb}⌉ ∗
  memUR_trader (sat γa) (sat γ) r2a_mem r2a_mem ∗
  heapUR_trader (sat γb) (sat γ) own_heap_s r2a_heap ∗
  ⌈r2a_memUR_inv ha @ sat γ⌉ ∗
  ⌈r2a_heapUR_inv hm' @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm' @ sat γb⌉ ∗
  ⌈r2a_heapUR_inv hb @ sat γ⌉ ∗
  ⌈r2a_shared_auth (r2av_combine inja' injb') @ sat γ⌉ ∗ ⌜h_static_provs hm' = h_static_provs hm⌝.
Proof.
  iIntros "#?????????#Hsa#Hsb???".
  rewrite /heap_in_inj_inv /r2a_in_inj_inv.
  have Hempty : ∀ k, k ∈ [] ↔ False by set_solver.
  setoid_rewrite Hempty. setoid_rewrite bi.False_or.
  rewrite {2}r2av_combine_to_b big_sepM_fmap.
  setoid_rewrite (weak_embed_big_sepM _ _ (r2av_core_a _ _)).
  setoid_rewrite (weak_embed_big_sepM _ _ (r2av_core_b _ _)).
  setoid_rewrite big_sepM_r2av_core_a_b; try apply _.
  2: { iIntros (???? ->) "(%&%&?&?&?) (%&%&?&?&?)". iDestruct (heapUR_block_excl own_heap_i with "[$] [$]") as %[]. }
  iDestruct (big_sepM_sep with "[$]") as "Hm".
  iApply (big_sepM_impl_bupd_ex_frame with "Hm"). 2: by iFrame.
  iIntros "!>" (???[?[??]]%r2av_core_b_lookup_Some) "(?&?&Hta&Htb&?&Hinva&Hinvb&?&?&<-) [[%[%Heq0[??]]] [% [% [? [??]]]]]".
  erewrite lookup_total_correct => //. rewrite Heq0 Z.add_0_r.
  iDestruct (r2av_split_val_map with "[$] Hsa Hsb [$] [$]") as (bm) "#[? ?]". simpl.

  iApply (weak_embed_bupd_intro (sat γa) with "[$]").
  iDestruct (heapUR_lookup_block_prov r2a_heap with "Hinva [$]") as %?.
  iMod (heapUR_update_block r2a_heap with "Hinva [$]") as "[? ?]".
  iMod (memUR_trade_ptsto_big with "Hta [$] [$]") as "[? [??]]".
  iIntros "!> Hγa".

  iApply (weak_embed_bupd_intro (sat γb) with "[$]").
  iMod (heapUR_update_block own_heap_i with "Hinvb [$]") as "[? ?]".
  iMod (heapUR_trade_block with "Htb [$] [$]") as "[? [??]]".
  iIntros "!> Hγb".

  iModIntro. iFrame. iSplit!; repeat iSplit => //.
  - by rewrite h_static_provs_update_block.
  - apply r2av_core_a_lookup_Some. naive_solver.
  - done.
Qed.
End vertical.

Lemma r2a_bij_vertical m moinit hinit `{!VisNoAng m.(m_trans)} ins f2i :
  trefines (rec_to_asm ins f2i moinit hinit (rec_heap_inj hinit m))
           (rec_to_asm ins f2i moinit hinit m).
Proof.
  unshelve apply: mod_prepost_combine_bi.
  set (Σ := #[satΣ heap_injUR; satΣ rec_to_asmUR]).
  have ? : satG Σ heap_injUR by apply _.
  have ? : satG Σ rec_to_asmUR by apply _.
  clearbody Σ.
  eexists Σ, _, _, _ => γa γb γ.
  unshelve eexists _.  {
    exact (λ pl s1 _ s2,
      ∃ inja injb inj statics, ⌜s1 = s2⌝ ∗ r2a_f2i_trader (sat γ) (sat γa) ∗

        if pl is Env then
          (* We only require the subseteq here since it makes the
          initialization easier. *)
          ⌜r2av_combine inja injb ⊆ inj⌝ ∗ ∃ hm,
          ⌜h_static_provs hm = statics⌝ ∗
          ⌈[∗ map] ps↦li0∈inj, r2a_shared ps li0 @ sat γ⌉ ∗
          ⌈r2a_shared_auth inja @ sat γa⌉ ∗
          ⌈heap_inj_shared_auth injb @ sat γb⌉ ∗
          ⌈r2a_in_inj_inv (inja ∖ r2av_core_a inja injb) [] @ sat γa⌉ ∗
          ⌈heap_in_inj_inv (injb ∖ r2av_core_b inja injb) [] @ sat γb⌉ ∗
          ([∗ map] ps↦li0 ∈ r2av_core_b inja injb, r2av_residual γa γb li0) ∗
          ⌈r2a_heapUR_inv hm @ sat γa⌉ ∗
          ⌈heapUR_inv own_heap_i hm @ sat γb⌉ ∗
          memUR_trader (sat γa) (sat γ) r2a_mem r2a_mem ∗
          heapUR_trader (sat γb) (sat γ) own_heap_s r2a_heap ∗
          (* This proof could be quite a bit simpler without the
          requirement that the statics stay the same. (It is not used
          in this proof.) *)
          ⌈r2a_statics statics @ sat γa⌉ ∗
          ⌈heap_inj_statics statics @ sat γb⌉ ∗
          ⌈r2a_statics statics @ sat γ⌉
        else
          ⌜inj = r2av_combine inja injb⌝ ∗
          ⌈[∗ map] ps↦li0∈inja, r2a_shared ps li0 @ sat γa⌉ ∗
          ⌈[∗ map] ps↦li0∈injb, heap_inj_shared ps li0 @ sat γb⌉ ∗
          ⌈r2a_shared_auth inj @ sat γ⌉ ∗
          memUR_trader (sat γ) (sat γa) r2a_mem r2a_mem ∗
          heapUR_trader (sat γ) (sat γb) r2a_heap own_heap_s ∗
          ⌈r2a_statics statics @ sat γa⌉ ∗
          ⌈heap_inj_statics statics @ sat γb⌉ ∗
          ⌈r2a_statics statics @ sat γ⌉
          )%I. }
  split_and!.
  - move => /= [? []]//= regs mem b ? h ???. apply pp_to_all_forall => ? r Hppex.
    iIntros "([Hiniti [Hinits Hf2i]] & (?&[Hinv[? #?]]&?) & ?)".
    iDestruct (r2a_f2i_incl_to_full with "Hf2i") as (f2i_full) "[%Hent #Hf2i_full]".
    iDestruct (heapUR_lookup_block_big r2a_heap with "Hinv Hinits") as %Hblocks.
    set staticbs : gmap prov (gmap Z val) :=
            gset_to_gmap ∅ (h_static_provs h) ∖ hinit.
    iExists _, _. iSplit!. {
      apply: satisfiable_bmono; [eapply (r2a_res_init' _ f2i_full)|].
      iIntros "(Hinvm & Hinvh & ? & ? & ?)".
      iMod (memUR_alloc_big with "Hinvm") as "[Hinvm $]". { apply map_disjoint_empty_r. }
      iMod (heapUR_alloc_blocks _ (hinit ∪ staticbs) with "Hinvh") as "[Hinvh Hbs]"; [set_solver|].
      iDestruct (big_sepM_union with "Hbs") as "[$ ?]";
        [apply map_disjoint_difference_r'|].
      rewrite !right_id. iModIntro. iSplit; [iAccu|]. by iApply Hent.
    } {
      apply: satisfiable_bmono; [apply heap_inj_init|].
      iIntros "(? & ? & Hinvi & Hinvs)".
      iMod (heapUR_alloc_blocks _ (hinit ∪ staticbs) with "Hinvi") as "[Hinvi Hbs]"; [set_solver|].
      iMod (heapUR_alloc_blocks with "Hinvs") as "[Hinvs $]"; [set_solver|].
      iDestruct (big_sepM_union with "Hbs") as "[$ ?]";
        [apply map_disjoint_difference_r'|].
      rewrite !right_id. iModIntro. iAccu.
    }
    iIntros "Hγa Hγb Hγ (?&?&?&Hinvi&?&?) (?&?&?&?&?)".
    iModIntro. iFrame "#∗". iFrame "#".
    iExists ∅. rewrite /heap_in_inj_inv /r2a_in_inj_inv !big_sepM_empty. iSplit!.
    { iApply (r2a_f2i_trader_init with "Hf2i_full [$]"). } {
      rewrite h_static_provs_heap_from_blocks dom_union_L dom_difference_L.
      rewrite (comm (R:=(=)) (∪)) difference_union_L.
      rewrite dom_gset_to_gmap filter_union_L (comm (R:=(=)) (∪)).
      rewrite subseteq_union_1_L; [set_solver|].
      rewrite map_subseteq_spec in Hblocks.
      move => ? /elem_of_filter[?/elem_of_dom[? /Hblocks/h_blocks_lookup_Some[??]]].
      apply elem_of_filter. split!. by apply elem_of_h_static_provs.
    }
    iSplitL "Hinvi Hiniti".
    + iApply (memUR_trader_init with "[$] [$]").
    + iApply (heapUR_trader_init_blocks with "[$] [$]").
  - move => /= ??? [? []//=] ?? b ? h ???. apply pp_to_all_forall => ? r Hppex.
    iIntros "??? [[[? Hinvm] [Hinvh ?]] ?] (%inja & %injb & %inj & %statics & % & #? & % & %  & % & ? & Hsha & Hshb & Hinja & Hs)". simplify_eq.
    iDestruct (big_sepL2_length (PROP:=uPred rec_to_asmUR) with "[$]") as %?.
    iDestruct "Hs" as "(Hinjb & Hbs & ? & ? & Hta & Htb & #Hsa & #Hsb & #Hs)".
    iDestruct "Hinvh" as "(Hinvh & [%inj' [Hsh Hinj]] & Hs1)".
    iDestruct (r2a_statics_agree with "Hs Hs1") as %Heq.
    iDestruct (r2a_shared_lookup_big with "Hsh [$]") as %?.

    iAssert ⌜dom inj' ## dom (injb ∖ r2av_core_b inja injb)⌝%I as %?. {
      rewrite elem_of_disjoint.
      iIntros (?[??]%elem_of_dom[??]%elem_of_dom).
      iDestruct (r2a_in_inj_inv_borrow with "Hinj") as (??) "(?&Hp&?&?)"; [apply not_elem_of_nil|done|].
      iDestruct (heap_in_inj_inv_borrow with "Hinjb") as (???) "(?&?&?&?)"; [apply not_elem_of_nil|done|].
      iApply bupd_plainly.
      iApply (weak_embed_bupd_intro (sat γb) with "[$]").
      iMod (heapUR_trade_block with "[$] [$] Hp") as "[? [??]]".
      iDestruct (heapUR_block_excl own_heap_s with "[$] [$]") as %[].
    }

    (* Technically, h_provs hm should suffice, but it would require more proofs. *)
    set (X := (dom inja ∪ map_img (fst <$> injb) ∪ h_provs hm)).
    set (inja' := (r2av_proj_a inj' inja injb X)).
    set (injb' := (r2av_proj_b inj' inja injb X)).

    have -> : inj' = r2av_combine inja' injb' by
      apply r2av_combine_proj; [by etrans |done|set_solver..].

    (** Update the small injections  *)
    iApply (weak_embed_bupd_intro (sat γb) with "[$]").
    iMod (heap_inj_shared_alloc_big _ injb' with "Hshb") as "[? #Hshbbig]".
    { apply r2av_proj_b_subseteq. }
    iIntros "!> Hγb".

    iApply (weak_embed_bupd_intro (sat γa) with "[$]").
    iMod (r2a_shared_alloc_big _ inja' with "Hsha") as "[? #Hshabig]".
    { apply r2av_proj_a_subseteq. }
    iIntros "!> Hγa".

    (** Update the residual *)
    iMod (r2av_alloc_residual (r2av_core_b inja' injb' ∖ r2av_core_b inja injb) with "[$] [$] [$] [$]") as (hm') "[Hbs' [Hγa [Hγb[?[?%Heqm]]]]]". {
      move => ? /elem_of_map_img[? /lookup_fmap_Some[? [? ]]]. subst.
      move => /r2av_core_b_proj_fresh[|/(fresh_map_lookup_Some _ _ _ _)]; set_solver.
    } {
      move => ??? /lookup_fmap_Some[[??][? /r2av_core_b_proj_fresh[|??]]]. 1: set_solver.
      move => /lookup_fmap_Some[[??][? /r2av_core_b_proj_fresh[|??]]]. 1: set_solver. simplify_eq/=.
      by apply: fresh_map_bij.
    } { move => ?? /r2av_core_b_proj_fresh[|//]. set_solver. } {
      apply equiv_empty_L. move => ? /elem_of_filter[? /elem_of_map_img[? /lookup_fmap_Some[l [? ]]]]. subst.
      move => /r2av_core_b_proj_fresh[//|/fresh_map_is_Block]. 1: set_solver. by destruct l.1.
    }
    iDestruct (big_sepM_union_2 with "Hbs Hbs'") as "Hbs".
    rewrite map_difference_union. 2: { apply r2av_core_b_proj_subseteq. }

    (** Create the small [heap_in_inj_inv]. *)
    iMod (r2av_shared_to_ab with "[$] Hγa Hγb Hta Htb [$] [$] [$] [$] [$] [$] [$] [$] [$]") as (?) "([??] & ? & ? & ? & ? & ? & ? & ? & ? & ? & %Heqm')".

    iDestruct (r2a_in_inj_inv_combine with "Hinja [$]") as "Hinja".
    iDestruct (heap_in_inj_inv_combine with "Hinjb [$]") as "Hinjb".
    erewrite r2av_recombine_a => //. erewrite r2av_recombine_b => //.
    2: set_solver.

    (** Split the val_in_inj for the arguments. *)
    iDestruct (r2av_split_val_list with "[$] Hshabig Hshbbig [$] [$]") as (vms) "#[Hv1 ?]".
    iDestruct (big_sepL2_length (PROP:=uPred rec_to_asmUR) with "Hv1") as %?.

    (** Transfer the traders *)
    iApply (weak_embed_bupd_intro (sat γb) with "[$]").
    iMod (heapUR_trader_switch with "[$] [$]") as "[? ?]".
    iIntros "!> ?".
    iApply (weak_embed_bupd_intro (sat γa) with "[$]").
    iMod (r2a_mem_stack_trade with "[$] [$] [$]") as "[? [? ?]]".
    iMod (memUR_trader_switch with "[$] [$]") as "[? ?]".
    iIntros "!> ?". iModIntro.

    (** Finish *)
    iExists b; destruct b; destruct!/=; iFrame.
    (* We need to be careful here to not accidentally instantiate
    evars via the [Persistent] typeclass search of [iSplit] for bigops *)
    all: iSplit; [done|]; iExists vms, _; iFrame "#∗"; iSplit!; rewrite -?Heq ?Heqm' ?Heqm //.
    + iSplit; [|done]. done.
    + rewrite right_id. iApply (r2a_f2i_trade_incl with "[$] [$]").
    + by repeat iSplit.
    + by iSplit.
    + by rewrite {1}(list_to_singleton vms).
    + iSplit; [by iSplit|]. by rewrite {2}(list_to_singleton vms).
    + done.
  - move => /= ??? e ???????. apply pp_to_all_forall => ? r Hppex.
    iIntros "??? [[[? Hinvma] [Hinvha Hva]] Hr] [[Hinvb Hvb] ?] (%inja & %injb & %inj & %statics & % & #? & % & ? & ? & Hsh & Hta & Htb & Hsa & Hsb & #Hs)".
    iDestruct (big_sepL2_length (PROP:=uPred heap_injUR) with "[$]") as %?.
    rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap //.
    iDestruct "Hinvha" as "(Hinvha & [%inja' [Hsha Hinja]] & Hsa1)".
    iDestruct "Hinvb" as "(Hinvib & Hinvsb & [%injb' [Hshb Hinjb]] & Hsb1 & Hsb2)".
    iDestruct (r2a_statics_agree with "Hsa Hsa1") as %?.
    iDestruct (heap_inj_statics_eq with "Hsb1 Hsb2") as %Heq.
    iDestruct (heap_inj_statics_eq with "Hsb Hsb1") as %?.
    iDestruct (r2a_shared_lookup_big with "Hsha [$]") as %?.
    iDestruct (heap_inj_shared_lookup_big with "Hshb [$]") as %?. subst.

    (** Update the large injection *)
    iApply (weak_embed_bupd_intro (sat γ) with "[$]").
    iMod (r2a_shared_alloc_big _ (r2av_combine inja' injb') with "Hsh") as "[? #Hshbig]".
    { subst. by apply r2av_combine_subseteq. }
    iIntros "!> ?".

    (** Split the small invariants *)
    iDestruct (r2a_in_inj_inv_split (r2av_core_a inja' injb') with "Hinja") as "[? Hinja]"; [apply r2av_core_a_subseteq|].
    iDestruct (heap_in_inj_inv_split (r2av_core_b inja' injb') with "Hinjb") as "[? Hinjb]"; [apply r2av_core_b_subseteq|].

    (** Combine the small invariants to get the large invariant. *)
    iApply (weak_embed_bupd_intro (sat γ) with "[$]").
    iMod (r2av_shared_from_ab with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[[??][?[?[? [? [? [? [Hsha Hshb]]]]]]]]".

    (** Combine the val_in_inj for the arguments. *)
    iDestruct (r2av_combine_val_list with "[$] Hsha Hshb [$] [$] [$]") as "#Hvs".

    (** Trade the stack. *)
    iMod (r2a_mem_stack_trade with "[$] [$] [$]") as "[? [? ?]]".

    (** Transfer the traders *)
    iMod (memUR_trader_switch with "[$] [$]") as "[? ?]".
    iMod (heapUR_trader_switch with "[$] [$]") as "[? ?]".
    iIntros "!> ?". iModIntro.

    (** Finish *)
    rewrite Heq. destruct e as [? []]; destruct!/=.
    all: iFrame "#∗".
    all: iSplit! => //.
    + by iSplit.
    + iDestruct "Hr" as "[? _]". iApply (r2a_f2i_trade_incl with "[] [$]"). by iApply r2a_f2i_trader_switch.
    + by iSplit.
Qed.

Lemma r2a_bij_vertical_N m moinit hinit `{!VisNoAng m.(m_trans)} ins f2i n:
  trefines (rec_to_asm ins f2i moinit hinit (rec_heap_inj_N n hinit m))
           (rec_to_asm ins f2i moinit hinit m).
Proof. elim: n => //= ??. etrans; [by apply: r2a_bij_vertical|eauto]. Qed.
