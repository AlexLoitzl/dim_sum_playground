From dimsum.examples Require Import rec_heap_inj.
From dimsum.core.iris Require Import weak_embed sat.

Set Default Proof Using "Type".

(** ** Definitions for combining and splitting injections *)
(** abbreviation: rhiv: rec_heap_inj_vertical *)
(** inj: souce -> impl, injb: source -> middle, inja: middle -> impl *)

(** [rhiv_combine inja injb] combines the small injections [inja] and
[injb] into a large injection *)
Definition rhiv_combine (inja injb : gmap prov loc) : gmap prov loc :=
  omap (λ l, (λ li, li +ₗ l.2) <$> inja !! l.1) injb.

(** [rhiv_core_b inja injb] computes the part of [injb] that is also
used by the large injection *)
Definition rhiv_core_b (inja injb : gmap prov loc) : gmap prov loc :=
  filter (λ x, is_Some (inja !! x.2.1)) injb.

(** [rhiv_core_b inja injb] computes the part of [inja] that is also
used by the large injection *)
Definition rhiv_core_a (inja injb : gmap prov loc) : gmap prov loc :=
  filter (λ x, x.1 ∈ set_map (D:=gset _) fst (map_img (SA:=gset loc) injb)) inja.

(** [rhiv_proj_b inj inja injb X] projects a new b injection [injb'] injection
from the large injection [inj]. It preserves the previous [injb] and
allocates new provenances in the middle from outside [X]. *)
Definition rhiv_proj_b (inj inja injb : gmap prov loc) (X : gset prov) : gmap prov loc :=
  injb ∪ ((λ p, (p, 0%Z)) <$> fresh_map (dom inj) X).

(** [rhiv_proj_a inj inja injb X] projects a new a injection [inja'] injection
from the large injection [inj]. It preserves the previous [inja] and
allocates new provenances in the middle from outside [X]. *)
Definition rhiv_proj_a (inj inja injb : gmap prov loc) (X : gset prov) : gmap prov loc :=
  inja ∪ kmap (λ p, fresh_map (dom inj) X !!! p) (inj ∖ injb).

(** [rhiv_residual] is what is left in the middle heap after the
small injections are converted to large injection. *)
Definition rhiv_residual {Σ} `{!satG Σ heap_injUR} (γa γb : gname) (l : loc) : iProp Σ :=
  ∃ b, ⌜l.2 = 0⌝ ∗ ⌈l.1 ↦∗hi b @ sat γb⌉ ∗ ⌈l.1 ↦∗hs b @ sat γa⌉.

(** *** Lookup lemmas *)
Lemma rhiv_combine_lookup_Some inja injb ps li0:
  rhiv_combine inja injb !! ps = Some li0 ↔
   ∃ l li', injb !! ps = Some l ∧ inja !! l.1 = Some li' ∧ li0 = li' +ₗ l.2.
Proof.
  rewrite /rhiv_combine lookup_omap_Some. f_equiv => ? /=.
  rewrite fmap_Some. naive_solver.
Qed.

Lemma rhiv_core_b_lookup_Some inja injb p l :
  rhiv_core_b inja injb !! p = Some l ↔
   injb !! p = Some l ∧ is_Some (inja !! l.1).
Proof. by rewrite /rhiv_core_b map_lookup_filter_Some. Qed.

Lemma rhiv_core_b_lookup_None inja injb p :
  rhiv_core_b inja injb !! p = None ↔
   (∀ l, injb !! p = Some l → inja !! l.1 = None).
Proof.
  rewrite eq_None_not_Some /is_Some.
  setoid_rewrite rhiv_core_b_lookup_Some. split.
  2: rewrite /is_Some; naive_solver.
  move => Hl l ?. apply eq_None_not_Some. naive_solver.
Qed.

Lemma rhiv_core_a_lookup_Some inja injb p l :
  rhiv_core_a inja injb !! p = Some l ↔
   inja !! p = Some l ∧ ∃ ps lm, injb !! ps = Some lm ∧ lm.1 = p.
Proof.
  rewrite /rhiv_core_a map_lookup_filter_Some /=.
  rewrite elem_of_map. setoid_rewrite elem_of_map_img.
  naive_solver.
Qed.

Lemma rhiv_proj_b_lookup_Some inj inja injb X p (l : loc) :
  rhiv_proj_b inj inja injb X !! p = Some l ↔
   injb !! p = Some l ∨ injb !! p = None ∧
     fresh_map (dom inj) X !! p = Some l.1 ∧ l.2 = 0.
Proof.
  rewrite /rhiv_proj_b lookup_union_Some_raw. do 2 f_equiv.
  rewrite lookup_fmap_Some. destruct l; naive_solver.
Qed.

Lemma rhiv_proj_a_lookup_Some inj inja injb X p (l : loc) :
  rhiv_proj_a inj inja injb X !! p = Some l ↔
   inja !! p = Some l ∨ inja !! p = None ∧
     ∃ ps, inj !! ps = Some l ∧ injb !! ps = None ∧ fresh_map (dom inj) X !! ps = Some p.
Proof.
  rewrite /rhiv_proj_a lookup_union_Some_raw. do 2 f_equiv.
  rewrite lookup_kmap_Some_strong. 2: {
    move => i j [?/lookup_difference_Some[??]] [?/lookup_difference_Some[??]].
    rewrite !lookup_total_alt.
    destruct (fresh_map (dom inj) X !! i) eqn:Heq. 2: {
      move: Heq => /fresh_map_lookup_None/not_elem_of_dom. naive_solver. }
    destruct (fresh_map (dom inj) X !! j) eqn:Heq2. 2: {
      move: Heq2 => /fresh_map_lookup_None/not_elem_of_dom. naive_solver. }
    move => ?. simplify_eq/=. apply (fresh_map_bij _ _ _ _ _ Heq Heq2).
  }
  f_equiv => ?. rewrite lookup_difference_Some.
  split => -[??]; destruct!; split!; subst.
  - apply lookup_lookup_total. by apply fresh_map_lookup_is_Some, elem_of_dom.
  - by erewrite lookup_total_correct.
Qed.


(** *** Lemmas about the definitions  *)
(** [rhiv_combine] is monotonic. *)
Lemma rhiv_combine_subseteq inja injb inja' injb':
  inja ⊆ inja' →
  injb ⊆ injb' →
  rhiv_combine inja injb ⊆ rhiv_combine inja' injb'.
Proof.
  move => Hsuba Hsubb. apply map_subseteq_spec => ??.
  rewrite !rhiv_combine_lookup_Some.
  move => [? [? [/(lookup_weaken _ _ _ _)/(_ Hsubb)? [/(lookup_weaken _ _ _ _)/(_ Hsuba) ??]]]].
  naive_solver.
Qed.

(** [rhiv_core_a] is smaller than [inja] *)
Lemma rhiv_core_a_subseteq inja injb :
  rhiv_core_a inja injb ⊆ inja.
Proof. apply map_subseteq_spec => ?? /rhiv_core_a_lookup_Some. naive_solver. Qed.

(** [rhiv_core_b] is smaller than [inja] *)
Lemma rhiv_core_b_subseteq inja injb :
  rhiv_core_b inja injb ⊆ injb.
Proof. apply map_subseteq_spec => ?? /rhiv_core_b_lookup_Some. naive_solver. Qed.

(** [rhiv_proj_a] is bigger than [inja] *)
Lemma rhiv_proj_a_subseteq inj inja injb X :
  inja ⊆ rhiv_proj_a inj inja injb X.
Proof. apply map_union_subseteq_l. Qed.

(** [rhiv_proj_b] is bigger than [injb] *)
Lemma rhiv_proj_b_subseteq inj inja injb X :
  injb ⊆ rhiv_proj_b inj inja injb X.
Proof. apply map_union_subseteq_l. Qed.

(** We can convert the new large injection [inj] as a combination of
the projections. *)
Lemma rhiv_combine_proj inj inja injb X :
  (** inj only grew *)
  rhiv_combine inja injb ⊆ inj →
  (** inj does have provs that are already in injb (except for those in the core) *)
  (** We do not need a similar assumption for inja since it is fine to map multiple
    source provs to the same target *)
  inj ##ₘ injb ∖ rhiv_core_b inja injb →
  (** newly allocated provs must be disjoint from the existing ones in inja and injb *)
  dom inja ⊆ X →
  map_img (fst <$> injb) ⊆ X →
  inj = rhiv_combine (rhiv_proj_a inj inja injb X) (rhiv_proj_b inj inja injb X).
Proof.
  move => Hsub Hdisj HXa HXb.
  apply map_eq => p. apply option_eq => li.
  rewrite rhiv_combine_lookup_Some.
  setoid_rewrite rhiv_proj_a_lookup_Some.
  setoid_rewrite rhiv_proj_b_lookup_Some.
  split => ?.
  - exploit @map_disjoint_Some_l; [done..|].
    move => /lookup_difference_None[?|[?/rhiv_core_b_lookup_Some[?[??]]]].
    + have [??]: is_Some (fresh_map (dom inj) X !! p) by apply fresh_map_lookup_is_Some, elem_of_dom.
      eexists (_, _), _. split!. 2: by rewrite offset_loc_0. right.
      split! => //. exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      apply eq_None_not_Some => -[?]. contradict Hnotin. apply HXa.
      by apply elem_of_dom.
    + move: Hsub =>/map_subseteq_spec Hsub.
      exploit Hsub. { apply rhiv_combine_lookup_Some. naive_solver. }
      naive_solver.
  - destruct!.
    + move: Hsub =>/map_subseteq_spec Hsub. apply Hsub.
      apply rhiv_combine_lookup_Some. naive_solver.
    + exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      contradict Hnotin. apply HXa. by apply elem_of_dom.
    + exploit @fresh_map_lookup_Some; [done|]. move => [_ Hnotin].
      contradict Hnotin. apply HXb, elem_of_map_img. eexists _.
      apply lookup_fmap_Some. naive_solver.
    + have ? : p = ps by apply: fresh_map_bij. rewrite H5 offset_loc_0. naive_solver.
Qed.

(** The core of a only grows. *)
Lemma rhiv_core_a_proj_subseteq inja injb inj X :
  rhiv_core_a inja injb ⊆ rhiv_core_a (rhiv_proj_a inj inja injb X) (rhiv_proj_b inj inja injb X).
Proof.
  apply map_subseteq_spec => ?? /rhiv_core_a_lookup_Some [? [? [? [??]]]].
  apply rhiv_core_a_lookup_Some. split.
  - apply rhiv_proj_a_lookup_Some. naive_solver.
  - eexists _, _. split; [|done]. apply rhiv_proj_b_lookup_Some. naive_solver.
Qed.


(** The core of b only grows. *)
Lemma rhiv_core_b_proj_subseteq inja injb inj X :
  rhiv_core_b inja injb ⊆ rhiv_core_b (rhiv_proj_a inj inja injb X) (rhiv_proj_b inj inja injb X).
Proof.
  apply map_subseteq_spec => ?? /rhiv_core_b_lookup_Some [? [??]].
  apply rhiv_core_b_lookup_Some. split.
  - apply rhiv_proj_b_lookup_Some. naive_solver.
  - eexists _. apply rhiv_proj_a_lookup_Some. naive_solver.
Qed.


(** This lemma allows us to build the new a injection [inja'] by
replacing the core of [inja]. (Technically, we only need the right to
left inclusion.) *)
Lemma rhiv_recombine_a inja injb inja' injb' inj' X :
  inja' = rhiv_proj_a inj' inja injb X →
  injb' = rhiv_proj_b inj' inja injb X →
  (inja ∖ rhiv_core_a inja injb ∪ rhiv_core_a inja' injb') = inja'.
Proof.
  move => -> ->.
  apply map_eq => pm. apply option_eq => li.
  rewrite lookup_union_Some_raw lookup_difference_Some lookup_difference_None.
  split.
  - move => [[??]| [? /rhiv_core_a_lookup_Some [??]]] //.
    apply: lookup_weaken; [done|]. apply rhiv_proj_a_subseteq.
  - move => /rhiv_proj_a_lookup_Some[?|[?[?[?[??]]]]].
    + destruct (rhiv_core_a inja injb !! pm) eqn:Heq; [|naive_solver]. split!.
      apply: lookup_weaken. 2: apply rhiv_core_a_proj_subseteq.
      move: (Heq) => /rhiv_core_a_lookup_Some. naive_solver.
    + split!. by left. apply rhiv_core_a_lookup_Some. split.
      * apply rhiv_proj_a_lookup_Some. naive_solver.
      * eexists _, (_, _). split!. apply rhiv_proj_b_lookup_Some. by right.
Qed.

(** This lemma allows us to build the new a injection [injb'] by
replacing the core of [injb]. (Technically, we only need the right to
left inclusion.) *)
Lemma rhiv_recombine_b inja injb inja' injb' inj' X :
  inja' = rhiv_proj_a inj' inja injb X →
  injb' = rhiv_proj_b inj' inja injb X →
  dom inja ⊆ X →
  (injb ∖ rhiv_core_b inja injb ∪ rhiv_core_b inja' injb') = injb'.
Proof.
  move => -> -> HXa.
  apply map_eq => ps. apply option_eq => lm.
  rewrite lookup_union_Some_raw lookup_difference_Some lookup_difference_None.
  rewrite rhiv_core_b_lookup_None rhiv_core_b_lookup_Some.
  split.
  - move => [[??]|[?[??]]] //. apply: lookup_weaken; [done|].
    apply rhiv_proj_b_subseteq.
  - move => /rhiv_proj_b_lookup_Some[?|[?[??]]].
    + destruct (inja !! lm.1) eqn:?.
      * right. split!. { eexists _. apply rhiv_core_b_lookup_Some. naive_solver. }
        { apply rhiv_proj_b_lookup_Some. naive_solver. }
        eexists _. apply rhiv_proj_a_lookup_Some. by left.
      * left. split!. move => ??. unfold loc in *. by simplify_eq.
    + split!. by left.
      * apply rhiv_proj_b_lookup_Some. naive_solver.
      * exploit @fresh_map_lookup_Some; [done|].
        move => [/elem_of_dom[??] Hnotin]. eexists _.
        apply rhiv_proj_a_lookup_Some. right. split! => //.
        apply eq_None_not_Some => -[?]. contradict Hnotin. apply HXa.
        by apply elem_of_dom.
Qed.

(** [rhiv_combine_to_b] allows us to express [rhiv_combine] in terms of [rhiv_core_b]. *)
Lemma rhiv_combine_to_b inja injb :
  rhiv_combine inja injb = (λ l, inja !!! l.1 +ₗ l.2) <$> rhiv_core_b inja injb.
Proof.
  apply map_eq => ?. apply option_eq => ?. rewrite rhiv_combine_lookup_Some.
  rewrite lookup_fmap_Some. setoid_rewrite rhiv_core_b_lookup_Some.
  rewrite /is_Some. split => ?; destruct!/=; split!.
  - by erewrite lookup_total_correct.
  - by erewrite lookup_total_correct.
Qed.

(** provs in the new core that are not in the old core are fresh *)
Lemma rhiv_core_b_proj_fresh inj inja injb X p (l : loc):
  map_img (fst <$> injb) ⊆ X →
  (rhiv_core_b (rhiv_proj_a inj inja injb X) (rhiv_proj_b inj inja injb X) ∖
     rhiv_core_b inja injb) !! p = Some l →
  fresh_map (dom inj) X !! p = Some l.1 ∧ l.2 = 0.
Proof.
  move => HXb /lookup_difference_Some[/rhiv_core_b_lookup_Some[/rhiv_proj_b_lookup_Some Horb [? /rhiv_proj_a_lookup_Some Hora]] /rhiv_core_b_lookup_None?].
  destruct Horb as [|[?[??]]]; [|done].
  destruct Hora as [|[? [?[? [??]]]]]; [naive_solver|].
  exploit @fresh_map_lookup_Some; [done|]. move => [? Hnotin]. contradict Hnotin. apply HXb. apply elem_of_map_img.
  setoid_rewrite lookup_fmap_Some. naive_solver.
Qed.

(** Combine the value relation. *)
Lemma rhiv_combine_val {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ vi vm vs:
  ⌈heap_inj_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ rhiv_combine inja' injb', heap_inj_shared ps li0 @ sat γ⌉ -∗
  ⌈val_in_inj vi vm @ sat γa⌉ -∗
  ⌈val_in_inj vm vs @ sat γb⌉ -∗
  ⌈val_in_inj vi vs @ sat γ⌉.
Proof.
  iIntros "Ha Hb H Hva Hvb".
  destruct vi, vm => /=; rewrite ?weak_embed_pure //.
  all: destruct vs => /=; rewrite ?weak_embed_pure //; iDestruct! => //.
  iDestruct "Hva" as (??) "Hla".
  iDestruct "Hvb" as (??) "Hlb". subst => /=.
  iDestruct (heap_inj_shared_lookup with "Ha [$]") as %?.
  iDestruct (heap_inj_shared_lookup with "Hb [$]") as %?.
  iDestruct (big_sepM_lookup (PROP:=uPred heap_injUR) with "[$]") as "?".
  { apply rhiv_combine_lookup_Some. by split!. }
  rewrite /loc_in_inj weak_embed_exist.
  iExists _. iFrame. by rewrite offset_loc_assoc.
Qed.

Lemma rhiv_combine_val_list {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ vi vm vs:
  ⌈heap_inj_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ rhiv_combine inja' injb', heap_inj_shared ps li0 @ sat γ⌉ -∗
  ⌈[∗ list] v1;v2∈vi;vm, val_in_inj v1 v2 @ sat γa⌉ -∗
  ⌈[∗ list] v1;v2∈vm;vs, val_in_inj v1 v2 @ sat γb⌉ -∗
  ⌈[∗ list] v1;v2∈vi;vs, val_in_inj v1 v2 @ sat γ⌉.
Proof.
  iIntros "Haa Hab ? Him Hms".
  iInduction vm as [|] "IH" forall (vi vs). {
    iDestruct (big_sepL2_nil_inv_r (PROP:=uPred heap_injUR) with "Him") as %->.
    iDestruct (big_sepL2_nil_inv_l (PROP:=uPred heap_injUR) with "Hms") as %->.
    simpl. by iPureIntro.
  }
  iDestruct (big_sepL2_cons_inv_l (PROP:=uPred heap_injUR) with "Hms") as (?? ->) "[??]".
  iDestruct (big_sepL2_cons_inv_r (PROP:=uPred heap_injUR) with "Him") as (?? ->) "[??]".
  simpl.
  iDestruct (rhiv_combine_val with "Haa Hab [$] [$] [$]") as "#?".
  iSplit; [done|]. iApply ("IH" with "[$] [$] [$] [$] [$]").
Qed.

Lemma rhiv_combine_val_map {Σ} `{!satG Σ heap_injUR} `{Countable K} inja' injb' γa γb γ (vi vm vs : gmap K val):
  ⌈heap_inj_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ rhiv_combine inja' injb', heap_inj_shared ps li0 @ sat γ⌉ -∗
  ⌈[∗ map] v1;v2∈vi;vm, val_in_inj v1 v2 @ sat γa⌉ -∗
  ⌈[∗ map] v1;v2∈vm;vs, val_in_inj v1 v2 @ sat γb⌉ -∗
  ⌈[∗ map] v1;v2∈vi;vs, val_in_inj v1 v2 @ sat γ⌉.
Proof.
  iIntros "Haa Hab ? Him Hms".
  iInduction vm as [|] "IH" using map_ind forall (vi vs). {
    iDestruct (big_sepM2_empty_l (PROP:=uPred heap_injUR) with "Him") as %->.
    iDestruct (big_sepM2_empty_r (PROP:=uPred heap_injUR) with "Hms") as %->.
    by rewrite big_sepM2_empty.
  }
  iDestruct (big_sepM2_delete_l (PROP:=uPred heap_injUR) with "Hms") as (??) "[??]".
  { apply lookup_insert. }
  iDestruct (big_sepM2_delete_r (PROP:=uPred heap_injUR) with "Him") as (??) "[??]".
  { apply lookup_insert. }
  rewrite delete_insert //.
  iDestruct (rhiv_combine_val with "Haa Hab [$] [$] [$]") as "#?".
  erewrite <-(insert_delete vi) at 2; [|done].
  erewrite <-(insert_delete vs) at 2; [|done].
  rewrite big_sepM2_insert; simplify_map_eq => //.
  iSplit; [done|]. iApply ("IH" with "[$] [$] [$] [$] [$]").
Qed.

(** Split the value relation. *)
Lemma rhiv_split_val {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ vi vs:
  ⌈[∗ map] ps↦li0 ∈ inja', heap_inj_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈heap_inj_shared_auth (rhiv_combine inja' injb') @ sat γ⌉ -∗

  ⌈val_in_inj vi vs @ sat γ⌉ -∗
  ∃ vm, ⌈val_in_inj vi vm @ sat γa⌉ ∗ ⌈val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "Ha Hb H Hv".
  destruct vi, vs => /=; rewrite ?weak_embed_pure //; iDestruct!.
  { iExists (ValNum _) => /=. by iPureIntro. }
  { iExists (ValBool _) => /=. by iPureIntro. }
  { iExists (ValFn _) => /=. by iPureIntro. }
  iDestruct "Hv" as (li ?) "Hl".
  iDestruct (heap_inj_shared_lookup with "H [$]") as %[lm[li'[?[??]]]]%rhiv_combine_lookup_Some.
  iDestruct (big_sepM_lookup (PROP:=uPred heap_injUR) with "Ha") as "?"; [done|].
  iDestruct (big_sepM_lookup (PROP:=uPred heap_injUR) with "Hb") as "?"; [done|].
  subst. iExists (ValLoc (lm +ₗ l0.2)) => /=. iFrame. iSplit; [|done].
  unfold loc_in_inj. simpl. iFrame. by rewrite offset_loc_assoc.
Qed.

Lemma rhiv_split_val_list {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ vis vss:
  ⌈[∗ map] ps↦li0 ∈ inja', heap_inj_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈heap_inj_shared_auth (rhiv_combine inja' injb') @ sat γ⌉ -∗

  ⌈[∗ list] vi;vs∈vis;vss, val_in_inj vi vs @ sat γ⌉ -∗
  ∃ vms, ⌈[∗ list] vi;vm∈vis;vms, val_in_inj vi vm @ sat γa⌉ ∗
         ⌈[∗ list] vm;vs∈vms;vss, val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "Ha Hb H Hv".
  iInduction vis as [|] "IH" forall (vss). {
    iDestruct (big_sepL2_nil_inv_l (PROP:=uPred heap_injUR) with "Hv") as %->.
    iExists []. by simpl.
  }
  iDestruct (big_sepL2_cons_inv_l (PROP:=uPred heap_injUR) with "Hv") as (?? ->) "[??]".
  iDestruct (rhiv_split_val with "Ha Hb [$] [$]") as (?) "#[??]".
  iDestruct ("IH" with "Ha Hb [$] [$]") as (?) "#[??]".
  iExists (_::_) => /=. by repeat iSplit.
Qed.

Lemma rhiv_split_val_map {Σ A} `{!satG Σ heap_injUR} `{Countable A} inja' injb' γa γb γ (vis vss : gmap A val):
  ⌈[∗ map] ps↦li0 ∈ inja', heap_inj_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈heap_inj_shared_auth (rhiv_combine inja' injb') @ sat γ⌉ -∗

  ⌈[∗ map] vi;vs∈vis;vss, val_in_inj vi vs @ sat γ⌉ -∗
  ∃ vms, ⌈[∗ map] vi;vm∈vis;vms, val_in_inj vi vm @ sat γa⌉ ∗
         ⌈[∗ map] vm;vs∈vms;vss, val_in_inj vm vs @ sat γb⌉.
Proof.
  iIntros "Ha Hb H Hv".
  iInduction vis as [|] "IH" using map_ind forall (vss). {
    iDestruct (big_sepM2_empty_r (PROP:=uPred heap_injUR) with "Hv") as %->.
    iExists ∅. by rewrite big_sepM2_empty.
  }
  iDestruct (big_sepM2_delete_l (PROP:=uPred heap_injUR) with "Hv") as (??) "[??]".
  { apply lookup_insert. }
  rewrite delete_insert //.
  iDestruct (rhiv_split_val with "Ha Hb [$] [$]") as (?) "#[? ?]".
  iEval (erewrite <-(insert_delete vss); [|done]).
  iDestruct ("IH" with "[$] [$] [$] [$]") as (vms) "[??]".
  iExists (<[_:=_]>vms). iSplit.
  all: by iApply (big_sepM2_insert_2 (PROP:=uPred heap_injUR)); [done|].
Qed.

(** Allocate the residual for the new provs in the middle heap. *)
Lemma rhiv_alloc_residual {Σ} `{!satG Σ heap_injUR} (m : gmap prov loc) hm γa γb:
  map_img (fst <$> m) ## h_provs hm →
  (∀ i j k, (fst <$> m) !! i = Some k → (fst <$> m) !! j = Some k → i = j) →
  (∀ i k, m !! i = Some k → k.2 = 0%Z) →
  (filter is_ProvStatic (map_img (SA:=gset _) (fst <$> m)) = ∅) →
  ⌈{sat γa}⌉ -∗ ⌈{sat γb}⌉ -∗
  ⌈heap_inj_inv_s hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ ==∗
  ∃ hm', ([∗ map] li0 ∈ m, rhiv_residual γa γb li0) ∗
  ⌈{sat γa}⌉ ∗ ⌈{sat γb}⌉ ∗
  ⌈heap_inj_inv_s hm' @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm' @ sat γb⌉ ∗
  ⌜h_static_provs hm' = h_static_provs hm⌝.
Proof.
  iIntros (? Hinj Hm0 Hs) "?? Hinva Hinvb".

  set bs : gmap prov (gmap Z val) := gset_to_gmap ∅ (map_img (fst <$> m)).
  have ? : dom bs ## h_provs hm by rewrite dom_gset_to_gmap.

  iApply (weak_embed_bupd_intro (sat γa) with "[$]").
  iMod (heapUR_alloc_blocks own_heap_s bs with "Hinva") as "[? Ha]" => //.
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
[rhiv_core_a] into the [big_sepM] for [rhiv_core_b]. This is useful
since then we only need to do an induction over [rhiv_core_b].
However, this only holds if [rhiv_core_b] is an injection, i.e. it
maps different source provenances to different provenances in the
middle heap. (Otherwise, we would need to reuse the same [Φa l.1 li]
for multiple elements of [rhiv_core_b]./) *)
Lemma big_sepM_rhiv_core_a_b_1 {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP} `{!BiPureForall PROP}:
  (** Check that rhiv_core_b is injective *)
  (∀ p1 p2 l1 l2, ⌜l1.1 = l2.1⌝ -∗ Φb p1 l1 -∗ Φb p2 l2 -∗ False) -∗
  ([∗ map] p↦l ∈ rhiv_core_a inja injb, Φa p l) -∗
  ([∗ map] p↦l ∈ rhiv_core_b inja injb, Φb p l) -∗
  ([∗ map] p↦l ∈ rhiv_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜rhiv_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li).
Proof.
  iIntros "Hf ? Hb".
  iAssert ⌜∀ p1 p2 l1 l2, l1.1 = l2.1 → rhiv_core_b inja injb !! p1 = Some l1 → rhiv_core_b inja injb !! p2 = Some l2 → p1 = p2⌝%I as %Himpl. {
    iIntros (p1 p2 l1 l2 ? ??). destruct (decide (p1 = p2)) => //.
    rewrite (big_sepM_delete _ (rhiv_core_b _ _)); [|done]. iDestruct "Hb" as "[? Hb]".
    iDestruct (big_sepM_lookup with "Hb") as "?". { apply lookup_delete_Some. naive_solver. }
    iDestruct ("Hf" with "[//] [$] [$]") as %[].
  }
  iApply big_sepM_sep. iFrame.
  iApply (big_sepM_impl_rel (λ pa la pb lb, pa = lb.1) with "[$]").
  move => ?? /rhiv_core_b_lookup_Some[?[??]].
  split!.
  - apply rhiv_core_a_lookup_Some. naive_solver.
  - iIntros "$". iPureIntro. apply rhiv_core_a_lookup_Some. naive_solver.
  - move => ????. apply: Himpl; [done| |done]. apply rhiv_core_b_lookup_Some. naive_solver.
Qed.

Lemma big_sepM_rhiv_core_a_b_2 {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP}:
  ([∗ map] p↦l ∈ rhiv_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜rhiv_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li) ⊢
  ([∗ map] p↦l ∈ rhiv_core_a inja injb, Φa p l) ∗
  ([∗ map] p↦l ∈ rhiv_core_b inja injb, Φb p l).
Proof.
  iIntros "Hb".
  iDestruct (big_sepM_sep with "Hb") as "[$ ?]".
  iApply (big_sepM_impl_rel (λ pb lb pa la, pa = lb.1) with "[$]").
  move => ?? /rhiv_core_a_lookup_Some[?[? [? [??]]]].
  split!.
  - done.
  - apply rhiv_core_b_lookup_Some. naive_solver.
  - iIntros "(%& %Ha & ?)". move: Ha => /rhiv_core_a_lookup_Some[?[?[?[??]]]]. by simplify_eq.
  - naive_solver.
Qed.

Lemma big_sepM_rhiv_core_a_b {PROP : bi} inja injb (Φa Φb : _ → _ → PROP) `{!BiAffine PROP} `{!BiPureForall PROP}:
  (∀ p1 p2 l1 l2, l1.1 = l2.1 → Φb p1 l1 -∗ Φb p2 l2 -∗ False) →
  ([∗ map] p↦l ∈ rhiv_core_a inja injb, Φa p l) ∗
  ([∗ map] p↦l ∈ rhiv_core_b inja injb, Φb p l) ⊣⊢
  ([∗ map] p↦l ∈ rhiv_core_b inja injb,
    Φb p l ∗ ∃ li, ⌜rhiv_core_a inja injb !! l.1 = Some li⌝ ∗ Φa l.1 li).
Proof.
  move => Hf. iSplit.
  - iIntros "[??]". iApply (big_sepM_rhiv_core_a_b_1 with "[] [$] [$]"). iIntros. by iApply (Hf with "[$] [$]").
  - iIntros "?". by iApply big_sepM_rhiv_core_a_b_2.
Qed.

(** Create the large invariant and the residual from the two small invariants. *)
Lemma rhiv_shared_from_ab {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ ha hb hm:
  heapUR_trader (sat γ) (sat γa) own_heap_i own_heap_i -∗
  heapUR_trader (sat γ) (sat γb) own_heap_s own_heap_s -∗
  ⌈heap_inj_inv_i ha @ sat γa⌉ -∗
  ⌈heap_inj_inv_s hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ -∗
  ⌈heap_inj_inv_s hb @ sat γb⌉ -∗
  ⌈heap_inj_shared_auth inja' @ sat γa⌉ -∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ rhiv_combine inja' injb', heap_inj_shared ps li0 @ sat γ⌉ -∗

  (** interesting part starts here *)
  ⌈heap_in_inj_inv (rhiv_core_a inja' injb') [] @ sat γa⌉ -∗
  ⌈heap_in_inj_inv (rhiv_core_b inja' injb') [] @ sat γb⌉ ==∗⌈sat γ⌉
  (⌈heap_in_inj_inv (rhiv_combine inja' injb') [] @ sat γ⌉ ∗
  ([∗ map] ps↦li0 ∈ rhiv_core_b inja' injb', rhiv_residual γa γb li0)) ∗
  (** interesting part ends here *)

  heapUR_trader (sat γ) (sat γa) own_heap_i own_heap_i ∗
  heapUR_trader (sat γ) (sat γb) own_heap_s own_heap_s ∗
  ⌈heap_inj_inv_i ha @ sat γa⌉ ∗
  ⌈heap_inj_inv_s hm @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ ∗
  ⌈heap_inj_inv_s hb @ sat γb⌉ ∗
  ⌈heap_inj_shared_auth inja' @ sat γa⌉ ∗
  ⌈heap_inj_shared_auth injb' @ sat γb⌉.
Proof.
  iIntros "???????? #? ? ?". rewrite /heap_in_inj_inv.
  have Hempty : ∀ k, k ∈ [] ↔ False by set_solver.
  setoid_rewrite Hempty. setoid_rewrite bi.False_or.
  iEval (rewrite rhiv_combine_to_b big_sepM_fmap).
  rewrite (weak_embed_big_sepM _ _ (rhiv_core_a _ _)).
  rewrite !(weak_embed_big_sepM _ _ (rhiv_core_b _ _)).
  iDestruct (big_sepM_rhiv_core_a_b_1 with "[] [$] [$]") as "?".
  { iIntros (???? ->) "(%&%&?&?&?) (%&%&?&?&?)". iDestruct (heapUR_block_excl own_heap_i with "[$] [$]") as %[]. }
  rewrite -big_sepM_sep.
  iMod (big_sepM_impl_weak_bupd_frame with "[$] [] [-]") as "[$ ?]".
  2: iAccu. 2: by iFrame.
  iIntros "!>" (???). iIntros "(Hta & Htb & ? & Hma & Hmb & ? & Hsha & Hshb)".
  iIntros "[(% & % & % & ? & ? & Hvb) Ha]".

  iDestruct "Ha" as (?[??]%rhiv_core_a_lookup_Some) "(% & % & % & ? & ? & Hva)" => //=.
  iMod (heapUR_trade_block with "Hta [$] [$]") as "[? [??]]".
  iMod (heapUR_trade_block with "Htb [$] [$]") as "[? [??]]".
  iDestruct (heapUR_lookup_block (PROP:=uPred heap_injUR) with "Hma [$]") as %?.
  iDestruct (heapUR_lookup_block (PROP:=uPred heap_injUR) with "Hmb [$]") as %?.
  simplify_eq.
  iDestruct (rhiv_combine_val_map with "Hsha Hshb [$] Hva Hvb") as "#?". iFrame.
  iModIntro. erewrite lookup_total_correct => //. iFrame.
  repeat iSplit => //. iPureIntro. lia.
Qed.

(** Create the two small invariants from the large invariant and the residual. *)
Lemma rec_heap_inj_vertical_shared_to_ab {Σ} `{!satG Σ heap_injUR} inja' injb' γa γb γ ha hb hm:
  ⌈{sat γa}⌉ -∗ ⌈{sat γb}⌉ -∗
  heapUR_trader (sat γa) (sat γ) own_heap_i own_heap_i -∗
  heapUR_trader (sat γb) (sat γ) own_heap_s own_heap_s -∗
  ⌈heap_inj_inv_i ha @ sat γ⌉ -∗
  ⌈heap_inj_inv_s hm @ sat γa⌉ -∗
  ⌈heap_inj_inv_i hm @ sat γb⌉ -∗
  ⌈heap_inj_inv_s hb @ sat γ⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ inja', heap_inj_shared ps li0 @ sat γa⌉ -∗
  ⌈[∗ map] ps↦li0 ∈ injb', heap_inj_shared ps li0 @ sat γb⌉ -∗
  ⌈heap_inj_shared_auth (rhiv_combine inja' injb') @ sat γ⌉ -∗

  (** interesting part starts here *)
  ⌈heap_in_inj_inv (rhiv_combine inja' injb') [] @ sat γ⌉ -∗
  ([∗ map] ps↦li0 ∈ rhiv_core_b inja' injb', rhiv_residual γa γb li0) ==∗
  ∃ hm',
  (⌈heap_in_inj_inv (rhiv_core_a inja' injb') [] @ sat γa⌉ ∗
  ⌈heap_in_inj_inv (rhiv_core_b inja' injb') [] @ sat γb⌉) ∗
  (** interesting part ends here *)

  ⌈{sat γa}⌉ ∗ ⌈{sat γb}⌉ ∗
  heapUR_trader (sat γa) (sat γ) own_heap_i own_heap_i ∗
  heapUR_trader (sat γb) (sat γ) own_heap_s own_heap_s ∗
  ⌈heap_inj_inv_i ha @ sat γ⌉ ∗
  ⌈heap_inj_inv_s hm' @ sat γa⌉ ∗
  ⌈heap_inj_inv_i hm' @ sat γb⌉ ∗
  ⌈heap_inj_inv_s hb @ sat γ⌉ ∗
  ⌈heap_inj_shared_auth (rhiv_combine inja' injb') @ sat γ⌉ ∗ ⌜h_static_provs hm' = h_static_provs hm⌝.
Proof.
  iIntros "????????#Hsa#Hsb???".
  rewrite /heap_in_inj_inv.
  have Hempty : ∀ k, k ∈ [] ↔ False by set_solver.
  setoid_rewrite Hempty. setoid_rewrite bi.False_or.
  rewrite {2}rhiv_combine_to_b big_sepM_fmap.
  setoid_rewrite (weak_embed_big_sepM _ _ (rhiv_core_a _ _)).
  setoid_rewrite (weak_embed_big_sepM _ _ (rhiv_core_b _ _)).
  setoid_rewrite big_sepM_rhiv_core_a_b; try apply _.
  2: { iIntros (???? ->) "(%&%&?&?&?) (%&%&?&?&?)". iDestruct (heapUR_block_excl own_heap_i with "[$] [$]") as %[]. }
  iDestruct (big_sepM_sep with "[$]") as "Hm".
  iApply (big_sepM_impl_bupd_ex_frame with "Hm"). 2: by iFrame.
  iIntros "!>" (???[?[??]]%rhiv_core_b_lookup_Some) "(?&?&Hta&Htb&?&Hinva&Hinvb&?&?&<-) [[%[%[??]]] [%[%[%Htot[Hi[Hs Hv]]]]]]".
  erewrite lookup_total_correct in Htot |- * => //. simplify_eq/=.
  iDestruct (rhiv_split_val_map with "Hsa Hsb [$] [$]") as (bm) "#[? ?]". simpl.

  iApply (weak_embed_bupd_intro (sat γa) with "[$]").
  iDestruct (heapUR_lookup_block_prov own_heap_s with "Hinva [$]") as %?.
  iMod (heapUR_update_block own_heap_s with "Hinva [$]") as "[? ?]".
  iMod (heapUR_trade_block with "Hta [$] [$]") as "[? [??]]".
  iIntros "!> Hγa".

  iApply (weak_embed_bupd_intro (sat γb) with "[$]").
  iMod (heapUR_update_block own_heap_i with "Hinvb [$]") as "[? ?]".
  iMod (heapUR_trade_block with "Htb [$] [$]") as "[? [??]]".
  iIntros "!> Hγb".

  iModIntro. iFrame. iSplit!; repeat iSplit => //.
  - by rewrite h_static_provs_update_block.
  - apply rhiv_core_a_lookup_Some. naive_solver.
  - iPureIntro. lia.
Qed.

Lemma rec_heap_inj_vertical m hinit `{!VisNoAng m.(m_trans)} :
  trefines (rec_heap_inj hinit (rec_heap_inj hinit m))
           (rec_heap_inj hinit m).
Proof.
  unshelve apply: mod_prepost_combine_bi.
  set (Σ := #[satΣ heap_injUR]). have ? : satG Σ heap_injUR by apply _. clearbody Σ.
  eexists Σ, _, _, _ => γa γb γ.
  unshelve eexists _.  {
    exact (λ pl _ _ _,
      ∃ inja injb inj statics,
        if pl is Env then
          (* We only require the subseteq here since it makes the
          initialization easier. *)
          ⌜rhiv_combine inja injb ⊆ inj⌝ ∗ ∃ hm,
          ⌜h_static_provs hm = statics⌝ ∗
          ⌈[∗ map] ps↦li0∈inj, heap_inj_shared ps li0 @ sat γ⌉ ∗
          ⌈heap_inj_shared_auth inja @ sat γa⌉ ∗
          ⌈heap_inj_shared_auth injb @ sat γb⌉ ∗
          ⌈heap_in_inj_inv (inja ∖ rhiv_core_a inja injb) [] @ sat γa⌉ ∗
          ⌈heap_in_inj_inv (injb ∖ rhiv_core_b inja injb) [] @ sat γb⌉ ∗
          ([∗ map] ps↦li0 ∈ rhiv_core_b inja injb, rhiv_residual γa γb li0) ∗
          ⌈heapUR_inv own_heap_s hm @ sat γa⌉ ∗
          ⌈heapUR_inv own_heap_i hm @ sat γb⌉ ∗
          heapUR_trader (sat γa) (sat γ) own_heap_i own_heap_i ∗
          heapUR_trader (sat γb) (sat γ) own_heap_s own_heap_s ∗
          (* This proof could be quite a bit simpler without the
          requirement that the statics stay the same. (It is not used
          in this proof.) *)
          ⌈heap_inj_statics statics @ sat γa⌉ ∗
          ⌈heap_inj_statics statics @ sat γb⌉ ∗
          ⌈heap_inj_statics statics @ sat γ⌉
        else
          ⌜inj = rhiv_combine inja injb⌝ ∗
          ⌈[∗ map] ps↦li0∈inja, heap_inj_shared ps li0 @ sat γa⌉ ∗
          ⌈[∗ map] ps↦li0∈injb, heap_inj_shared ps li0 @ sat γb⌉ ∗
          ⌈heap_inj_shared_auth inj @ sat γ⌉ ∗
          heapUR_trader (sat γ) (sat γa) own_heap_i own_heap_i ∗
          heapUR_trader (sat γ) (sat γb) own_heap_s own_heap_s ∗
          ⌈heap_inj_statics statics @ sat γa⌉ ∗
          ⌈heap_inj_statics statics @ sat γb⌉ ∗
          ⌈heap_inj_statics statics @ sat γ⌉
          )%I. }
  split_and!.
  - move => /= e ? h.
    iIntros "([Hiniti Hinits] & [($&Hinv&[%inj[Hsh ?]]& $ & #?) $] & _)".
    iDestruct (heapUR_lookup_block_big own_heap_s with "Hinv Hinits") as %Hblocks.
    set staticbs : gmap prov (gmap Z val) :=
            gset_to_gmap ∅ (h_static_provs h) ∖ hinit.
    iExists _, _. iSplit!. {
      apply: satisfiable_bmono; [apply heap_inj_init|].
      iIntros "(? & ? & Hinvi & Hinvs)".
      iMod (heapUR_alloc_blocks with "Hinvi") as "[Hinvi $]"; [set_solver|].
      iMod (heapUR_alloc_blocks _ (hinit ∪ staticbs) with "Hinvs") as "[Hinvs Hbs]"; [set_solver|].
      iDestruct (big_sepM_union with "Hbs") as "[$ ?]";
        [apply map_disjoint_difference_r'|].
      rewrite !right_id. iModIntro. iAccu.
    } {
      apply: satisfiable_bmono; [apply heap_inj_init|].
      iIntros "(? & ? & Hinvi & Hinvs)".
      iMod (heapUR_alloc_blocks _ (hinit ∪ staticbs) with "Hinvi") as "[Hinvi Hbs]"; [set_solver|].
      iMod (heapUR_alloc_blocks with "Hinvs") as "[Hinvs $]"; [set_solver|].
      iDestruct (big_sepM_union with "Hbs") as "[$ ?]";
        [apply map_disjoint_difference_r'|].
      rewrite !right_id. iModIntro. iAccu.
    }
    iIntros "Hγa Hγb Hγ (?&?&Hinvia&?&?) (?&?&?&Hinvsb&?)".
    iModIntro. iFrame "#∗". iFrame "#".
    iExists ∅. rewrite /heap_in_inj_inv !big_sepM_empty. iSplit!. {
      rewrite h_static_provs_heap_from_blocks dom_union_L dom_difference_L.
      rewrite (comm (R:=(=)) (∪)) difference_union_L.
      rewrite dom_gset_to_gmap filter_union_L (comm (R:=(=)) (∪)).
      rewrite subseteq_union_1_L; [set_solver|].
      rewrite map_subseteq_spec in Hblocks.
      move => ? /elem_of_filter[?/elem_of_dom[? /Hblocks/h_blocks_lookup_Some[??]]].
      apply elem_of_filter. split!. by apply elem_of_h_static_provs.
    }
    iSplitL "Hinvia Hiniti"; iApply (heapUR_trader_init_blocks with "[$] [$]").
  - move => /= ??????. iIntros "??? [[Hinv ?] _] (%inja & %injb & %inj & %statics & % & %  & % & ? & Hsha & Hshb & Hinja & Hs)". simplify_eq.
    iDestruct (big_sepL2_length (PROP:=uPred heap_injUR) with "[$]") as %?.
    iDestruct "Hs" as "(Hinjb & Hbs & ? & ? & Hta & Htb & #Hsa & #Hsb & #Hs)".
    iDestruct "Hinv" as "(Hinvi & Hinvs & [%inj' [Hsh Hinj]] & Hs1 & Hs2)".
    iDestruct (heap_inj_statics_eq with "Hs1 Hs2") as %Heq1.
    iDestruct (heap_inj_statics_eq with "Hs Hs2") as %Heq2.
    iDestruct (heap_inj_shared_lookup_big with "Hsh [$]") as %?.

    iAssert ⌜inj' ##ₘ injb ∖ rhiv_core_b inja injb⌝%I as %?. {
      rewrite map_disjoint_spec.
      iIntros (?????).
      iDestruct (heap_in_inj_inv_borrow with "Hinj") as (???) "(?&?&Hp&?)"; [apply not_elem_of_nil|done|].
      iDestruct (heap_in_inj_inv_borrow with "Hinjb") as (???) "(?&?&?&?)"; [apply not_elem_of_nil|done|].
      iApply bupd_plainly.
      iApply (weak_embed_bupd_intro (sat γb) with "[$]").
      iMod (heapUR_trade_block with "[$] [$] Hp") as "[? [??]]".
      iDestruct (heapUR_block_excl own_heap_s with "[$] [$]") as %[].
    }

    (* Technically, h_provs hm should suffice, but it would require more proofs. *)
    set (X := (dom inja ∪ map_img (fst <$> injb) ∪ h_provs hm)).
    set (inja' := (rhiv_proj_a inj' inja injb X)).
    set (injb' := (rhiv_proj_b inj' inja injb X)).

    have -> : inj' = rhiv_combine inja' injb' by
      apply rhiv_combine_proj; [by etrans |done|set_solver..].

    (** Update the small injections  *)
    iApply (weak_embed_bupd_intro (sat γb) with "[$]").
    iMod (heap_inj_shared_alloc_big _ injb' with "Hshb") as "[? #Hshbbig]".
    { apply rhiv_proj_b_subseteq. }
    iIntros "!> Hγb". iFrame "Hshbbig".

    iApply (weak_embed_bupd_intro (sat γa) with "[$]").
    iMod (heap_inj_shared_alloc_big _ inja' with "Hsha") as "[? #Hshabig]".
    { apply rhiv_proj_a_subseteq. }
    iIntros "!> Hγa". iFrame "Hshabig".

    (** Update the residual *)
    iMod (rhiv_alloc_residual (rhiv_core_b inja' injb' ∖ rhiv_core_b inja injb) with "[$] [$] [$] [$]") as (hm') "[Hbs' [Hγa [Hγb[?[?%Heqm]]]]]". {
      move => ? /elem_of_map_img[? /lookup_fmap_Some[? [? ]]]. subst.
      move => /rhiv_core_b_proj_fresh[|/(fresh_map_lookup_Some _ _ _ _)]; set_solver.
    } {
      move => ??? /lookup_fmap_Some[[??][? /rhiv_core_b_proj_fresh[|??]]]. 1: set_solver.
      move => /lookup_fmap_Some[[??][? /rhiv_core_b_proj_fresh[|??]]]. 1: set_solver. simplify_eq/=.
      by apply: fresh_map_bij.
    } { move => ?? /rhiv_core_b_proj_fresh[|//]. set_solver. } {
      apply equiv_empty_L. move => ? /elem_of_filter[? /elem_of_map_img[? /lookup_fmap_Some[l [? ]]]]. subst.
      move => /rhiv_core_b_proj_fresh[//|/fresh_map_is_Block]. 1: set_solver. by destruct l.1.
    }
    iDestruct (big_sepM_union_2 with "Hbs Hbs'") as "Hbs".
    rewrite map_difference_union. 2: { apply rhiv_core_b_proj_subseteq. }

    (** Create the small [heap_in_inj_inv]. *)
    iMod (rec_heap_inj_vertical_shared_to_ab with "Hγa Hγb Hta Htb [$] [$] [$] [$] [$] [$] [$] [$] [$]") as (?) "([??] & ? & ? & ? & ? & ? & ? & ? & ? & ? & %Heqm')".

    iDestruct (heap_in_inj_inv_combine with "Hinja [$]") as "Hinja".
    iDestruct (heap_in_inj_inv_combine with "Hinjb [$]") as "Hinjb".
    erewrite rhiv_recombine_a => //. erewrite rhiv_recombine_b => //.
    2: set_solver.

    (** Split the val_in_inj for the arguments. *)
    iDestruct (rhiv_split_val_list with "Hshabig Hshbbig [$] [$]") as (vms) "#[Hv1 ?]".
    iDestruct (big_sepL2_length (PROP:=uPred heap_injUR) with "Hv1") as %?.

    (** Transfer the traders *)
    iApply (weak_embed_bupd_intro (sat γb) with "[$]").
    iMod (heapUR_trader_switch with "[$] [$]") as "[$ ?]".
    iIntros "!> ?".
    iApply (weak_embed_bupd_intro (sat γa) with "[$]").
    iMod (heapUR_trader_switch with "[$] [$]") as "[$ ?]".
    iIntros "!> ?". iModIntro.

    (** Finish *)
    iExists vms, _. setoid_rewrite event_set_vals_heap_idemp.
    rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap //.
    iFrame "#∗". iSplit!; repeat iSplit => //.
    + by rewrite Heq1 -Heq2.
    + by rewrite Heqm' Heqm.
    + by rewrite Heqm' Heqm.
    + by rewrite -Heq2.

  - move => /= ????????. iIntros "??? [[Hinva Hva] _] [[Hinvb Hvb] _] (%inja & %injb & %inj & %statics & % & ? & ? & Hsh & Hta & Htb & Hsa & Hsb & #Hs)".
    iDestruct (big_sepL2_length (PROP:=uPred heap_injUR) with "[$]") as %?.
    rewrite heap_of_event_event_set_vals_heap event_set_vals_heap_idemp vals_of_event_event_set_vals_heap //.
    iDestruct "Hinva" as "(Hinvia & Hinvsa & [%inja' [Hsha Hinja]] & Hsa1 & Hsa2)".
    iDestruct "Hinvb" as "(Hinvib & Hinvsb & [%injb' [Hshb Hinjb]] & Hsb1 & Hsb2)".
    iDestruct (heap_inj_statics_eq with "Hsa1 Hsa2") as %Heq1.
    iDestruct (heap_inj_statics_eq with "Hsa Hsa1") as %?.
    iDestruct (heap_inj_statics_eq with "Hsb1 Hsb2") as %Heq2.
    iDestruct (heap_inj_statics_eq with "Hsb Hsb1") as %?.
    iFrame "Hsa Hsb Hs".
    iDestruct (heap_inj_shared_lookup_big with "Hsha [$]") as %?.
    iDestruct (heap_inj_shared_lookup_big with "Hshb [$]") as %?.

    (** Update the large injection *)
    iApply (weak_embed_bupd_intro (sat γ) with "[$]").
    iMod (heap_inj_shared_alloc_big _ (rhiv_combine inja' injb') with "Hsh") as "[? #Hshbig]".
    { subst. by apply rhiv_combine_subseteq. }
    iIntros "!> ?". iFrame "Hshbig".

    (** Split the small invariants *)
    iDestruct (heap_in_inj_inv_split (rhiv_core_a inja' injb') with "Hinja") as "[? Hinja]"; [apply rhiv_core_a_subseteq|].
    iDestruct (heap_in_inj_inv_split (rhiv_core_b inja' injb') with "Hinjb") as "[? Hinjb]"; [apply rhiv_core_b_subseteq|].
    iFrame "Hinja Hinjb".

    (** Combine the small invariants to get the large invariant. *)
    iApply (weak_embed_bupd_intro (sat γ) with "[$]").
    iMod (rhiv_shared_from_ab with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]") as "[[??][?[?[? [? [? [? [Hsha Hshb]]]]]]]]".

    (** Combine the val_in_inj for the arguments. *)
    iDestruct (rhiv_combine_val_list with "Hsha Hshb [$] [$] [$]") as "#?".

    (** Transfer the traders *)
    iMod (heapUR_trader_switch with "[$] [$]") as "[$ $]".
    iMod (heapUR_trader_switch with "[$] [$]") as "[$ ?]".
    iIntros "!> ?". iModIntro.

    (** Finish *)
    iExists _, _. iFrame. iSplit!.
    repeat iSplit.
    + by subst.
    + subst. by rewrite -Heq2 -Heq1.
    + done.
Qed.

(*
For the following definition of the sharing invariant, it is impossible to prove
vertical compositionality:

Definition heap_in_inj_inv (inj : gmap prov loc) (rem : list prov) :
  uPred heap_injUR :=
    [∗ map] ps↦li0∈inj, ⌜ps ∈ rem⌝ ∨
      ∃ b, heap_inj_block_s ps b ∗
      [∗ map] o↦vs∈b, ∃ vi, (li0 +ₗ o) ↦hi vi ∗ val_in_inj vi vs.

This is because of the following situation:

In the two wrappers, we have two blocks that are mapped to two different blocks
in the first wrapper and to one block in the second wrapper:

---  ---
| |  | |
---  ---
| |  | |
--------

From the perspective of the single wrapper, the middle blocks disappear, so it looks
like this:
---  ---
| |  | |
| |  | |
| |  | |
--------

Now the outer code can move locations from the second to the first block.
This works since it does not need the dom in the target for this, resulting in a
picture like the following:

----  --
|  |  ||
|  |  ||
|  |  ||
--------

However, we cannot backtranslate this picture to the two wrappers, since we do not
have the dom for the provenances in the middle and in fact the code in the middle
might rely on the fact that the dom of the provenances in the middle does not change.

---  ---
| |  | |
---  ---
|  |  ||
--------

So one could prove false from the vertical composition with suitable modules.

One idea to get an injection wrapper that is vertically composable is to not put
the full dom of the source into the sharing invariant, but only 1/2 fraction.
This would mean that each module can only change the size of blocks that it allocated
itself. This seems like a reasonable solution, but the resulting wrapper would be
incomparable to the existing bijection wrapper. In the vertical composition proof,
one would make sure that one has all doms for the middle heap for the provenances
that were shared by the environment. This would require some looking into the trader
to make sure that one never trades a full dom that belongs to the inner module.

The definition of the invariant could look like this:

Definition heap_in_inj_inv (inj : gmap prov loc) (rem : list prov) :
  uPred heap_injUR :=
    [∗ map] ps↦li0∈inj, ⌜ps ∈ rem⌝ ∨
      ∃ d, heap_inj_dom_s ps (1/2) d ∗
      [∗ map] o∈d, ∃ vi vs, (li0 +ₗ o) ↦hi vi ∗ (p, o) ↦hs vs ∗ val_in_inj vi vs.

An alternative idea is to add some more ghost state that ensure that shared blocks
can only shrink, but not grow. This would allow deallocation by other modules, while
preventing the problematic situation from above but otherwise restrict everything
quite a bit more. Also setting up the extra ghost state would be more tricky.
*)
