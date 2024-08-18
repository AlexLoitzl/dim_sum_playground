From dimsum.core Require Export proof_techniques.
From dimsum.core Require Import prepost.
From dimsum.examples Require Import rec asm rec_to_asm rec_heap_bij.

Local Open Scope Z_scope.

(** * Vertical compositionality of [rec_to_asm] and [rec_heap_bij] *)
(** Overview of the structure of the proof:

There are three heaps / memories involved:
- the inner heap, seen by the inner module [m],
- the middle heap, after applying [rec_heap_bij], but before [rec_to_asm]
- the outer memory, after applying both [rec_heap_bij] and [rec_to_asm]

Additionally, there are the following translations:
- [rh : gmap prov rec_to_asm_elem] : inner heap ↔ asm memory
- [rha : gmap prov rec_to_asm_elem] : middle heap ↔ asm memory
- [bijb : heap_bij] : inner heap ↔ middle heap

There are allow the following private states:
- [ho] : private locations of the program in the inner heap
- [hob] : private locations of the environment in the inner heap


They are related as depicted by the following diagram:

  memory              middle heap                inner heap
    -----------------------|-------------------------|------------------------
    |    r2a_shared rha    |                         | r2a_shared rh         |
    -----------------------|     hb_shared bijb      |------------------------
        |                  |                         | r2a_constant rh (ho)  |
        | r2a_constant rha |--------------------------------------------------
        |                  |                |
    -----------------------| hb_priv_i bijb |
    |   r2a_shared rha     |                |
    --------------------------------------------------------------------------
                                    |                | r2a_constant rh (ho)  |
                                    | hb_priv_s bijb |------------------------
                                    |                | r2a_constant rh (hob) |
                                    ------------------------------------------
*)


(** * through bij *)
Definition val_through_bij (bij : heap_bij) (vs : val) : val :=
  match vs with
  | ValLoc l => ValLoc (if hb_bij bij !! l.1 is Some (HBShared p) then p else (ProvBlock 42), l.2)
  | _ => vs
  end.

Program Definition heap_through_bij (bij : heap_bij) (h : heap_state) : heap_state :=
  Heap (list_to_map $ omap (λ '(l, v), if hb_bij bij !! l.1 is Some (HBShared p) then
         Some ((p, l.2), val_through_bij bij v) else None) (map_to_list (h_heap h)))
       (set_omap prov_to_block (hb_shared_i bij)) _.
Next Obligation.
  move => ??? b. rewrite list_to_map_lookup_is_Some => -[?]. rewrite elem_of_list_omap => -[[[??]?]]/=[??].
  repeat case_match; simplify_eq. rewrite elem_of_set_omap => ?. exists (ProvBlock b). split!. rewrite elem_of_hb_shared_i. naive_solver.
Qed.

Lemma heap_through_bij_Some bij h pi o vi:
  h_heap (heap_through_bij bij h) !! (pi, o) = Some vi ↔
    ∃ ps vs, hb_bij bij !! ps = Some (HBShared pi) ∧ h_heap h !! (ps, o) = Some vs ∧ vi = val_through_bij bij vs.
Proof.
  simpl. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [[??]?] [[??]?] [??] /=.
    move => /elem_of_map_to_list ?/elem_of_map_to_list? /fmap_Some[[??][??]] /fmap_Some[[??][??]].
    by repeat case_match; simplify_eq/=; simplify_bij.
  }
  rewrite elem_of_list_omap.
  split.
  - move => [[[??]?]]. rewrite elem_of_map_to_list => ?. repeat case_match => //; naive_solver.
  - move => ?. destruct!. eexists (_,_,_). rewrite elem_of_map_to_list. split; [done|].
    by simplify_option_eq.
Qed.

Lemma heap_through_bij_blocks bij h:
 h_used_blocks (heap_through_bij bij h) = set_omap prov_to_block (hb_shared_i bij).
Proof. done. Qed.

Opaque heap_through_bij.

Lemma heap_through_bij_is_Some bij h pi o:
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔
          ∃ ps, hb_bij bij !! ps = Some (HBShared pi) ∧ is_Some (h_heap h !! (ps, o)).
Proof. rewrite /is_Some. setoid_rewrite heap_through_bij_Some. naive_solver. Qed.

Lemma heap_through_bij_is_Some1 bij h pi ps o:
  hb_bij bij !! ps = Some (HBShared pi) →
  is_Some (h_heap (heap_through_bij bij h) !! (pi, o)) ↔ is_Some (h_heap h !! (ps, o)).
Proof.
  move => ?. rewrite heap_through_bij_is_Some. split; [|naive_solver].
  move => [p'[??]]. by simplify_bij.
Qed.

Lemma h_static_provs_heap_through_bij bij h :
  dom (hb_bij bij) ⊆ h_provs h →
  h_static_provs (heap_through_bij bij h) = filter is_ProvStatic (hb_shared_i bij).
Proof.
  move => Hdom.
  apply set_eq => p.
  rewrite elem_of_filter !elem_of_h_static_provs elem_of_hb_shared_i.
  split.
  - move => [? [[??]/=[? ]]]. subst. rewrite heap_through_bij_is_Some.
    move => [p2 [??]]. naive_solver.
  - move => [? [p2 ?]]. split; [done|].
    exploit hb_shared_prov; [done|] => ?.
    exploit same_prov_kind_static_l; [done..|] => ?. subst.
    have : p2 ∈ h_provs h. { apply Hdom. by apply: elem_of_dom_2. }
    rewrite elem_of_h_provs elem_of_h_static_provs => ?. destruct!/=.
    eexists (_, l.2). split!.
    rewrite heap_through_bij_is_Some1; [|done]. by destruct l.
Qed.

Lemma h_provs_heap_through_bij bij h :
  dom (hb_bij bij) ⊆ h_provs h →
  h_provs (heap_through_bij bij h) = hb_shared_i bij.
Proof.
  move => ?.
  apply set_eq => p.
  rewrite elem_of_h_provs /=.
  rewrite h_static_provs_heap_through_bij // heap_through_bij_blocks elem_of_filter.
  setoid_rewrite elem_of_set_omap.
  destruct p; [|set_solver].
  split; [|naive_solver].
  move => -[|[? [?[[]]]]]; naive_solver.
Qed.

(** * combine bij *)
(** ** r2a_combine_bij *)
Definition r2a_combine_bij (rh : gmap prov Z) (bij : heap_bij) : gmap prov Z :=
  omap (λ v, if v is HBShared pi then
               if rh !! pi is Some a then
                 Some a
               else
                 None
             else
               None) bij.(hb_bij).

Lemma r2a_combine_bij_lookup_Some rh bij p a:
  r2a_combine_bij rh bij !! p = Some a ↔ ∃ p', hb_bij bij !! p = Some (HBShared p') ∧ rh !! p' = Some a.
Proof.
  rewrite /r2a_combine_bij lookup_omap_Some.
  split => ?; destruct!.
  - do 2 case_match => //. simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
Qed.

Lemma r2a_combine_bij_mono rh bij rh' bij' :
  rh ⊆ rh' →
  hb_shared bij ⊆ hb_shared bij' →
  r2a_combine_bij rh bij ⊆ r2a_combine_bij rh' bij'.
Proof.
  move => Hih Hbij. apply map_subseteq_spec => ??.
  setoid_rewrite r2a_combine_bij_lookup_Some.
  setoid_rewrite <-hb_shared_lookup_Some => -[?[??]].
  split!; by apply: lookup_weaken.
Qed.

(** ** r2a_combine_priv_shared *)
Definition r2a_combine_priv_shared (rh : gmap prov Z) (bij : heap_bij) (hb : heap_state)
  : gmap prov (gmap Z val) :=
  map_imap (λ ps v, if v is HBShared pi then
               if rh !! pi is Some a then
                 None
               else
                 Some (h_block hb ps)
             else
               None) bij.(hb_bij).

Lemma r2a_combine_priv_shared_Some rh bij p b hb:
  r2a_combine_priv_shared rh bij hb !! p = Some b ↔
    ∃ pi, hb_bij bij !! p = Some (HBShared pi) ∧ rh !! pi = None ∧ b = h_block hb p.
Proof.
  rewrite /r2a_combine_priv_shared map_lookup_imap bind_Some.
  split => ?; destruct!.
  - repeat case_match => //; simplify_eq. naive_solver.
  - eexists (HBShared _). by simplify_map_eq.
Qed.

Lemma r2a_combine_priv_shared_priv_s_disj rh bij ho :
  r2a_combine_priv_shared rh bij ho ##ₘ hb_priv_s bij.
Proof.
  apply map_disjoint_spec => ???. rewrite r2a_combine_priv_shared_Some hb_priv_s_lookup_Some. naive_solver.
Qed.


(** ** r2a_combine_priv *)
Definition r2a_combine_priv (rh : gmap prov Z) (bij : heap_bij) (hb : heap_state) : gmap prov (gmap Z val) :=
  r2a_combine_priv_shared rh bij hb ∪ hb_priv_s bij.

Lemma r2a_combine_priv_Some rh bij p b hb:
  r2a_combine_priv rh bij hb !! p = Some b ↔
    hb_bij bij !! p = Some (HBConstant b) ∨
    ∃ pi, hb_bij bij !! p = Some (HBShared pi) ∧ rh !! pi = None ∧ b = h_block hb p.
Proof.
  rewrite /r2a_combine_priv lookup_union_Some. 2: by apply r2a_combine_priv_shared_priv_s_disj.
  rewrite r2a_combine_priv_shared_Some hb_priv_s_lookup_Some. naive_solver.
Qed.

(** ** combine lemmas *)
Lemma r2a_combine_priv_diff rh bij hb ho :
  r2a_combine_priv_shared rh bij hb ⊆ ho →
  r2a_combine_priv rh bij hb ∖ ho = hb_priv_s bij ∖ ho.
Proof.
  move => Hho.
  apply map_eq => ?. apply option_eq => ?.
  rewrite !lookup_difference_Some r2a_combine_priv_Some hb_priv_s_lookup_Some.
  split => ?; destruct! => //.
  - exfalso. revert select (ho !! _ = None). apply not_eq_None_Some. apply: lookup_weaken_is_Some; [|done].
    eexists _. apply r2a_combine_priv_shared_Some. naive_solver.
  - naive_solver.
Qed.

Lemma r2a_combine_bij_priv_disj rh bij h:
  R2AShared <$> r2a_combine_bij rh bij ##ₘ R2AConstant <$> r2a_combine_priv rh bij h.
Proof.
  apply map_disjoint_spec => ???.
  rewrite !lookup_fmap !fmap_Some.
  setoid_rewrite r2a_combine_bij_lookup_Some. setoid_rewrite r2a_combine_priv_Some.
  move => ??. destruct!.
Qed.

(** ** r2a_combine_extend *)
Lemma fresh_map_learn rh bijb (X : gset prov) ps pi:
  fresh_map (dom (r2a_rh_shared rh) ∖ hb_shared_s bijb) X !! ps = Some pi →
  ps ∈ (dom (r2a_rh_shared rh) ∖ hb_shared_s bijb) ∧
  (∃ a, rh !! ps = Some (R2AShared a) ∧ ∀ pi', hb_bij bijb !! ps ≠ Some (HBShared pi'))
   ∧ pi ∉ X ∧ is_ProvBlock pi.
Proof.
  move => Hf. move: (Hf) => /fresh_map_is_Block?.
  move: Hf => /(fresh_map_lookup_Some _ _ _ _) [Hd ?].
  move: (Hd) => /elem_of_difference[/elem_of_dom[? /r2a_ih_shared_Some ?]].
  rewrite !elem_of_hb_shared_s => ?. split!; naive_solver.
Qed.
Ltac fresh_map_learn :=
  repeat match goal with
         | H : fresh_map (dom (r2a_rh_shared _) ∖ hb_shared_s _) _ !! _ = Some _ |- _ =>
             learn_hyp (fresh_map_learn _ _ _ _ _ H)
         end.

Definition fresh_or_static (s X : gset prov) :=
    set_to_map (λ p, (p, p)) (filter (λ p, ¬is_ProvBlock p) s)
  ∪ fresh_map s X.

Lemma fresh_or_static_lookup_None s X i :
  fresh_or_static s X !! i = None ↔ i ∉ s.
Proof.
  rewrite lookup_union union_None fresh_map_lookup_None eq_None_not_Some /is_Some.
  setoid_rewrite lookup_set_to_map; last done.
  split; first naive_solver.
  move => H. split! => [[? [? [/elem_of_filter [??] [??]]]]]; by simplify_map_eq.
Qed.

Lemma fresh_or_static_lookup_Some_static s X p p' :
  is_ProvStatic p →
  fresh_or_static s X !! p = Some p' ↔ p = p' ∧ p ∈ s.
Proof.
  move => ?.
  rewrite lookup_union_Some_raw lookup_set_to_map //.
  setoid_rewrite elem_of_filter. destruct p => //.
  split.
  - move => [?|]; [naive_solver|].
    move => [Hs /(fresh_map_lookup_Some _ _ _ _)[??]].
    exfalso. apply: eq_None_ne_Some_1; [done|].
    rewrite lookup_set_to_map //. split!. rewrite elem_of_filter. split!.
    naive_solver.
  - move => [??]. simplify_eq. left. split!. naive_solver.
Qed.

Lemma fresh_or_static_learn rh bijb (X : gset prov) ps pi:
  fresh_or_static (dom (r2a_rh_shared rh) ∖ hb_shared_s bijb) X !! ps = Some pi →
  (∃ a, rh !! ps = Some (R2AShared a) ∧ ∀ pi', hb_bij bijb !! ps ≠ Some (HBShared pi')) ∧
  (if bool_decide (is_ProvBlock pi) then pi ∉ X else ps = pi).
Proof.
  rewrite lookup_union union_Some lookup_set_to_map // => [[[p [/elem_of_filter [H1 H2] [<-<-]]]|[?]]].
  - rewrite elem_of_difference /hb_shared_s not_elem_of_dom elem_of_dom /is_Some in H2.
    setoid_rewrite lookup_omap_Some in H2. destruct H2 as [[? [[] []]] Hbij]; last done. split!. 2: by case_bool_decide.
    rewrite lookup_omap in Hbij.
    move => ? Heq. rewrite Heq // in Hbij.
  - move => H. fresh_map_learn. destruct!. split!. by case_bool_decide.
Qed.
Ltac fresh_or_static_learn :=
  repeat match goal with
         | H : fresh_or_static (dom (r2a_rh_shared _) ∖ hb_shared_s _) _ !! _ = Some _ |- _ =>
             learn_hyp (fresh_or_static_learn _ _ _ _ _ H)
         end.

Lemma fresh_or_static_bij s X i1 i2 j :
  fresh_or_static s X !! i1 = Some j →
  fresh_or_static s X !! i2 = Some j →
  i1 = i2.
Proof.
  rewrite !lookup_union !union_Some !lookup_set_to_map //.
  move => ??. destruct!.
  + done.
  + apply fresh_map_is_Block in H2.
    by apply elem_of_filter in H as [? ?].
  + apply fresh_map_is_Block in H0.
    by apply elem_of_filter in H1 as [? ?].
  + by eapply fresh_map_bij.
Qed.

Lemma fresh_or_static_same_kind s X ps pi :
  fresh_or_static s X !! ps = Some pi → same_prov_kind pi ps.
Proof.
  rewrite lookup_union union_Some !lookup_set_to_map // => [[]].
  - move => [p [? [<-<-]]]. by destruct p.
  - rewrite eq_None_not_Some /is_Some.
    setoid_rewrite lookup_set_to_map => //.
    setoid_rewrite elem_of_filter => [[H H']].
    apply fresh_map_is_Block in H' as ?.
    apply fresh_map_lookup_Some in H' as [].
    destruct pi; last done.
    destruct ps; first done.
    exfalso. apply H. now split!.
Qed.
Global Typeclasses Opaque fresh_or_static.
Global Opaque fresh_or_static.

Definition r2a_combine_heap_bij_bij (X : gset prov) (rh : gmap prov rec_to_asm_elem) (bijb : heap_bij) :=
  (HBShared <$> (hb_shared bijb ∪ fresh_or_static ((dom (r2a_rh_shared rh)) ∖ hb_shared_s bijb) X)) ∪
  (HBConstant <$> r2a_rh_constant rh).

Lemma r2a_combine_heap_bij_bij_shared X bijb ps pi rh:
  r2a_combine_heap_bij_bij X rh bijb !! ps = Some (HBShared pi) ↔
    hb_bij bijb !! ps = Some (HBShared pi) ∨
    fresh_or_static ((dom (r2a_rh_shared rh)) ∖ hb_shared_s bijb) X !! ps = Some pi.
Proof.
  (* TODO: Why is the lock necessary? *)
  rewrite /r2a_combine_heap_bij_bij (lock fresh_or_static) !lookup_union_Some_raw ?lookup_union_None !lookup_fmap.
  unlock.
  rewrite !fmap_None !fmap_Some.
  setoid_rewrite r2a_rh_constant_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_union_None.
  setoid_rewrite hb_shared_lookup_Some.
  setoid_rewrite hb_shared_lookup_None.
  split => ?; destruct!/=.
  - naive_solver.
  - naive_solver.
  - left. split!. naive_solver.
  - fresh_or_static_learn. destruct!. left. split!. naive_solver.
Qed.

Lemma r2a_combine_heap_bij_bij_priv_s X bijb ps rh h:
  r2a_combine_heap_bij_bij X rh bijb !! ps = Some (HBConstant h) ↔
    rh !! ps = Some (R2AConstant h) ∧ ps ∉ hb_shared_s bijb.
Proof.
  rewrite /r2a_combine_heap_bij_bij !lookup_union_Some_raw ?lookup_union_None !lookup_fmap.
  rewrite elem_of_hb_shared_s.
  rewrite !fmap_None !fmap_Some.
  setoid_rewrite r2a_rh_constant_Some.
  setoid_rewrite lookup_union_Some_raw.
  setoid_rewrite lookup_union_None.
  setoid_rewrite hb_shared_lookup_Some.
  setoid_rewrite hb_shared_lookup_None.
  split => ?; destruct!/=.
  - naive_solver.
  - right. split!. 1: naive_solver. apply fresh_or_static_lookup_None.
    apply not_elem_of_difference. left. move => /elem_of_dom[? /r2a_ih_shared_Some ?]. naive_solver.
Qed.

Definition r2a_shared_statics (rh : gmap prov rec_to_asm_elem) (bijb : heap_bij) : gset prov :=
  filter is_ProvStatic (dom (r2a_rh_shared rh) ∖ hb_shared_s bijb).

Lemma r2a_shared_statics_in rh bijb p :
  p ∈ r2a_shared_statics rh bijb ↔
    ∃ a, is_ProvStatic p ∧ rh !! p = Some (R2AShared a) ∧ p ∉ hb_shared_s bijb.
Proof.
  rewrite /r2a_shared_statics elem_of_filter elem_of_difference elem_of_dom /is_Some.
  setoid_rewrite r2a_ih_shared_Some. naive_solver.
Qed.

Program Definition r2a_combine_heap_bij (X : gset prov) (rh : gmap prov rec_to_asm_elem) (bijb : heap_bij)
 (H1 : hb_provs_i bijb ⊆ X) : heap_bij :=
  HeapBij (r2a_combine_heap_bij_bij X rh bijb) (filter (λ p, p.1 ∉ r2a_shared_statics rh bijb) (hb_priv_i bijb)) _ _ _.
Next Obligation.
  move => X rh bijb HX ps pi.
  rewrite !r2a_combine_heap_bij_bij_shared // => -[/hb_disj ?|?].
  { apply map_lookup_filter_None_2. by left. }
  apply eq_None_ne_Some => ? /map_lookup_filter_Some[? Hnin].
  have : (pi ∈ hb_provs_i bijb) by rewrite elem_of_hb_provs_i; naive_solver.
  fresh_or_static_learn. destruct!. case_bool_decide; [set_solver| ].
  move => ?. simplify_eq. eapply Hnin => /=. apply r2a_shared_statics_in.
  split!. 1: by destruct pi. move => /elem_of_hb_shared_s. naive_solver.
Qed.
Next Obligation.
  move => X rh bijb HX pi ps ps'.
  rewrite !r2a_combine_heap_bij_bij_shared => H1 H2.
  destruct!; simplify_bij.
  - done.
  - fresh_or_static_learn. destruct!. case_bool_decide.
    + move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
    + simplify_eq. exploit hb_shared_static_eq_i => //. by destruct pi.
  - fresh_or_static_learn. destruct!. case_bool_decide.
    + move: (HX pi). rewrite elem_of_hb_provs_i. naive_solver.
    + simplify_eq. exploit hb_shared_static_eq_i => //. by destruct pi.
  - by eapply fresh_or_static_bij.
Qed.
Next Obligation.
  move => X rh bijb HX ps pi.
  rewrite !r2a_combine_heap_bij_bij_shared => [[H|]].
  - by eapply hb_shared_prov.
  - move => ?. by apply: fresh_or_static_same_kind.
Qed.

Definition r2a_combine_r2a (X : gset prov) (rh : gmap prov rec_to_asm_elem) (bijb : heap_bij) : gmap prov Z :=
  list_to_map $
   omap (λ '(ps, pi), if rh !! ps is Some (R2AShared a) then Some (pi : prov, a) else None) $
    map_to_list (fresh_or_static ((dom (r2a_rh_shared rh)) ∖ hb_shared_s bijb) X).

Lemma r2a_combine_r2a_Some X rh bijb p a:
  r2a_combine_r2a X rh bijb !! p = Some a ↔
    ∃ ps, fresh_or_static ((dom (r2a_rh_shared rh)) ∖ hb_shared_s bijb) X !! ps = Some p
          ∧ rh !! ps = Some (R2AShared a).
Proof.
  rewrite /r2a_combine_r2a. rewrite -elem_of_list_to_map. 2: {
    rewrite list_fmap_omap. apply: NoDup_omap_2_strong; [|apply NoDup_map_to_list].
    move => [??] [??] ? /elem_of_map_to_list? /elem_of_map_to_list? /= /fmap_Some[?[??]] /fmap_Some[?[??]].
    repeat case_match => //. simplify_eq/=. f_equal. by apply: fresh_or_static_bij.
  }
  rewrite elem_of_list_omap.
  split => ?; destruct!.
  - repeat case_match => //. simplify_eq/=. revert select (_ ∈ map_to_list _) => /elem_of_map_to_list. naive_solver.
  - eexists (_, _). simplify_option_eq. split!. by apply elem_of_map_to_list.
Qed.

Lemma r2a_combine_extend (X : gset prov) rha bijb rh ho hb hsn :
  r2a_combine_bij (r2a_rh_shared rha) bijb ⊆ r2a_rh_shared rh →
  ho ⊆ r2a_rh_constant rh →
  ho ⊆ r2a_combine_priv (r2a_rh_shared rha) bijb hb →
  r2a_combine_priv_shared (r2a_rh_shared rha) bijb hb ⊆ ho →
  dom rha ⊆ X →
  hb_provs_i bijb ⊆ X →
  R2AConstant <$> hsn ⊆ rha →
  dom hsn = r2a_shared_statics rh bijb →
  (* rh' : newly shared blocks, bijb': new heap bijection  *)
  ∃ rh' bijb',
    r2a_rh_shared rh = r2a_combine_bij (rh' ∪ r2a_rh_shared rha) bijb' ∧
    r2a_rh_constant rh = r2a_combine_priv (rh' ∪ r2a_rh_shared rha) bijb' hb ∧
    dom rh' ## X ∖ dom (R2AConstant <$> hsn) ∧
    hb_shared bijb ⊆ hb_shared bijb' ∧
    hb_priv_i bijb ∖ hsn = hb_priv_i bijb' ∧
    (* The following is a random collection of semi-redundant
    properties that are used by the later proof. TODO: clean this up *)
    (R2AShared <$> rh') ##ₘ rha ∖ (R2AConstant <$> hsn) ∧
    dom (hb_bij bijb') ⊆ dom rh ∧
    (r2a_rh_constant rh ∖ (hb_priv_s bijb' ∖ ho)) = ho ∧
    ho ∖ (ho ∖ hb_priv_s bijb) ⊆ hb_priv_s bijb' ∧
    (hb_priv_s bijb' ∖ (ho ∖ (ho ∖ hb_priv_s bijb))) = hb_priv_s bijb' ∖ ho ∧
    dom rh' ⊆ hb_shared_i bijb' ∧
    dom hsn ⊆ hb_shared_s bijb' ∧
    (∀ p2 p1, hb_bij bijb' !! p2 = Some (HBShared p1) →
              p1 ∉ dom (rh' ∪ r2a_rh_shared rha) →
              hb_bij bijb !! p2 = Some (HBShared p1))
.
Proof.
  move => Hcombine Hho Hho2 Hpriv HXa HXb Hsr Hhsn.
  have HhsnNone : ∀ i, hsn !! i = None ↔ ¬ (∃ a : Z, is_ProvStatic i ∧ rh !! i = Some (R2AShared a) ∧ i ∉ hb_shared_s bijb). {
    move => i. by rewrite -not_elem_of_dom Hhsn r2a_shared_statics_in.
  }
  have HhsnSome : ∀ i x, hsn !! i = Some x → (∃ a : Z, is_ProvStatic i ∧ rh !! i = Some (R2AShared a) ∧ i ∉ hb_shared_s bijb). {
    move => i x. move => /(elem_of_dom_2 _ _ _).
    by rewrite Hhsn r2a_shared_statics_in.
  }
  have Hdisj : (R2AShared <$> (r2a_combine_r2a X rh bijb)) ##ₘ rha ∖ (R2AConstant <$> hsn). {
    apply map_disjoint_spec => p ??. rewrite lookup_fmap => /fmap_Some [?[/r2a_combine_r2a_Some[?[??]]?]] /lookup_difference_Some [? Hn].
    fresh_or_static_learn. destruct!. case_bool_decide; simplify_eq.
    - revert select (_ ∉ X). apply. apply HXa. by apply elem_of_dom.
    - move: Hn. rewrite lookup_fmap. move => /fmap_None/HhsnNone. apply.
      split!. 1: by destruct p. rewrite elem_of_hb_shared_s. naive_solver.
  }
  have Hdisj2 : dom (r2a_combine_priv_shared (r2a_rh_shared rha) bijb hb) ## dom (r2a_rh_shared rh). {
    apply: disjoint_mono; [|by apply: subseteq_dom|done].
    apply: disjoint_mono; [|by apply: subseteq_dom; apply Hho|done].
    apply elem_of_disjoint => ? /elem_of_dom[? /r2a_rh_constant_Some ?] /elem_of_dom[? /r2a_ih_shared_Some ?].
    naive_solver.
  }
  have Hrev: ∀ ps pi b,
      rh !! ps = Some (R2AConstant b) →
      hb_bij bijb !! ps = Some (HBShared pi) →
      r2a_rh_shared rha !! pi = None ∧ b = h_block hb ps. {
    move => ps pi b Hih Hbij.
    destruct (r2a_rh_shared rha !! pi) as [a|] eqn: Hiha.
    - exfalso. have : r2a_rh_shared rh !! ps = Some a.
      { apply: lookup_weaken; [|done]. apply r2a_combine_bij_lookup_Some. naive_solver. }
      rewrite r2a_ih_shared_Some. naive_solver.
    - split!. have : rh !! ps = Some (R2AConstant (h_block hb ps)); [|naive_solver].
      rewrite -r2a_rh_constant_Some. apply: lookup_weaken; [|done]. apply: lookup_weaken; [|done].
      rewrite r2a_combine_priv_shared_Some. naive_solver.
  }

  eexists (r2a_combine_r2a X rh bijb).
  eexists (r2a_combine_heap_bij (X ∪ dom (hb_priv_s bijb)) rh bijb HXb).
  split_and!.
  - apply map_eq => ps. apply option_eq => a. rewrite r2a_ih_shared_Some.
    rewrite r2a_combine_bij_lookup_Some /=.
    setoid_rewrite r2a_combine_heap_bij_bij_shared.
    setoid_rewrite (lookup_union_Some _ (r2a_rh_shared rha)). 2: {
     apply (map_disjoint_fmap R2AShared R2AShared).
     eapply map_disjoint_weaken_r; [done|].
     apply map_subseteq_difference_r; [apply r2a_rh_shared_fmap_l|].
     apply map_disjoint_spec => ??? /lookup_fmap_Some[?[?/r2a_ih_shared_Some ?]] Hc.
     exploit @lookup_weaken; [done..|]. move: Hc => /lookup_fmap_Some. naive_solver.
    }
    setoid_rewrite r2a_combine_r2a_Some.
    setoid_rewrite r2a_ih_shared_Some.
    split => ?.
    + destruct (hb_shared bijb !! ps) as [pi|] eqn:Hps.
      * move: Hps => /hb_shared_lookup_Some Hps. eexists _. split; [by left|].
        split!.
        destruct (r2a_rh_shared rha !! pi) as [a'|] eqn:Heq.
        -- right. have : r2a_rh_shared rh !! ps = Some a'. {
             apply: lookup_weaken; [|done]. apply r2a_combine_bij_lookup_Some. naive_solver.
           }
           rewrite r2a_ih_shared_Some. rewrite r2a_ih_shared_Some in Heq. naive_solver.
        -- exfalso. move: Hdisj2 => /elem_of_disjoint. apply.
           ++ apply elem_of_dom. eexists _.
              rewrite r2a_combine_priv_shared_Some. naive_solver.
           ++ apply elem_of_dom. eexists _. by apply r2a_ih_shared_Some.
      * have [??]: is_Some (fresh_or_static (dom (r2a_rh_shared rh) ∖ hb_shared_s bijb) X !! ps). {
          apply not_eq_None_Some. rewrite fresh_or_static_lookup_None. apply. apply elem_of_difference.
          split.
          - apply elem_of_dom. eexists _. by apply r2a_ih_shared_Some.
          - rewrite elem_of_hb_shared_s. rewrite hb_shared_lookup_None in Hps. naive_solver.
        }
        eexists _.
        split; [by right|]. left. naive_solver.
    + destruct!.
      * fresh_or_static_learn. destruct!. case_bool_decide.
        -- exfalso. revert select (_ ∉ X). apply. apply HXb.
           apply elem_of_hb_provs_i. naive_solver.
        -- simplify_eq. exploit hb_shared_static_eq_i; [done|by destruct p'|].
           naive_solver.
      * have : ps = ps0; [|naive_solver]. by apply: fresh_or_static_bij.
      * rewrite -r2a_ih_shared_Some. apply: lookup_weaken; [|done].
        apply r2a_combine_bij_lookup_Some. split!. by apply r2a_ih_shared_Some.
      * fresh_or_static_learn. destruct!. case_bool_decide.
        -- exfalso. select (_ ∉ _) (fun H => apply H).
           enough (p' ∈ X). { revert select (p' ∈ X). clear. set_solver. }
           apply HXa. by apply elem_of_dom.
        -- simplify_eq.
           have : p' ∈ r2a_shared_statics rh bijb. {
             apply r2a_shared_statics_in. setoid_rewrite elem_of_hb_shared_s.
             destruct p'; naive_solver. }
           rewrite -Hhsn. move => /elem_of_dom[??].
           rewrite map_subseteq_spec in Hsr.
           exploit Hsr. { apply lookup_fmap_Some. naive_solver. }
           naive_solver.
  - apply map_eq => ps. apply option_eq => b. rewrite r2a_rh_constant_Some r2a_combine_priv_Some /=.
    setoid_rewrite r2a_combine_heap_bij_bij_priv_s.
    setoid_rewrite r2a_combine_heap_bij_bij_shared.
    setoid_rewrite lookup_union_None.
    split => ?; destruct!.
    + destruct (decide (ps ∈ hb_shared_s bijb)) as [[pi ?]%elem_of_hb_shared_s|]. 2: naive_solver.
      right.
      opose proof* Hrev; [done..|]. destruct!.
      eexists _. split_and!; [by left | |done|done].
      apply eq_None_ne_Some => ?. rewrite r2a_combine_r2a_Some => ?. destruct!.
      fresh_or_static_learn. destruct!. case_bool_decide.
      * simplify_eq. revert select (_ ∉ X). apply. apply HXb.
        rewrite elem_of_hb_provs_i. naive_solver.
      * simplify_eq. exploit hb_shared_static_eq_i; [done|by destruct pi|].
        naive_solver.
    + naive_solver.
    + rewrite -r2a_rh_constant_Some. apply: lookup_weaken; [|done]. apply: lookup_weaken; [|done].
      rewrite r2a_combine_priv_shared_Some. naive_solver.
    + fresh_or_static_learn. destruct!.
      exfalso. revert select (r2a_combine_r2a _ _ _ !! _ = None). apply not_eq_None_Some.
      eexists _. apply r2a_combine_r2a_Some. naive_solver.
  - apply elem_of_disjoint => p /elem_of_dom [? /r2a_combine_r2a_Some ?]. destruct!.
    fresh_or_static_learn. destruct!. rewrite dom_fmap_L Hhsn.
    move => /elem_of_difference[? /r2a_shared_statics_in].
    case_bool_decide; [naive_solver|]. simplify_eq. apply.
    split!; [by destruct p|]. rewrite elem_of_hb_shared_s. naive_solver.
  - apply map_subseteq_spec => ??. rewrite !hb_shared_lookup_Some /= r2a_combine_heap_bij_bij_shared. naive_solver.
  - simpl. apply map_eq => p. apply option_eq => h.
    by rewrite lookup_difference_Some map_lookup_filter_Some /= -not_elem_of_dom Hhsn.
  - done.
  - move => ps /elem_of_dom /=[][pi|?].
    + move => /r2a_combine_heap_bij_bij_shared[|].
      * move => ?. rewrite -(r2a_rh_shared_constant rh). rewrite dom_union_L !dom_fmap elem_of_union !elem_of_dom.
        destruct (r2a_rh_shared rha !! pi) eqn:Heq.
        -- left. apply: lookup_weaken_is_Some; [|done]. eexists _. apply r2a_combine_bij_lookup_Some. naive_solver.
        -- right. apply: lookup_weaken_is_Some; [|done]. apply: lookup_weaken_is_Some; [|done].
           eexists _. apply r2a_combine_priv_shared_Some. naive_solver.
      * move => ?. fresh_or_static_learn. destruct!. by apply elem_of_dom.
    + move => /r2a_combine_heap_bij_bij_priv_s[??]. by apply elem_of_dom.
  - apply map_eq => ps. apply option_eq => b.
    rewrite lookup_difference_Some lookup_difference_None hb_priv_s_lookup_None r2a_rh_constant_Some /=.
    setoid_rewrite r2a_combine_heap_bij_bij_priv_s.
    split => ?; destruct!.
    + destruct (decide (ps ∈ hb_shared_s bijb)) as [[pi ?]%elem_of_hb_shared_s|]. 2: naive_solver.
      enough (is_Some (ho !! ps)) as [b' ?]. {
        have /r2a_rh_constant_Some : r2a_rh_constant rh !! ps = Some b' by apply: lookup_weaken.
        naive_solver.
      }
      apply: lookup_weaken_is_Some; [|done]. eexists _.
      apply r2a_combine_priv_shared_Some.
      split!. apply eq_None_ne_Some_2 => a ?.
      enough (r2a_rh_shared rh !! ps = Some a) as ?%r2a_ih_shared_Some by naive_solver.
      apply: lookup_weaken; [|done]. apply r2a_combine_bij_lookup_Some. naive_solver.
    + revert select (is_Some _) => -[b' ?].
      have /r2a_rh_constant_Some : r2a_rh_constant rh !! ps = Some b' by apply: lookup_weaken.
      naive_solver.
    + split; [|naive_solver]. apply r2a_rh_constant_Some. by apply: lookup_weaken.
  - apply map_subseteq_spec => ??.
    rewrite hb_priv_s_lookup_Some /= r2a_combine_heap_bij_bij_priv_s.
    rewrite lookup_difference_Some lookup_difference_None /is_Some.
    setoid_rewrite hb_priv_s_lookup_Some. rewrite elem_of_hb_shared_s.
    move => ?. destruct!. split; [|naive_solver].
    rewrite -r2a_rh_constant_Some. by apply: lookup_weaken.
  - apply map_eq => i. apply option_eq => ?.
    rewrite !(lookup_difference_Some, lookup_difference_None, hb_priv_s_lookup_Some) /= /is_Some.
    rewrite !r2a_combine_heap_bij_bij_priv_s elem_of_hb_shared_s.
    setoid_rewrite lookup_difference_Some.
    setoid_rewrite hb_priv_s_lookup_None.
    split => ?; destruct!.
    + done.
    + have [?]: is_Some (r2a_combine_priv (r2a_rh_shared rha) bijb hb !! i) by apply: lookup_weaken_is_Some.
      rewrite r2a_combine_priv_Some. naive_solver.
    + naive_solver.
  - move => ? /elem_of_dom[? /r2a_combine_r2a_Some[??]]. apply elem_of_hb_shared_i => /=.
    eexists _. apply r2a_combine_heap_bij_bij_shared. naive_solver.
  - rewrite Hhsn. move => ? /r2a_shared_statics_in[?[?[??]]].
    apply elem_of_hb_shared_s => /=. eexists _.
    apply r2a_combine_heap_bij_bij_shared. right.
    apply fresh_or_static_lookup_Some_static; [done|]. split!.
    rewrite elem_of_difference. rewrite elem_of_dom /is_Some.
    setoid_rewrite r2a_ih_shared_Some. naive_solver.
  - move => ?? /= /r2a_combine_heap_bij_bij_shared[//|?] Hnotin. exfalso. apply Hnotin.
    rewrite dom_union_L elem_of_union !elem_of_dom /is_Some.
    setoid_rewrite r2a_combine_r2a_Some. fresh_or_static_learn. naive_solver.
Qed.

(** ** unowned statics *)
Definition r2a_unowned_statics (h : heap_state) (bijb bijb' : heap_bij) : gmap prov (gmap Z val) :=
  (map_imap (λ p _, Some (h_block h p))
        (gset_to_gmap (ProvBlock inhabitant)
           ((filter is_ProvStatic (dom (hb_bij bijb))) ∖ dom (hb_bij bijb')))).

Lemma r2a_unowned_statics_lookup_Some h bijb bijb' p b :
  r2a_unowned_statics h bijb bijb' !! p = Some b ↔
   is_ProvStatic p ∧ b = h_block h p ∧
       p ∈ dom (hb_bij bijb) ∧ p ∉ dom (hb_bij bijb').
Proof.
  rewrite map_lookup_imap. rewrite bind_Some.
  setoid_rewrite lookup_gset_to_gmap_Some.
  setoid_rewrite elem_of_difference.
  setoid_rewrite elem_of_filter. naive_solver.
Qed.

Lemma r2a_unowned_statics_disj h bijb bijb' rha' :
  R2AConstant <$> r2a_unowned_statics h bijb bijb' ##ₘ
      (R2AShared <$> r2a_combine_bij (r2a_rh_shared rha') bijb') ∪
      (R2AConstant <$> r2a_combine_priv (r2a_rh_shared rha') bijb' h).
Proof.
  apply map_disjoint_spec => p x y.
  move => /lookup_fmap_Some[? [? ]] /r2a_unowned_statics_lookup_Some[?[?[? /not_elem_of_dom?]]].
  move => /lookup_union_Some_raw[|].
  - move => /lookup_fmap_Some[? [? ]] /r2a_combine_bij_lookup_Some. naive_solver.
  - move => [? ] /lookup_fmap_Some[? [? ]] /r2a_combine_priv_Some. naive_solver.
Qed.

(** * mem_transfer *)
Lemma r2a_mem_transfer mem m1 m2 P1 P2:
  satisfiable (r2a_mem_auth mem ∗ r2a_mem_map m1 ∗ r2a_mem_map m2 ∗ P1) →
  satisfiable (r2a_mem_map (mem ∖ m1) ∗ P2) →
    satisfiable (r2a_mem_auth mem ∗ r2a_mem_map (m2 ∪ m1) ∗ P1) ∧
    satisfiable (r2a_mem_map m2 ∗ r2a_mem_map (mem ∖ (m2 ∪ m1)) ∗ P2).
Proof.
  move => Hs1 Hs2.
  iSatStart Hs1. iIntros "(Hauth&Hm1&Hm2&?)".
  iDestruct (r2a_mem_lookup_big' with "Hauth Hm1") as %?.
  iDestruct (r2a_mem_lookup_big' with "Hauth Hm2") as %?.
  iDestruct (r2a_mem_map_excl with "Hm1 Hm2") as %?.
  iSatStop Hs1. split.
  - iSatMono Hs1. iFrame. rewrite /r2a_mem_map big_sepM_union; [by iFrame|done].
  - iSatMono Hs2. iIntros "(Hmem&$)".
    rewrite -(map_difference_union m2 (mem ∖ m1)). 2: {
      apply map_subseteq_spec => ???. apply lookup_difference_Some.
      split; [by apply: lookup_weaken| by apply: map_disjoint_Some_l].
    }
    rewrite /r2a_mem_map big_sepM_union; [|by apply map_disjoint_difference_r'].
    by rewrite map_difference_difference map_union_comm.
Qed.

Ltac r2a_mem_transfer Hfrom Hto :=
  let H := fresh in
  opose proof* r2a_mem_transfer as H;
  [ | iSatMono Hto; iIntros!; iFrame; by iAccu |];
  [ iSatMono Hfrom; iIntros!; iFrame; by iAccu | ];
  clear Hfrom Hto; destruct H as [Hfrom Hto].

(** * pure versions *)
(** ** rec to asm *)
(** *** r2a_val_rel_pure *)
Definition r2a_val_rel_pure (f2i : gmap string Z) (rh : gmap prov Z) (iv : val) (av : Z) : Prop :=
  match iv with
  | ValNum z => av = z
  | ValBool b => av = bool_to_Z b
  | ValFn f => f2i !! f = Some av
  | ValLoc l => ∃ z, av = (z + l.2)%Z ∧ rh !! l.1 = Some z
  end.

Lemma r2a_val_rel_to_pure f2i v av rh :
  r2a_f2i_full f2i -∗
  r2a_heap_auth rh -∗
  r2a_val_rel v av -∗
  ⌜r2a_val_rel_pure f2i (r2a_rh_shared rh) v av⌝.
Proof.
  iIntros "Hf2i Hh Hv". destruct v => //=.
  - iApply (r2a_f2i_full_singleton with "[$] [$]").
  - iDestruct!.
    iDestruct (r2a_heap_shared_lookup' with "[$] [$]") as %?.
    iPureIntro. setoid_rewrite r2a_ih_shared_Some. naive_solver.
Qed.

Lemma r2a_val_rel_of_pure f2i rh v av :
  r2a_val_rel_pure f2i rh v av →
  r2a_f2i_full f2i -∗
  ([∗ map] p↦a ∈ rh, r2a_heap_shared p a) -∗
  r2a_val_rel v av.
Proof.
  iIntros (Hv) "Hf2i Hsh". destruct v => //=; destruct!/=.
  - by iApply r2a_f2i_full_to_singleton.
  - iSplit!; [done|]. by iApply (big_sepM_lookup with "[$]").
Qed.

Lemma r2a_val_rel_pure_through_bij f2i iv av rh1 rh2 bij:
  r2a_val_rel_pure f2i rh1 iv av →
  rh1 = r2a_combine_bij rh2 bij →
  r2a_val_rel_pure f2i rh2 (val_through_bij bij iv) av.
Proof.
  move => Hp ?. subst. destruct iv => //; simplify_eq/=.
  move: Hp => [? [? /r2a_combine_bij_lookup_Some[?[??]]]]. simplify_map_eq.
  naive_solver.
Qed.

Lemma r2a_val_rel_big_to_pure f2i vs avs rh :
  r2a_f2i_full f2i -∗
  r2a_heap_auth rh -∗
  ([∗ list] v;av∈vs;avs, r2a_val_rel v av) -∗
  ⌜Forall2 (r2a_val_rel_pure f2i (r2a_rh_shared rh)) vs avs⌝.
Proof.
  iIntros "Hf2i Hh Hv".
  iDestruct (big_sepL2_length with "[$]") as %?.
  iApply bi.pure_mono; [by apply Forall2_same_length_lookup_2|].
  iIntros (?????). iApply (r2a_val_rel_to_pure with "[$] [$]").
  by iApply (big_sepL2_lookup with "Hv").
Qed.

Lemma r2a_val_rel_big_of_pure f2i rh vs avs :
  Forall2 (r2a_val_rel_pure f2i rh) vs avs →
  r2a_f2i_full f2i -∗
  ([∗ map] p↦a ∈ rh, r2a_heap_shared p a) -∗
  ([∗ list] v;av∈vs;avs, r2a_val_rel v av).
Proof.
  iIntros (Hall) "#Hf2i #Hsh". iInduction Hall as [] "IH"; [done|].
  iFrame "#". by iApply r2a_val_rel_of_pure.
Qed.

Lemma r2a_val_rel_big_through_bij f2i vs avs rh1 rh2 bij :
  Forall2 (r2a_val_rel_pure f2i rh1) vs avs →
  rh1 = r2a_combine_bij rh2 bij →
  r2a_f2i_full f2i -∗
  ([∗ map] p↦a ∈ rh2, r2a_heap_shared p a) -∗
  [∗ list] v;av ∈ (val_through_bij bij <$> vs);avs, r2a_val_rel v av.
Proof.
  iIntros (Hall ?) "#Hf2i #Hih2". subst.
  rewrite big_sepL2_fmap_l. iApply big_sepL2_intro. { by apply: Forall2_length. }
  iIntros "!>" (? v ???).
  iApply (r2a_val_rel_of_pure with "Hf2i Hih2"). apply: r2a_val_rel_pure_through_bij; [|done].
  by apply: Forall2_lookup_lr.
Qed.

(** *** r2a_heap_shared_agree_pure *)
Definition r2a_heap_shared_agree_pure (f2i : gmap string Z) (h : gmap loc val) (rh : gmap prov Z) (mem : gmap Z (option Z)) : Prop :=
  ∃ m2l : gmap Z loc,
  map_Forall (λ l v,
               if rh !! l.1 is Some a then
                 ∃ av, r2a_val_rel_pure f2i rh v av ∧ mem !! (a + l.2) = Some (Some av) ∧ m2l !! (a + l.2) = Some l
               else True
  ) h.


Lemma r2a_heap_shared_agree_to_pure f2i h rh :
  r2a_f2i_full f2i -∗
  r2a_heap_shared_agree h rh -∗
  r2a_heap_auth rh -∗
  ∃ m, ⌜r2a_heap_shared_agree_pure f2i h (r2a_rh_shared rh) m⌝ ∗ r2a_mem_map m ∗ r2a_heap_auth rh.
Proof.
  iIntros "#Hf2i Hag Hauth".
  iInduction h as [|l v h ?] "IH" using map_ind.
  { iExists ∅. iFrame. rewrite /r2a_mem_map big_sepM_empty. iSplit!. eexists ∅ => ?? //. }
  rewrite /r2a_heap_shared_agree big_sepM_insert //. iDestruct "Hag" as "[??]".
  iDestruct ("IH" with "[$] [$]") as (? [m2l Hag]) "[Hm Hauth]". iClear "IH".
  destruct ((r2a_rh_shared rh) !! l.1) as [a|] eqn: Hl. 2: {
    iExists _. iFrame. iPureIntro. eexists m2l.
    move => ?? /lookup_insert_Some[[??]|[??]]; simplify_option_eq => //. by apply Hag.
  }
  move: Hl => /r2a_ih_shared_Some Hl. simplify_option_eq.
  iDestruct!. iDestruct (r2a_val_rel_to_pure with "[$] [$] [$]") as %?.
  iDestruct (r2a_mem_map_constant_excl with "[$] [$]") as %?.
  iExists (<[a + l.2 := Some av]>m). rewrite /r2a_mem_map big_sepM_insert //. iFrame. iPureIntro.
  eexists (<[a + l.2 := l]>m2l). move => ?? /lookup_insert_Some[[??]|[??]]; simplify_eq.
  + move: Hl => /r2a_ih_shared_Some ->. split!; simplify_map_eq; done.
  + case_match => //. have := Hag _ _ ltac:(done). simplify_option_eq => ?. destruct!.
    rewrite !lookup_insert_ne; [|move => Heq; rewrite ->Heq in *; naive_solver..]. naive_solver.
Qed.

Lemma r2a_heap_shared_agree_of_pure f2i rh h m :
  r2a_heap_shared_agree_pure f2i h (r2a_rh_shared rh) m →
  r2a_f2i_full f2i -∗
  ([∗ map] p↦a ∈ r2a_rh_shared rh, r2a_heap_shared p a) -∗
  r2a_mem_map m -∗
  r2a_heap_shared_agree h rh.
Proof.
  iIntros (Hag) "#Hf2i #Hsh Hm".
  iInduction h as [|l v h Hl] "IH" using map_ind forall (m Hag). { by iApply big_sepM_empty. }
  move: Hag => [m2l /map_Forall_insert [//|? Hag]].
  iApply big_sepM_insert; [done|].
  case_match eqn: Heq; destruct!; rewrite ?r2a_ih_shared_Some ?r2a_rh_shared_None in Heq; simplify_option_eq.
  - erewrite <-(insert_delete m); [|done].
    iDestruct (big_sepM_insert with "Hm") as "[Ha Hm]". { by simplify_map_eq. }
    iSplitL "Ha".
    + iSplit!; [|done]. by iApply r2a_val_rel_of_pure.
    + iApply ("IH" with "[] Hm"). iPureIntro. eexists m2l. move => l' v' Hl'.
      have := (Hag l' v' ltac:(done)). case_match => // ?. destruct!. split!; [done|].
      apply lookup_delete_Some. split!. move => Hx. rewrite <-Hx in *. simplify_option_eq.
      by rewrite Hl in Hl'.
  - iSplitR.
    + do 2 case_match => //. naive_solver.
    + iApply ("IH" with "[%] Hm"). by eexists _.
Qed.

Lemma r2a_heap_shared_agree_pure_lookup f2i l v rh h m :
  r2a_heap_shared_agree_pure f2i h rh m →
  h !! l = Some v →
  is_Some (rh !! l.1) →
  ∃ a, r2a_val_rel_pure f2i rh v a.
Proof. move => [? Hag] Hl [??]. have := Hag _ _ ltac:(done). simplify_option_eq. naive_solver. Qed.

Lemma r2a_heap_shared_agree_pure_impl f f2i rh1 h1 rh2 h2 m :
  r2a_heap_shared_agree_pure f2i h1 rh1 m →
  (∀ l2 v2 a, h2 !! l2 = Some v2 → rh2 !! l2.1 = Some a →
    ∃ p1 v1, f p1 = Some l2.1 ∧ h1 !! (p1, l2.2) = Some v1 ∧ rh1 !! p1 = Some a ∧
               (∀ av, r2a_val_rel_pure f2i rh1 v1 av → r2a_val_rel_pure f2i rh2 v2 av)) →
  r2a_heap_shared_agree_pure f2i h2 rh2 m.
Proof.
  move => [m2l Hh] Himpl.
  eexists (omap (λ x, (λ y, (y, x.2)) <$> f x.1) m2l). move => l2 v2 ?. case_match => //.
  have [?[?[?[?[? Hvr]]]]]:= Himpl _ _ _ ltac:(done) ltac:(done).
  have := Hh _ _ ltac:(done). simplify_map_eq.
  move => [?[?[??]]]. split!; [by apply: Hvr|].
  simplify_option_eq. by destruct l2.
Qed.

(** ** heap_bij *)
(** *** val_in_bij_pure *)
Definition val_in_bij_pure (bij : heap_bij) (v1 v2 : val) : Prop :=
  match v1, v2 with
  | ValNum n1, ValNum n2 => n1 = n2
  | ValBool b1, ValBool b2 => b1 = b2
  | ValFn f1, ValFn f2 => f1 = f2
  | ValLoc l1, ValLoc l2 => l1.2 = l2.2 ∧ same_prov_kind l1.1 l2.1 ∧ hb_bij bij !! l2.1 = Some (HBShared l1.1)
  | _, _ => False
  end.

Lemma val_in_bij_to_pure bij v1 v2 :
  heap_bij_auth bij -∗
  val_in_bij v1 v2 -∗
  ⌜val_in_bij_pure bij v1 v2⌝.
Proof.
  iIntros "Hh Hv". destruct v1, v2 => //=. unfold loc_in_bij. iDestruct!.
  iDestruct (heap_bij_shared_lookup with "[$] [$]") as %?. done.
Qed.

Lemma val_in_bij_to_pure_big bij vs1 vs2 :
  heap_bij_auth bij -∗
  ([∗ list] v1;v2∈vs1;vs2, val_in_bij v1 v2) -∗
  ⌜Forall2 (val_in_bij_pure bij) vs1 vs2⌝.
Proof.
  iIntros "Hh Hv".
  iInduction vs1 as [|v1 vs1] "IH" forall (vs2).
  { iDestruct (big_sepL2_nil_inv_l with "[$]") as %->. iPureIntro. econs. }
  iDestruct (big_sepL2_cons_inv_l with "[$]") as (???) "[??]". subst.
  iDestruct ("IH" with "[$] [$]") as %?.
  iDestruct (val_in_bij_to_pure with "[$] [$]") as %?.
  iPureIntro. by econs.
Qed.

Lemma val_in_bij_of_pure bij v1 v2 :
  val_in_bij_pure bij v1 v2 →
  ([∗ map]p2↦p1∈hb_shared bij, heap_bij_shared p1 p2) -∗
  val_in_bij v1 v2.
Proof.
  iIntros (Hv) "Hsh". destruct v1, v2 => //=. simplify_eq/=. destruct!.
  do 2 (iSplit; [done|]). iApply (big_sepM_lookup with "[$]"). by apply hb_shared_lookup_Some.
Qed.

(** *** heap_in_bij_pure *)
Definition heap_in_bij_pure (bij : heap_bij) (h h' : heap_state) : Prop :=
  ∀ p1 p2 o,
  hb_bij bij !! p2 = Some (HBShared p1) →

  (is_Some (h.(h_heap) !! (p1, o)) ↔ is_Some (h'.(h_heap) !! (p2, o)))
  ∧
  ∀ v1 v2,
  h.(h_heap)  !! (p1, o) = Some v1 →
  h'.(h_heap) !! (p2, o) = Some v2 →
  val_in_bij_pure bij v1 v2.

Lemma heap_in_bij_to_pure bij h h' :
  heap_bij_auth bij -∗
  heap_in_bij bij h h' -∗
  ⌜heap_in_bij_pure bij h h'⌝.
Proof.
  iIntros "Ha Hh". iIntros (????).
  iDestruct ("Hh" with "[//]") as (?) "Hh".
  iSplit; [done|]. iIntros (????).
  iApply (val_in_bij_to_pure with "[$]"). by iApply "Hh".
Qed.

Lemma heap_in_bij_of_pure bij h h' :
  heap_in_bij_pure bij h h' →
  ([∗ map]p2↦p1∈hb_shared bij, heap_bij_shared p1 p2) -∗
  heap_in_bij bij h h'.
Proof.
  iIntros (Hh) "Hsh". iIntros (p1 p2 o ?).
  move: Hh => /(_ _ _ o ltac:(done))[? {}Hh]. iSplit; [done|].
  iIntros (????). iApply (val_in_bij_of_pure with "[$]"). by apply: Hh.
Qed.

(** ** combining *)
Lemma val_in_through_bij f2i bij v av rh1 rh:
  r2a_val_rel_pure f2i rh1 v av →
  rh1 = r2a_combine_bij rh bij →
  ([∗ map] p2↦p1 ∈ hb_shared bij, heap_bij_shared p1 p2) -∗
  val_in_bij (val_through_bij bij v) v.
Proof.
  iIntros (Hp ?) "Hbij". destruct v => //; simplify_eq/=.
  move: Hp => [?[? /r2a_combine_bij_lookup_Some [?[??]]]]. simplify_map_eq.
  unfold loc_in_bij. iSplit!. { by eapply hb_shared_prov. }
  iApply (big_sepM_lookup with "[$]").
  by apply hb_shared_lookup_Some.
Qed.

Lemma r2a_val_rel_pure_combine f2i rh bij v1 v2 av :
  r2a_val_rel_pure f2i rh v1 av →
  val_in_bij_pure bij v1 v2 →
  r2a_val_rel_pure f2i (r2a_combine_bij rh bij) v2 av.
Proof.
  move => ??. destruct v1, v2; simplify_eq/= => //. destruct!.
  split!; [by f_equal|]. apply r2a_combine_bij_lookup_Some. naive_solver.
Qed.

Lemma r2a_heap_shared_agree_pure_combine f2i rh bij h1 h2 h m :
  r2a_heap_shared_agree_pure f2i h1 rh m →
  heap_in_bij_pure bij h2 h →
  (∀ l v, h_heap h2 !! l = Some v → l.1 ∈ hb_shared_i bij → h1 !! l = Some v) →
  r2a_heap_shared_agree_pure f2i (h_heap h) (r2a_combine_bij rh bij) m.
Proof.
  move => ? Hbij Hincl.
  apply: (r2a_heap_shared_agree_pure_impl (λ p, hb_shared_rev bij !! p)); [done|].
  move => l2 ??? /r2a_combine_bij_lookup_Some[pi [??]].
  setoid_rewrite hb_shared_rev_lookup_Some.
  have [Hiff Hv]:= Hbij _ _ l2.2 ltac:(done). rewrite -surjective_pairing in Hiff.
  have [??]: is_Some (h_heap h2 !! (pi, l2.2)) by naive_solver.
  split!.
  - apply Hincl; [done|]. apply elem_of_hb_shared_i. naive_solver.
  - move => ??. apply: r2a_val_rel_pure_combine; [done|]. naive_solver.
Qed.

(** * Main vertical compositionality theorem:  *)
Lemma pp_to_ex_quant_if_then {R M A} (b : bool) `{!Inhabited A} pp1 pp2 (Q : R → uPred M → Prop):
  pp_to_ex (if b then pp_quant pp1 else pp2) Q →
  ∃ x : A, pp_to_ex (if b then pp1 x else pp2) Q.
Proof. destruct b => //=. by exists inhabitant. Qed.

Lemma r2a_bij_vertical m moinit hinit `{!VisNoAng m.(m_trans)} ins f2i :
  trefines (rec_to_asm ins f2i moinit hinit (rec_heap_bij hinit m))
           (rec_to_asm ins f2i moinit hinit m).
Proof.
  unshelve apply: mod_prepost_combine. {
    exact (λ pl '(R2A csa lra) _ '(R2A cs lr) Pa Pb P,
      csa = cs ∧
      lra = lr ∧
      (* mem': auth of asm memory *)
      (* moa: reflection of the asm memory owned by the environment
      into the rec_to_asm in the target *)
      (* mo: reflection of the asm memory owned by the module
      into the environment *)
      (* sprovs: static provenances (all wrappers agree and ensured to be constant) *)
      ∃ mem' moa mo sprovs,
        if pl is Env then
          (* rha: auth of the rec_to_asm in the target *)
          (* bijb: auth of the heap bij (in the target) *)
          (* hob: reflection of the ownership of the environment into
          the heap bijection. *)
          (* ho: reflection of the ownership of the module in the heap
          bijection into the environment. *)
          (* hprev: previous middle heap *)
          (* mh: assembly memory backing the locations that are shared
          in rha, but not in bijb *)
          (* hb: previous inner heap *)
          (* hs: statics owned in the middle heap *)
          (* ho': ownership that was deallocated from bijb by the
             module. We need to avoid that the env allocates this
             ownership again since if it contains statics, and the env
             shares these statics, we would not be able to mirrro this
             sharing in the middle heap (since the module might not
             have deallocated the ownership of the static in the
             middle heap). **)
          ∃ f2i_full rha bijb hob ho hprev mh hb hs ho',
          moa = mem' ∖ mo ∧
          hob = r2a_combine_priv (r2a_rh_shared rha) bijb hb ∖ ho ∧
          (P ⊣⊢ r2a_mem_map mo ∗ r2a_mem_map mh ∗ r2a_statics sprovs ∗
             ([∗ map] p↦a ∈ r2a_combine_bij (r2a_rh_shared rha) bijb, r2a_heap_shared p a) ∗
             ([∗ map] p↦h ∈ ho, r2a_heap_constant p h) ∗
             ([∗ map] p↦h ∈ ho', r2a_heap_constant p h) ∗
             r2a_f2i_full f2i_full) ∧
          satisfiable (Pa ∗ r2a_mem_auth mem' ∗ r2a_heap_auth rha ∗
                          r2a_mem_map moa ∗ r2a_statics sprovs ∗
                          ([∗ map] p↦h∈ hs, r2a_heap_constant p h) ∗
                          ([∗ map]p↦a ∈ r2a_rh_shared rha, r2a_heap_shared p a) ∗
                          r2a_f2i_full f2i_full) ∧
          satisfiable (Pb ∗ heap_bij_auth bijb ∗ heap_bij_statics sprovs ∗
             ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
             ([∗ map] p↦h∈ hs, heap_bij_const_i p h) ∗
             ([∗ map] p↦h∈ hob, heap_bij_const_s p h) ∗
             heap_in_bij bijb hprev hb) ∧
          mo ⊆ mem' ∧
          ho ⊆ r2a_combine_priv (r2a_rh_shared rha) bijb hb ∧
          hb_provs_i bijb ⊆ h_provs hprev ∧
          dom rha ⊆ h_provs hprev ∧
          heap_preserved (r2a_rh_constant rha) hprev ∧
          heap_preserved (hb_priv_i bijb) hprev ∧
          r2a_combine_priv_shared (r2a_rh_shared rha) bijb hb ⊆ ho ∧
          r2a_heap_shared_agree_pure f2i_full (filter (λ x, x.1.1 ∉ hb_shared_i bijb) (h_heap hprev))
                                     (r2a_rh_shared rha) mh ∧
          h_static_provs hprev = sprovs ∧
          sprovs ∖ (dom ho ∪ dom ho' ∪ hb_shared_s bijb) ⊆ dom hs
        else
          ∃ rha bijb rh hob ho hb hs ho' f2i_full,
          mo = mem' ∖ moa ∧
          ho = r2a_rh_constant rh ∖ hob ∧
          r2a_rh_shared rh = r2a_combine_bij (r2a_rh_shared rha) bijb ∧
          r2a_rh_constant rh = r2a_combine_priv (r2a_rh_shared rha) bijb hb ∧
          satisfiable (P ∗ r2a_mem_auth mem' ∗ r2a_heap_auth rh ∗ r2a_mem_map mo ∗
                         r2a_f2i_full f2i_full ∗ r2a_statics sprovs ∗
                          ([∗ map] p↦a ∈ r2a_rh_shared rh, r2a_heap_shared p a) ∗
                          ([∗ map] p↦h ∈ ho, r2a_heap_constant p h) ∗
                          ([∗ map] p↦h ∈ ho', r2a_heap_constant p h)) ∧
          (Pa ⊣⊢ r2a_mem_map moa ∗ r2a_f2i_full f2i_full ∗ r2a_statics sprovs ∗
             ([∗ map] p↦h∈ hs, r2a_heap_constant p h) ∗
             ([∗ map] p↦a ∈ r2a_rh_shared rha, r2a_heap_shared p a)) ∧

          (Pb ⊣⊢ ([∗ map] p2↦p1∈ hb_shared bijb, heap_bij_shared p1 p2) ∗
             ([∗ map] p↦h∈ hob, heap_bij_const_s p h) ∗
             ([∗ map] p↦h∈ hs, heap_bij_const_i p h) ∗
             heap_bij_statics sprovs) ∧
          moa ⊆ mem' ∧
          hob ⊆ r2a_rh_constant rh ∧
          filter is_ProvStatic (dom (hb_bij bijb)) ⊆ sprovs ∧
          sprovs ∖ (dom ho ∪ dom ho' ∪ hb_shared_s bijb) ⊆ dom hs). }
  { move => [? []] //= rs mem [] //= ? h *.
    have [? [?[??]]] : ∃ rh, heap_preserved (r2a_rh_constant rh) h ∧ dom rh ⊆ h_provs h ∧
                            hinit ⊆ r2a_rh_constant rh. {
      iSatStart. iIntros!.
      iDestruct select (r2a_heap_inv _) as (rh ??) "[Hsh [Hhag [Hh #Hag]]]".
      iDestruct (r2a_heap_lookup_big' with "[$] [$]") as %?.
      iSatStop. naive_solver.
    }
    iSatStart. iIntros!.
    iDestruct select (r2a_f2i_incl f2i _) as "Hf2i".
    unfold r2a_f2i_incl at 1. iDestruct "Hf2i" as (f2i_full ??) "#?".
    iSatStop.

    pose (hs := (filter (λ p, is_ProvStatic p.1 ∧ hinit !! p.1 = None) (gmap_curry (h_heap h)))).
    have Hpres : heap_preserved (hinit ∪ hs) h. {
      apply heap_preserved_union.
      + by apply: heap_preserved_mono.
      + move => ?? /map_lookup_filter_Some[/lookup_gmap_curry_Some[? ->] ?].
        by rewrite -surjective_pairing.
    }
    have Hdisj : hinit ##ₘ hs. {
      apply map_disjoint_spec => ???? /map_lookup_filter_Some. naive_solver.
    }
    have Hdisjinit : dom hs ## hb_shared_i (heap_bij_init_bij hinit). {
      rewrite/= /heap_bij_init_bij hb_shared_i_hb_update_const_s_big
        ?hb_shared_i_hb_update_const_i_big ?hb_shared_s_hb_update_const_i_big
        ?hb_shared_i_empty ?hb_shared_s_empty; apply disjoint_empty_r.
    }
    have Hinprovs : dom hinit ∪ dom hs ⊆ h_provs h. {
      apply union_subseteq. split.
      + etrans; [|done]. etrans; [by eapply subseteq_dom|].
        rewrite -(dom_fmap_L R2AConstant).
        eapply subseteq_dom. apply r2a_rh_constant_fmap_l.
      + move => ? /elem_of_dom[? /map_lookup_filter_Some[/lookup_gmap_curry_Some[He Heq] ?]].
        move: He => /(map_choose _)[?[? Hl]]. rewrite Heq in Hl.
        by apply: (lookup_heap_is_Some_elem_of_h_provs (_, _)).
    }
    eexists. split_and!; [done..| |].
    eexists moinit, ∅, moinit, (h_static_provs h), f2i_full, (R2AConstant <$> (hinit ∪ hs)),
      (hb_update_const_s_big hs
         (hb_update_const_i_big hs (heap_bij_init_bij hinit) Hdisjinit)), hs, hinit, h, ∅, h, hs, ∅.
    split!.
    - by rewrite map_difference_diag.
    - rewrite r2a_rh_shared_fmap_constant. apply map_eq => ?. apply option_eq => ?.
      split.
      + move => ?. apply lookup_difference_Some. split.
        2: { by apply: map_disjoint_Some_r. }
        apply r2a_combine_priv_Some. left => /=.
        apply lookup_union_Some_raw. left. apply lookup_fmap_Some. naive_solver.
      + move => /lookup_difference_Some[/r2a_combine_priv_Some]/=.
        rewrite right_id_L. move => [|].
        * move => /lookup_union_Some_raw[/lookup_fmap_Some|[?/lookup_fmap_Some]]; naive_solver.
        * move => [? [/lookup_union_Some_raw[/lookup_fmap_Some|[?/lookup_fmap_Some]] ]]; naive_solver.
    - apply: satisfiable_bmono; [apply (r2a_res_init' moinit (hinit ∪ hs))|].
      rewrite big_sepM_union //.
      iIntros!. iDestruct select (r2a_f2i_full _) as "#$". iFrame.
      iModIntro. rewrite r2a_rh_shared_fmap_constant /r2a_mem_map.
      iSplit!. unfold r2a_f2i_incl. by iFrame "#".
    - apply: satisfiable_bmono; [apply heap_bij_init|]. iIntros "[? $]".
      iMod (heap_bij_alloc_const_i_big hinit with "[$]") as "[? $]".
      { rewrite hb_provs_i_empty. set_solver. }
      iMod (heap_bij_alloc_const_s_big hinit with "[$]") as "[? $]".
      { rewrite /= dom_empty. set_solver. }
      iMod (heap_bij_alloc_const_i_big hs with "[$]") as "[? $]".
      { rewrite hb_provs_i_hb_update_const_s_big
          ?hb_provs_i_hb_update_const_i_big
          ?hb_provs_i_empty ?hb_shared_s_hb_update_const_i_big
          ?hb_shared_s_empty ?right_id_L.
        - symmetry. by apply map_disjoint_dom.
        - set_solver. }
      iMod (heap_bij_alloc_const_s_big hs with "[$]") as "[? $]".
      { rewrite /= right_id_L dom_fmap. symmetry. by apply map_disjoint_dom. }
      iFrame. iModIntro. iSplit!.
      + iApply big_sepM_intro. iIntros "!>" (?? Hin). exfalso. move: Hin.
        rewrite hb_shared_lookup_Some /= right_id_L -map_fmap_union lookup_fmap_Some.
        naive_solver.
      + iIntros (???). simpl. rewrite right_id_L -map_fmap_union lookup_fmap_Some.
        iIntros (?). naive_solver.
    - rewrite r2a_rh_shared_fmap_constant. apply map_subseteq_spec => p ??.
      apply r2a_combine_priv_Some. left => /=. rewrite right_id_L.
      apply lookup_union_Some; [by rewrite map_disjoint_fmap|]. right.
      apply lookup_fmap_Some. naive_solver.
    - rewrite hb_provs_i_hb_update_const_s_big. 2: {
         rewrite hb_shared_s_hb_update_const_i_big /heap_bij_init_bij
           hb_shared_s_hb_update_const_s_big ?hb_shared_s_hb_update_const_i_big
           ?hb_shared_s_empty; apply disjoint_empty_r. }
      rewrite hb_provs_i_hb_update_const_i_big /heap_bij_init_bij
        hb_provs_i_hb_update_const_s_big ?hb_shared_s_hb_update_const_i_big
        ?hb_provs_i_hb_update_const_i_big ?hb_shared_s_empty
        ?hb_provs_i_empty ?right_id_L. 2: apply disjoint_empty_r.
      by rewrite union_comm.
    - rewrite dom_fmap_L dom_union_L. done.
    - rewrite r2a_rh_constant_fmap //.
    - rewrite right_id_L map_union_comm //.
    - rewrite r2a_rh_shared_fmap_constant. apply map_subseteq_spec => p ?.
      move => /r2a_combine_priv_shared_Some/=[?[+[??]]].
      rewrite right_id_L. rewrite -map_fmap_union lookup_fmap_Some. naive_solver.
    - rewrite r2a_rh_shared_fmap_constant.
      eexists ∅. move => ???. by simplify_map_eq.
    - move => p /elem_of_difference[/elem_of_h_static_provs[?[l [? [??]]]]].
      move => /not_elem_of_union[/not_elem_of_union[/not_elem_of_dom? _] _].
      apply elem_of_dom. eexists (h_block h p). apply map_lookup_filter_Some. split!.
      apply lookup_gmap_curry_Some. setoid_rewrite h_block_lookup. split; [|done].
      move => /map_empty/(_ l.2). subst. rewrite h_block_lookup -surjective_pairing.
      naive_solver.
    - iSatMono. iIntros!. iDestruct (r2a_heap_get_statics with "[$]") as "#?". iFrame "∗#".
      rewrite r2a_rh_shared_fmap_constant /r2a_mem_map !big_sepM_empty.
      iSplit!. iApply big_sepM_intro. iIntros "!>" (?? [?[??]]%r2a_combine_bij_lookup_Some).
      simplify_map_eq.
  }
  all: move => [csa lra] [] [cs lr] Pa Pb P [? e] ?/=; destruct!.
  - move: e => []//= regs mem b ? h ? vs avs.
    apply pp_to_all_forall => -[e' [??]] P'x Hx P' HP'. simplify_eq/=. setoid_subst. eexists b.
    rename select (satisfiable (Pa ∗ _)) into HPa.
    rename select (satisfiable (Pb ∗ _)) into HPb.
    rename select (heap_preserved (r2a_rh_constant rha) hprev) into Hpreva.
    rename select (heap_preserved (hb_priv_i bijb) hprev) into Hprevb.
    iSatStart HP'. iIntros!.
    iDestruct select (r2a_mem_inv _ _ _) as "((Hgp&Hsp)&Hmauth)".
    iDestruct (r2a_mem_lookup_big' mo with "[$] [$]") as %?.
    iDestruct (r2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
    iDestruct select (r2a_heap_inv _) as (rh ??) "[Hsh [Hhag [Hh #Hag]]]".
    iDestruct (r2a_heap_shared_lookup_big' (r2a_combine_bij _ _) with "[$] [$]") as %?.
    iDestruct (r2a_heap_lookup_big' ho with "[$] [$]") as %?.
    iDestruct select (r2a_f2i_full _) as "#Hf2i_full".
    iDestruct (r2a_heap_shared_agree_to_pure with "[$] [$] [$]") as (??) "[? ?]".
    iDestruct (r2a_val_rel_big_to_pure with "[$] [$] [$]") as %Hvs.
    iDestruct (r2a_statics_agree with "[$] [$]") as %Hag.
    iSatStop HP'.

    have /(map_subseteq_exists_L _ _)[hsn [Hhsn Hhsndom]] :
      r2a_shared_statics rh bijb ⊆ dom hs. {
      move => p /r2a_shared_statics_in[? [?[Hsh ?]]].
      revert select (_ ⊆ dom hs). apply.
      apply elem_of_difference. split. {
        rewrite Hag -h_provs_static //. revert select (dom rh ⊆ h_provs h).
        apply. by apply elem_of_dom. }
      move => /elem_of_union[/elem_of_union Hin|//].
      iSatStart HP'. iIntros!.
      move: Hin => [|] /elem_of_dom[? Hl].
      all: iDestruct (big_sepM_lookup _ _ _ _ Hl with "[$]") as "?".
      all: iDestruct (r2a_heap_lookup' with "[$] [$]") as %Heq;
        by rewrite Heq in Hsh.
      Unshelve. all: by apply _.
    }
    iSatStart HPa. iIntros!.
    rewrite Hhsn big_sepM_union. 2: { apply map_disjoint_difference_r'. }
    iDestruct!.
    iDestruct (r2a_heap_lookup_big' hsn with "[$] [$]") as %Hhsnsub.
    iSatStop HPa.

    have [| | | | | | | | rh' [bijb' ?]]:= r2a_combine_extend (h_provs hprev) rha bijb rh ho hb hsn => //.
    { etrans; [by apply map_fmap_mono|]. apply r2a_rh_constant_fmap_l. }
    destruct!.
    rename select (r2a_rh_shared rh = _) into Hihs.
    rename select (r2a_rh_constant rh = _) into Hihc.
    rename select (hb_priv_i bijb ∖ hsn = hb_priv_i bijb') into Hpriveq.
    rename select (r2a_rh_constant rh ∖ (hb_priv_s bijb' ∖ ho) = ho) into Hhoeq.
    rename select (hb_priv_s bijb' ∖ (ho ∖ (ho ∖ hb_priv_s bijb)) = hb_priv_s bijb' ∖ ho) into Hhoeq2.

    have Hstaticinprev :
      ∀ p, is_ProvStatic p → p ∈ hb_shared_i bijb' → p ∈ h_provs hprev. {
      move => p ? Hin. rewrite h_provs_static // Hag -h_provs_static //.
      have : p ∈ dom (hb_bij bijb'); [|set_solver].
      rewrite hb_shared_i_static // in Hin.
      move: Hin => /elem_of_hb_shared_s[??].
      by apply elem_of_dom.
    }

    iSatStartBupd HPa. iIntros!.
    iMod (r2a_mem_update_all mem with "[$] [$]") as "[Ha Hmo]"; [done..|].
    iMod (r2a_heap_free_big' _ hsn with "[$] [$]") as "?".
    iMod (r2a_heap_alloc_shared_big' with "[$]") as "[Hih ?]"; [done..|]. iModIntro.
    iSatStop HPa.

    iSatStart HP'. iDestruct "Hf2i_full" as "-#?". iSatStop HP'.
    repeat r2a_mem_transfer HP' HPa.

    iSatStart HP'. iIntros!. iDestruct (r2a_mem_lookup_big' with "[$] [$]") as %?. iSatStop HP'.

    iSatStartBupd HPb. iIntros!.
    rewrite r2a_combine_priv_diff //.
    rewrite (map_difference_difference_add (hb_priv_s bijb)).
    rewrite Hhsn big_sepM_union. 2: { apply map_disjoint_difference_r'. }
    iDestruct select (_ ∗ _)%I as "[Hhsn ?]".

    iMod (heap_bij_update_all bijb' with "[$] [$] [$] Hhsn") as "[?[#Hs ?]]". {
      apply map_difference_difference_subseteq, map_agree_spec. move => j x1 x2 Hho.
      have : r2a_combine_priv (r2a_rh_shared rha) bijb hb !! j = Some x1 by apply: lookup_weaken.
      move => /r2a_combine_priv_Some ? /hb_priv_s_lookup_Some. naive_solver.
    } { done. } { done. } { done. }
    rewrite Hhoeq2.
    iModIntro.
    iSatStop HPb.

    split; [done|].
    set (h' := (heap_merge (heap_restrict (heap_through_bij bijb' h)
                              (λ p, p ∈ dom (rh' ∪ r2a_rh_shared rha)))
                  (heap_restrict hprev
                                 (λ x, x ∉ dom (rh' ∪ r2a_rh_shared rha) ∨ x ∉ hb_shared_i bijb')))).
    set (vs' := (val_through_bij bijb' <$> vs)).


    have h_provs_h' : h_provs h' = hb_shared_i bijb' ∪ h_provs hprev. {
      rewrite /h' h_provs_heap_merge !h_provs_heap_restrict h_provs_heap_through_bij.
      2: set_solver.
      apply set_eq => p. rewrite 2!elem_of_union !elem_of_filter.
      destruct (decide (is_ProvBlock p)); [naive_solver|].
      have ? : is_ProvStatic p by destruct p.
      have ? : p ∈ hb_shared_i bijb' → p ∈ h_provs hprev by apply Hstaticinprev.

      split => ?; destruct! => //.
      - naive_solver.
      - naive_solver.
      - naive_solver.
      - destruct (decide (p ∈ dom (rh' ∪ r2a_rh_shared rha) ∧ p ∈ hb_shared_i bijb')); naive_solver.
      - destruct (decide (p ∈ dom (rh' ∪ r2a_rh_shared rha) ∧ p ∈ hb_shared_i bijb')) as [Hin|Hin];
          [naive_solver|].
        rewrite not_and_r in Hin. naive_solver.
    }

    have Hinstatic : ∀ p h, p ∈ h_static_provs h ↔ p ∈ h_provs h ∧ is_ProvStatic p. {
      move => p ?. destruct (decide (is_ProvStatic p)).
      - rewrite h_provs_static; naive_solver.
      - rewrite elem_of_h_static_provs. naive_solver.
    }

    have h_static_provs_h' : h_static_provs h' = h_static_provs h. {
      apply set_eq => p. rewrite Hinstatic h_provs_h' elem_of_union. split.
      - move => [[Hin| Hin] ?].
        + rewrite -Hag -h_provs_static //. by apply Hstaticinprev.
        + rewrite h_provs_static // in Hin. congruence.
      - move => ?. have ? : is_ProvStatic p by eapply elem_of_h_static_provs.
        split; [|done]. right. rewrite h_provs_static; congruence.
    }

    have Hrh_shared :
      r2a_rh_shared ((R2AShared <$> rh') ∪ rha ∖ (R2AConstant <$> hsn)) =
        rh' ∪ r2a_rh_shared rha. {
      rewrite r2a_rh_shared_union // r2a_rh_shared_fmap. f_equal.
      apply map_eq => ?. apply option_eq => ?.
      rewrite !r2a_ih_shared_Some lookup_difference_Some. split; [naive_solver|].
      move => ?. split!. rewrite lookup_fmap fmap_None.
      apply: lookup_weaken_None; [|done]. apply r2a_rh_constant_None. naive_solver.
    }


    eexists h', _, vs', avs. apply pp_to_ex_exists.
    eexists ((e'.1, event_set_vals_heap e'.2 vs' h'), R2A _ _).
    move: Hx => /pp_to_ex_quant_if_then[f Hx].
    eexists (if b then (r2a_f2i_incl {[f := regs !!! "PC"]} ∅) ∗ True else True)%I. unfold vs' in *.
    split!.
    + iSatMono HPa. iIntros!.
      iDestruct select (r2a_f2i_full _) as "#Hf2i". iFrame "Hf2i".
      iAssert ([∗ map] p↦a ∈ r2a_rh_shared ((R2AShared <$> rh') ∪ rha ∖ (R2AConstant <$> hsn)), r2a_heap_shared p a)%I as "#Hsh". {
        rewrite Hrh_shared. iApply (big_sepM_union_2 with "[$] [$]").
       } iFrame "Hsh".
      iDestruct select (r2a_mem_map (mem ∖ _)) as "$".
      iDestruct select (r2a_statics _) as "#$".
      iFrame.
      iDestruct (r2a_mem_uninit_alt2 with "[$]") as "Huninit". rewrite Hvslen Z2Nat.id; [|lia].
      iFrame "Huninit". rewrite -!(assoc bi_sep).
      iSplit!.
      * rewrite h_provs_h'. set_solver.
      * move => l ?. rewrite r2a_rh_constant_union // r2a_rh_constant_fmap_shared left_id_L.
        move => Hih /=.
        have ? : l.1 ∉ dom (rh' ∪ r2a_rh_shared rha). {
          move: Hih => /r2a_rh_constant_Some/lookup_difference_Some[??].
          rewrite dom_union. apply not_elem_of_union. split.
          - revert select (dom rh' ## _) => Hih'.
            symmetry in Hih'. apply: Hih'.
            apply elem_of_difference. rewrite not_elem_of_dom. split; [|done].
            revert select (dom rha ⊆ h_provs hprev). apply. by apply elem_of_dom.
          - apply not_elem_of_dom. apply r2a_rh_shared_None. naive_solver.
        }
        rewrite lookup_union_r. 2: { apply map_lookup_filter_None. naive_solver. }
        rewrite map_lookup_filter_true; [|naive_solver].
        apply Hpreva.
        move: Hih => /r2a_rh_constant_Some /lookup_difference_Some[/r2a_rh_constant_Some ??].
        done.
      * iApply r2a_heap_shared_agree_union. {
          apply map_disjoint_spec => -[p o] ?? /map_lookup_filter_Some[/=/heap_through_bij_Some??].
          move => /map_lookup_filter_Some[?[//|]] /=. destruct!.
          apply. apply elem_of_hb_shared_i. naive_solver.
        }
        iDestruct select (r2a_mem_map mh) as "Hmh".
        iSplitR "Hmh".
        -- iApply (r2a_heap_shared_agree_of_pure with "[$]"); [|done..].
           apply: (r2a_heap_shared_agree_pure_impl (λ p, hb_shared bijb' !! p)); [done|].
           move => ??? /map_lookup_filter_Some [/heap_through_bij_Some[?[?[?[??]]]] ?] Hsh. simplify_eq/=.
           split!.
           ++ by apply hb_shared_lookup_Some.
           ++ done.
           ++ rewrite Hihs. apply r2a_combine_bij_lookup_Some. split!.
              by rewrite Hrh_shared in Hsh.
           ++ move => ??. apply: r2a_val_rel_pure_through_bij; [done|].
              by rewrite Hrh_shared.
        -- iApply r2a_heap_shared_agree_impl.
           2: { iApply (r2a_heap_shared_agree_of_pure with "[$] [] [$]"); [done|].
                rewrite Hrh_shared // big_sepM_union //.
                { by iDestruct!. }
                apply (map_disjoint_fmap R2AShared R2AShared).
                apply: map_disjoint_weaken_r; [done|].
                apply: map_subseteq_difference_r; [apply r2a_rh_shared_fmap_l|].
                apply: map_disjoint_weaken_r; [apply r2a_rh_shared_constant_disj|].
                by apply map_fmap_mono.
           }
           move => l ?? /map_lookup_filter_Some[? Hne] Ha.
           move: Hne => [Hne|Hne]; simplify_eq/=. {
             contradict Hne. apply elem_of_dom.
             move: Ha. rewrite -r2a_ih_shared_Some Hrh_shared.
             done.
           }
           split.
           ++ apply map_lookup_filter_Some => /=. split; [done|].
              contradict Hne. move: Hne => /elem_of_hb_shared_i[?]. rewrite -hb_shared_lookup_Some => ?.
              apply elem_of_hb_shared_i. eexists _. rewrite -hb_shared_lookup_Some.
              by apply: lookup_weaken.
           ++ move: Ha => /lookup_union_Some_raw[|[? /lookup_difference_Some[??]] //].
              rewrite lookup_fmap => /fmap_Some[?[??]].
              simplify_eq. contradict Hne.
              revert select (dom rh' ⊆ hb_shared_i bijb'). apply.
              by apply elem_of_dom.
      * by rewrite Hag h_static_provs_h'.
      * iApply (r2a_val_rel_big_through_bij with "[$] Hsh"); [done|].
        by rewrite Hrh_shared.
      * destruct b => //. destruct!/=. iSplit; [|done]. iApply (r2a_f2i_full_to_singleton with "Hf2i").
        iSatStart HP'. iDestruct!.
        iDestruct (r2a_f2i_full_singleton with "[$] [$]") as %?.
        by iSatStop.
    + iSatMono HPb. iIntros!. rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap.
      2: { rewrite length_fmap. destruct b; simplify_eq/=; destruct!/=; done. }
      iDestruct select (heap_bij_statics _) as "#Hag".
      iFrame. iSplit!.
      * etrans; [eassumption|]. eassumption.
      * rewrite h_provs_h' /hb_provs_i -Hpriveq. set_solver.
      * apply: heap_preserved_mono; [done|]. rewrite Hihc.
        apply map_subseteq_spec => ??. rewrite hb_priv_s_lookup_Some r2a_combine_priv_Some.
           naive_solver.
      * rewrite -Hpriveq.
        move => [p o] /= ? /lookup_difference_Some[??].
        rewrite lookup_union_r. 2: {
          apply map_lookup_filter_None. left.
          apply eq_None_not_Some => /heap_through_bij_is_Some[?[/hb_disj]].
          rewrite -Hpriveq. move => /lookup_difference_None.
          rewrite /is_Some. naive_solver.
        }
        rewrite map_lookup_filter_true; [by apply Hprevb|].
        move => ?? /=. right. move => /elem_of_hb_shared_i[??].
        exploit hb_disj; [done|]. rewrite -Hpriveq.
        move => /lookup_difference_None. rewrite /is_Some. naive_solver.
      * iIntros (p1 p2 o ?) => /=.
        destruct (decide (p1 ∈ dom (rh' ∪ r2a_rh_shared rha))) as [Hin|].
        -- rewrite lookup_union_l.
           2: { apply map_lookup_filter_None. right => ?? /=. rewrite elem_of_hb_shared_i. naive_solver. }
           rewrite map_lookup_filter_true; [|done].
           iSplit; [iPureIntro; by apply heap_through_bij_is_Some1|].
           iIntros (??[?[?[?[??]]]]%heap_through_bij_Some ?). simplify_bij.
           have [|? Hval]:= r2a_heap_shared_agree_pure_lookup _ _ _ _ _ _ ltac:(done) ltac:(done) => /=. {
             move: Hin => /elem_of_dom[??]. rewrite Hihs. eexists _. apply r2a_combine_bij_lookup_Some.
             naive_solver.
           }
           revert select (r2a_rh_shared rh = _) => Heq. rewrite Heq in Hval.
           destruct x0 => //; simplify_eq/=.
           move: Hval => [?[? /r2a_combine_bij_lookup_Some [?[??]]]]. simplify_map_eq.
           unfold loc_in_bij. iSplit!.
           ++ by eapply hb_shared_prov.
           ++ iApply (big_sepM_lookup with "[$]"). by apply hb_shared_lookup_Some.
        -- rewrite lookup_union_r. 2: { apply map_lookup_filter_None. naive_solver. }
           rewrite map_lookup_filter_true; [|naive_solver].
           revert select (heap_preserved (r2a_rh_constant rh) h) => Hpre.
           have -> : h_heap h !! (p2, o) = h_heap hb !! (p2, o). {
             rewrite -(h_block_lookup hb). apply Hpre.
             rewrite Hihc /=. apply: lookup_weaken; [|by apply map_union_subseteq_l].
             apply r2a_combine_priv_shared_Some. split!. by apply not_elem_of_dom. }
           iDestruct select (heap_in_bij _ _ _) as "Hbij".
           iApply ("Hbij" $! p1 p2 o). iPureIntro.
           naive_solver.
        * by rewrite Hag h_static_provs_h'.
        * by rewrite Hag.
      * rewrite big_sepL2_fmap_l. iApply big_sepL_sepL2_diag.
        iApply big_sepL_intro. iIntros "!>" (???).
        move: Hvs => /(Forall2_lookup_l _ _ _ _ _). move => /(_ _ _ ltac:(done))[?[??]].
        by iApply (val_in_through_bij with "[$]"); [|done].
      * done.
    + destruct b; simplify_eq/=; destruct!/=; done.
    + rewrite Hrh_shared. done.
    + rewrite {1}Hihc Hrh_shared. done.
    + iSatMono HP'. iIntros!. rewrite Hhoeq. iFrame.
      rewrite !map_difference_id; [by iFrame|done..].
    + by apply map_subseteq_difference_l.
    + rewrite Hihc. apply map_union_subseteq_r';
           [by apply r2a_combine_priv_shared_priv_s_disj|by apply map_subseteq_difference_l].
    + move => p /elem_of_filter[?]. rewrite Hag -h_provs_static //. set_solver.
    + rewrite Hhoeq. rewrite dom_difference_L.
      have Hsubb : hb_shared_s bijb ∪ dom hsn ⊆ hb_shared_s bijb'. {
        apply union_least; [by apply subseteq_dom|done].
      }
      etrans. { by apply difference_mono_l, union_mono_l. }
      rewrite assoc_L -difference_difference_l_L.
      by apply difference_mono_r.
    + destruct b; simplify_eq/=; destruct!/=; split!.
  - move => vs hb' Pb' HPb' ? rs' mem'' ? avs.
    apply pp_to_all_forall => -[e' [??]] ? Hx Pa' HPa'.
    rename select (Pa ⊣⊢ _) into HPaeq.
    rename select (Pb ⊣⊢ _) into HPbeq.
    rename select (satisfiable (P ∗ _)) into HP.
    rename select (r2a_rh_shared rh = _) into Hihs.
    rename select (r2a_rh_constant rh = _) into Hihc.

    iSatStart HPb'.
    rewrite HPbeq.
    iIntros!.
    iDestruct select (heap_bij_inv _ _) as (bijb' ? ? ? ?) "(Hsh&Hh&Hbij&#[Hag1 Hag2])".
    iDestruct (val_in_bij_to_pure_big with "[$] [$]") as %?.
    iDestruct (heap_bij_const_s_lookup_big with "[$] [$]") as %?.
    iDestruct (heap_bij_shared_lookup_big with "[$] [$]") as %?.
    iDestruct (heap_in_bij_to_pure with "[$] [$]") as %?.
    iDestruct (heap_bij_statics_eq with "[$] [$]") as %Hag. subst.
    iDestruct (heap_bij_statics_eq with "Hag1 Hag2") as %Hag.
    iSatStop HPb'.

    iSatStart HPa'.
    rewrite HPaeq.
    iIntros!.
    rewrite heap_of_event_event_set_vals_heap vals_of_event_event_set_vals_heap.
    2: { destruct e; simplify_eq/=; destruct!/=; solve_length. }
    iDestruct select (r2a_f2i_full _) as "#Hf2i_full".
    iDestruct select (r2a_mem_inv _ _ _) as "((Hgp&Hsp)&Hmauth)".
    iDestruct (r2a_mem_lookup_big' moa with "[$] [$]") as %?.
    iDestruct (r2a_mem_uninit_alt1 with "[$]") as (? Hvslen) "Hsp"; [lia|].
    iDestruct select (r2a_heap_inv _) as (rha' ??) "[Hsh [Hhag [Hh #Hag]]]".
    rewrite -(map_filter_union_complement (λ x, x.1.1 ∈ hb_shared_i bijb') (h_heap hb')).
    rewrite r2a_heap_shared_agree_union. 2: apply map_disjoint_filter_complement.
    iDestruct "Hhag" as "[Hhag1 Hhag2]".
    iDestruct (r2a_heap_shared_agree_to_pure with "[$] Hhag1 [$]") as (mhag1 ?) "[? ?]".
    iDestruct (r2a_heap_shared_agree_to_pure with "[$] Hhag2 [$]") as (mhag2 ?) "[? ?]".
    iDestruct (r2a_heap_shared_lookup_big' with "[$] [$]") as %?.
    iDestruct (r2a_val_rel_big_to_pure with "[$] [$] [$]") as %Hvs.
    iDestruct (r2a_statics_agree with "[$] [$]") as %Hag'.
    iSatStop HPa'.

    have Hdisj := r2a_combine_bij_priv_disj (r2a_rh_shared rha') bijb' (heap_of_event e).

    iSatStartBupd HP. iIntros!.
    iMod (r2a_mem_update_all mem'' with "[$] [$]") as "[Ha Hmo]"; [done..|].
    iMod (r2a_heap_update_all
            (r2a_combine_bij (r2a_rh_shared rha') bijb')
            (r2a_combine_priv (r2a_rh_shared rha') bijb' (heap_of_event e))
           with "[$] [$] [$]") as "(?&?&?)".
    { done. }
    { etrans; [done|]. apply map_union_subseteq_r. apply r2a_combine_priv_shared_priv_s_disj. }
    { rewrite Hihs. by apply r2a_combine_bij_mono. }
    { move: Hdisj => /map_disjoint_dom. by rewrite !dom_fmap. }

    have ? := r2a_unowned_statics_disj (heap_of_event e) bijb bijb' rha'.
    iMod (r2a_heap_alloc_big' _ (r2a_unowned_statics (heap_of_event e) bijb bijb') with "[$]") as "(?&?)"; [done|].
    iDestruct select ([∗ map] p↦h ∈ ho', r2a_heap_constant p h)%I as "Hho'".
    iDestruct select ([∗ map] p↦h ∈ r2a_unowned_statics (heap_of_event e) bijb bijb', r2a_heap_constant p h)%I as "Hho''".
    iDestruct (big_sepM_union_2 with "Hho' Hho''") as "Hho'".
    iModIntro.
    iSatStop HP.

    iSatStart HPa'. iDestruct "Hf2i_full" as "-#?". iSatStop HPa'.
    repeat r2a_mem_transfer HPa' HP.

    split; [done|]. eexists  _, _, _, avs.
    apply pp_to_ex_exists. eexists (_, R2A _ _).
    eexists (if e is ERCall f _ _ then (r2a_f2i_incl {[f := rs' !!! "PC"]} ∅) ∗ True else True)%I. split!.
    2: {
      iSatMono HPa'. iIntros!.
      iDestruct (r2a_mem_lookup_big' with "[$] [$]") as %?.
      rewrite Hag'.
      iFrame. by erewrite map_difference_id.
    }
    + iSatMono HP. iIntros!.
      iDestruct select (r2a_f2i_full _) as "#Hf2i_full".
      iDestruct select (r2a_statics _) as "#Hag".
      iDestruct select ([∗ map] p↦h ∈ (ho' ∪ _), r2a_heap_constant p h)%I as "Hho'".
      iDestruct select ([∗ map] p↦h ∈ (r2a_combine_priv _ _ _ ∖ _), r2a_heap_constant p h)%I as "Hho".
      iDestruct select (r2a_mem_map (mem'' ∖ _)) as "$".
      iDestruct select (r2a_mem_map mhag2) as "$".
      iDestruct select ([∗ map] _↦_ ∈ _, r2a_heap_shared _ _)%I as "#Hsh".
      (* We need to be very careful with the order of framing such
      that ho and ho' get instantiated in the right way. *)
      iFrame "Hho". iFrame "Hho'". iFrame "Hsh". iFrame.
      iDestruct (r2a_mem_uninit_alt2 with "[$]") as "Hsp". rewrite Hvslen Z2Nat.id; [|lia].
      rewrite Hag'. iFrame "∗#".
      iSplitL; repeat iSplit.
      * iPureIntro. rewrite !dom_union_L !dom_fmap_L.
        apply union_subseteq. split.
        2: etrans; [|done]; apply union_subseteq; split.
        -- move => ? /elem_of_dom [? /r2a_unowned_statics_lookup_Some[?[?[??]]]].
           apply elem_of_h_provs. left.
           revert select (_ ⊆ h_static_provs (heap_of_event e)). apply.
           by apply elem_of_filter.
        -- move => p /elem_of_dom[?/r2a_combine_bij_lookup_Some?]. apply elem_of_dom. naive_solver.
        -- move => p /elem_of_dom[?/r2a_combine_priv_Some?]. apply elem_of_dom. naive_solver.
      * iPureIntro. rewrite !r2a_rh_constant_union // r2a_rh_constant_fmap_shared left_id_L.
        rewrite !r2a_rh_constant_fmap.
        move => l? /lookup_union_Some_raw[|[?]].
        -- move => /r2a_unowned_statics_lookup_Some [?[->?]].
           by rewrite h_block_lookup -surjective_pairing.
        -- move => /r2a_combine_priv_Some[?|?].
           ++ revert select (heap_preserved (hb_priv_s bijb') (heap_of_event e)).
              apply. by apply hb_priv_s_lookup_Some.
           ++ destruct!. by rewrite h_block_lookup -surjective_pairing.
      * rewrite !r2a_rh_shared_union // r2a_rh_shared_fmap !r2a_rh_shared_fmap_constant ?right_id_L ?left_id_L //.
      * iApply (r2a_heap_shared_agree_of_pure with "[$] [] [$]").
        all: rewrite !r2a_rh_shared_union // r2a_rh_shared_fmap !r2a_rh_shared_fmap_constant ?right_id_L ?left_id_L//.
        apply: r2a_heap_shared_agree_pure_combine; [done..|].
        move => ????. by apply map_lookup_filter_Some.
      * iApply (r2a_val_rel_big_of_pure with "[$] Hsh").
        apply Forall2_same_length_lookup. split; [solve_length|].
        move => ?????. move: Hvs => /(Forall2_lookup_r _ _ _ _ _). move => /(_ _ _ ltac:(done))[?[??]].
        revert select (Forall2 _ _ _) => /(Forall2_lookup_lr _ _ _ _ _ _)?.
        apply: r2a_val_rel_pure_combine; naive_solver.
      * destruct e => //=. destruct!/=. iSplit; [|done].
        iApply (r2a_f2i_full_to_singleton with "Hf2i_full").
        iSatStart HPa'. iIntros!.
        iDestruct (r2a_f2i_full_singleton with "[$] [$]") as %?. by iSatStop.
    + iSatMono HPb'. iFrame.
      erewrite map_difference_id; [by iFrame|].
      etrans; [done|]. apply map_union_subseteq_r. apply r2a_combine_priv_shared_priv_s_disj.
    + by apply map_subseteq_difference_l.
    + by apply map_subseteq_difference_l.
    + done.
    + done.
    + done.
    + done.
    + rewrite /r2a_combine_priv map_difference_union_distr.
      apply map_union_subseteq_l'.
      rewrite (map_difference_disj_id _ hob) //.
      apply: map_disjoint_weaken_r; [|done].
      apply r2a_combine_priv_shared_priv_s_disj.
    + done.
    + etrans; [|done]. rewrite Hag' Hihc.
      move => p /elem_of_difference[Hs Hn].
      apply elem_of_difference. split; [done|]. contradict Hn.
      rewrite dom_union !elem_of_union.
      move: Hn => /elem_of_union[/elem_of_union[|]|]. 2: naive_solver.
      2: { right. by apply: subseteq_dom. }
      rewrite !dom_difference.
      move => /elem_of_difference[+ ?].
      move => /elem_of_dom[? /r2a_combine_priv_Some[|[?[??]]]].
      * move => Hb. destruct (hb_bij bijb' !! p) as [[|]|] eqn: Hb'.
        -- right. apply elem_of_hb_shared_s. naive_solver.
        -- left. left. apply elem_of_difference. split; [|done].
           apply elem_of_dom. eexists _. apply r2a_combine_priv_Some.
           by left.
        -- left. right. right. apply elem_of_dom. eexists _.
           apply r2a_unowned_statics_lookup_Some. rewrite elem_of_dom not_elem_of_dom.
           split_and! => //. by eapply elem_of_h_static_provs.
      * right. apply: subseteq_dom; [done|]. apply elem_of_dom. eexists.
        by apply hb_shared_lookup_Some.
    + destruct e; simplify_eq/=; destruct!/=; split!.
Qed.

(* Print Assumptions r2a_bij_vertical. *)

Lemma r2a_bij_vertical_N m moinit hinit `{!VisNoAng m.(m_trans)} ins f2i n:
  trefines (rec_to_asm ins f2i moinit hinit (rec_heap_bij_N n hinit m))
           (rec_to_asm ins f2i moinit hinit m).
Proof. elim: n => //= ??. etrans; [by apply: r2a_bij_vertical|eauto]. Qed.
