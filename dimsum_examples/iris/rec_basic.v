From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Definition array (l : loc) (vs : list val) : gmap loc val :=
  (kmap (λ i, l +ₗ i) (map_seqZ 0 vs)).

Section array.
  Lemma array_nil l :
    array l [] = ∅.
  Proof. rewrite /array/=. apply kmap_empty. Qed.
  Lemma array_cons l v vs :
    array l (v::vs) = <[l:=v]> $ array (l +ₗ 1) vs.
  Proof.
    rewrite /array/= kmap_insert offset_loc_0. f_equal.
    apply map_eq => ?. apply option_eq => ?.
    rewrite !lookup_kmap_Some. setoid_rewrite lookup_map_seqZ_Some.
    split => -[i [? [? <-]]]; simplify_eq.
    - eexists (Z.pred i). split!; [|lia|f_equal; lia].
      unfold offset_loc. destruct l => /=. f_equal. lia.
    - eexists (Z.succ i). split!; [|lia|f_equal; lia].
      unfold offset_loc. destruct l => /=. f_equal. lia.
  Qed.

  Lemma array_app l vs1 vs2 :
    array l (vs1 ++ vs2) = array l vs1 ∪ array (l +ₗ length vs1) vs2.
  Proof.
    elim: vs1 l. { move => ?/=. by rewrite array_nil offset_loc_0 left_id_L. }
    move => v vs1 IH l /=. rewrite !array_cons -insert_union_l.
    rewrite IH. do 3 f_equal. apply loc_eq. split!. lia.
  Qed.

  Lemma array_insert l1 l2 v vs :
    l1.1 = l2.1 →
    l2.2 ≤ l1.2 < l2.2 + length vs →
    <[l1:=v]> $ array l2 vs = array l2 (<[Z.to_nat (l1.2 - l2.2):=v]>vs).
  Proof.
    move => ??. have {1} -> : l1 = l2 +ₗ Z.to_nat (l1.2 - l2.2).
    { unfold offset_loc. destruct l1, l2; simplify_eq/=. f_equal. lia. }
    rewrite /array/= map_seqZ_insert. 2: lia.
    by rewrite kmap_insert.
  Qed.

  Lemma array_lookup_None l l' vs :
    array l vs !! l' = None ↔ (l.1 = l'.1 → l'.2 < l.2 ∨ l.2 + length vs ≤ l'.2).
  Proof.
    rewrite /array.
    rewrite lookup_kmap_None.
    setoid_rewrite lookup_map_seqZ_None.
    split.
    - move => Hi Heq.
      exploit (Hi (l'.2 - l.2)). { unfold offset_loc. destruct l, l'; simplify_eq/=. f_equal. lia. }
      lia.
    - move => Hi ??. simplify_eq/=. lia.
  Qed.

  Lemma array_lookup_is_Some l l' vs :
    is_Some (array l vs !! l') ↔ l.1 = l'.1 ∧ l.2 ≤ l'.2 < l.2 + length vs.
  Proof. rewrite -not_eq_None_Some array_lookup_None. naive_solver lia. Qed.
End array.

Definition fnsUR : cmra :=
  agreeR (gmapO string (leibnizO fndef)).

Definition to_fns : gmap string fndef → fnsUR :=
  to_agree.


Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_mapsto_ghost_map_preG :: ghost_mapG Σ loc val;
  rec_alloc_ghost_map_preG :: ghost_mapG Σ prov Z;
  rec_fn_preG :: inG Σ fnsUR;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_mapsto_ghost_mapG :: ghost_mapG Σ loc val;
  rec_alloc_ghost_mapG :: ghost_mapG Σ prov Z;
  rec_fnG :: inG Σ fnsUR;
  rec_mapsto_name : gname;
  rec_alloc_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[ ghost_mapΣ loc val; ghost_mapΣ prov Z; GFunctor fnsUR ].

Global Instance subG_recΣ Σ :
  subG recΣ Σ → recPreGS Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{!recGS Σ}.

  Definition rec_mapsto_def (l : loc) (q : dfrac) (v : val) : iProp Σ :=
    ghost_map_elem rec_mapsto_name l q v.
  Local Definition rec_mapsto_aux : seal (@rec_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_mapsto := rec_mapsto_aux.(unseal).
  Local Definition rec_mapsto_unseal :
    @rec_mapsto = @rec_mapsto_def := rec_mapsto_aux.(seal_eq).

  Definition rec_mapsto_auth (h : gmap loc val) : iProp Σ :=
    ghost_map_auth rec_mapsto_name 1 h.

  Definition rec_alloc_def (l : loc) (sz : Z) : iProp Σ :=
    ⌜l.2 = 0⌝ ∗ ghost_map_elem rec_alloc_name l.1 (DfracOwn 1) sz.
  Local Definition rec_alloc_aux : seal (@rec_alloc_def).
  Proof. by eexists. Qed.
  Definition rec_alloc := rec_alloc_aux.(unseal).
  Local Definition rec_alloc_unseal :
    @rec_alloc = @rec_alloc_def := rec_alloc_aux.(seal_eq).

  Definition rec_alloc_auth (h : gset loc) : iProp Σ :=
    ∃ m,
    ⌜∀ p sz, m !! p = Some sz → sz > 0⌝ ∗
    ⌜∀ p sz, m !! p = Some sz → ∀ l', l'.1 = p → l' ∈ h ↔ 0 ≤ l'.2 < sz⌝ ∗
    ghost_map_auth rec_alloc_name 1 m.

  Definition rec_fn_auth (fns : gmap string fndef) : iProp Σ :=
    own rec_fn_name (to_fns fns).
  Definition rec_fn_mapsto_def (f : string) (fn : option fndef) : iProp Σ :=
    ∃ fns, ⌜fns !! f = fn⌝ ∗ rec_fn_auth fns.
  Local Definition rec_fn_mapsto_aux : seal (@rec_fn_mapsto_def).
  Proof. by eexists. Qed.
  Definition rec_fn_mapsto := rec_fn_mapsto_aux.(unseal).
  Local Definition rec_fn_mapsto_unseal :
    @rec_fn_mapsto = @rec_fn_mapsto_def := rec_fn_mapsto_aux.(seal_eq).

  Definition rec_state_interp (σ : rec_state) (os : option heap_state) : iProp Σ :=
    rec_fn_auth (st_fns σ) ∗
    if os is Some h then
      ⌜st_heap σ = h⌝
    else
      rec_mapsto_auth (h_heap (st_heap σ)) ∗ rec_alloc_auth (dom (h_heap (st_heap σ))).
End definitions.

Notation "l ↦ v" := (rec_mapsto l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "f ↪ fn" := (rec_fn_mapsto f fn)
  (at level 20, format "f  ↪  fn") : bi_scope.

Local Ltac unseal := rewrite
  ?rec_mapsto_unseal /rec_mapsto_def /rec_mapsto_auth
  ?rec_alloc_unseal /rec_alloc_def /rec_alloc_auth
  ?rec_fn_mapsto_unseal /rec_fn_mapsto_def /rec_fn_auth.

Section lemmas.
  Context `{!recGS Σ}.

  (** mapsto ghost state  *)
  Lemma rec_mapsto_lookup h l v :
    rec_mapsto_auth h -∗ l ↦ v -∗ ⌜h !! l = Some v⌝.
  Proof. unseal. apply ghost_map_lookup. Qed.

  Lemma rec_mapsto_update h l v v' :
    rec_mapsto_auth h -∗ l ↦ v ==∗ rec_mapsto_auth (alter (λ _, v') l h) ∗ l ↦ v'.
  Proof.
    iIntros "Hh Hl".
    iDestruct (rec_mapsto_lookup with "Hh Hl") as %?.
    unseal.
    iMod (ghost_map_update with "Hh Hl") as "[? $]".
    have -> : (<[l:=v']> h) = (alter (λ _ : val, v') l h); [|done].
    apply partial_alter_ext => ??. by simplify_map_eq.
  Qed.

  Lemma rec_mapsto_alloc_big h' h :
    h' ##ₘ h →
    rec_mapsto_auth h ==∗
    rec_mapsto_auth (h' ∪ h) ∗ [∗ map] l↦v∈h', l ↦ v.
  Proof. unseal. apply ghost_map_insert_big. Qed.

  Local Transparent heap_alloc_h.
  Lemma rec_mapsto_alloc h l sz :
    heap_is_fresh h l →
    rec_mapsto_auth (h_heap h) ==∗
    rec_mapsto_auth (h_heap (heap_alloc h l sz)) ∗ [∗ list] o∈seqZ 0 sz, (l +ₗ o) ↦ 0.
  Proof.
    iIntros (Ha) "Hh".
    iMod (rec_mapsto_alloc_big with "Hh") as "[$ ?]".
    { apply map_disjoint_list_to_map_l. apply Forall_forall => -[??] /= /elem_of_list_fmap[?[??]].
      simplify_eq. apply eq_None_not_Some => /heap_wf. unfold heap_is_fresh in *. naive_solver. }
    rewrite big_sepM_list_to_map. 2: {
      apply NoDup_alt => ???. do 2 setoid_rewrite list_lookup_fmap_Some.
      setoid_rewrite lookup_seqZ => ??. naive_solver lia. }
    by rewrite big_sepL_fmap.
  Qed.
  Local Opaque heap_alloc_h.

  Lemma rec_mapsto_alloc_list h ls h' szs :
    heap_alloc_list szs ls h h' →
    rec_mapsto_auth (h_heap h) ==∗
    rec_mapsto_auth (h_heap h') ∗ ([∗ list] l;n∈ls; szs, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0).
  Proof.
    iIntros (Ha) "Hh".
    iInduction (szs) as [|sz szs] "IH" forall (ls h h' Ha); destruct!/=. { by iFrame. }
    iMod (rec_mapsto_alloc with "Hh") as "[Hh $]"; [done|].
    iApply ("IH" with "[//] Hh").
  Qed.

  Lemma seqZ_succ m i :
    0 ≤ i →
    seqZ m (Z.succ i) = seqZ m i ++ [m + i].
  Proof. intros ?. by rewrite -(Z2Nat.id i) // -Nat2Z.inj_succ seqZ_S. Qed.

  Lemma rec_mapsto_free h l sz :
    heap_range h l sz →
    0 ≤ sz →
    rec_mapsto_auth (h_heap h) -∗
    ([∗ list] o∈seqZ 0 sz, ∃ v, (l +ₗ o) ↦ v) ==∗
    rec_mapsto_auth (h_heap (heap_free h l)).
  Proof.
    iIntros (Hr Hsz) "Ha Hl".
    iAssert (∃ vs, ⌜sz = length vs⌝ ∗ [∗ map] l↦v∈array l vs, l↦v)%I with "[Hl]" as (vs ?) "Hl".
    { clear Hr.
      iInduction sz as [|sz|sz] "IH" using (Z.succ_pred_induction 0) forall (Hsz).
      { iExists []. iSplit!. } 2: { lia. }
      rewrite seqZ_succ // big_sepL_app /=. iDestruct "Hl" as "[Hl [[%v Hv] _]]". rewrite Z.add_0_l.
      iDestruct ("IH" with "[//] [$]") as (vs ?) "?". subst.
      iExists (vs ++ [v]). iSplit; [iPureIntro; rewrite app_length /=; lia|].
      rewrite array_app array_cons array_nil. iApply (big_sepM_union_2 with "[$]").
      by iApply (big_sepM_insert_2 with "[Hv]").
    }
    unseal.
    iMod (ghost_map_delete_big with "Ha [$]") => /=.
    have -> : (h_heap h ∖ array l vs = (filter (λ '(l', _), l'.1 ≠ l.1) (h_heap h))); [|done].
    apply map_eq => i. apply option_eq => v.
    rewrite map_lookup_filter_Some lookup_difference_Some.
    rewrite array_lookup_None.
    unfold heap_range in Hr. split; [|naive_solver lia].
    move => [Hh ?]. split!. move => ?. have := Hr i. rewrite Hh /is_Some. naive_solver lia.
  Qed.

  (** alloc ghost state  *)
  Lemma rec_alloc_fake h :
    rec_alloc_auth ∅ -∗ rec_alloc_auth h.
  Proof.
    unseal. iDestruct 1 as (m Hsz Hl) "?".
    have -> : m = ∅. {
      apply map_empty => i. apply eq_None_ne_Some_2 => ??.
      have := Hl _ _ ltac:(done) (i, 0). set_unfold. naive_solver lia. }
    iExists ∅. iFrame. iPureIntro. naive_solver.
  Qed.

  Local Transparent heap_alloc_h.
  Lemma rec_alloc_alloc h l sz :
    heap_is_fresh h l →
    0 < sz →
    rec_alloc_auth (dom (h_heap h)) ==∗
    rec_alloc_auth (dom (h_heap (heap_alloc h l sz))) ∗ rec_alloc l sz.
  Proof.
    iIntros ([Hn Hl0] ?) "Ha". unseal.
    iDestruct "Ha" as (m Hsz Hin) "Ha".
    iMod (ghost_map_insert l.1 sz with "Ha") as "[Ha ?]". {
      apply eq_None_not_Some => -[??].
      have [//|_ Hdom]:= Hin _ _ ltac:(done) (l.1, 0).
      apply Hn. apply (heap_wf _ (l.1, 0)). apply elem_of_dom. naive_solver lia.
    }
    iModIntro. iFrame. iSplit!; [..|done].
    - move => ?? /lookup_insert_Some. naive_solver lia.
    - move => ?? /lookup_insert_Some[[??]|[??]] l' ?; simplify_eq.
      + rewrite dom_union_L elem_of_union dom_list_to_map_L.
        set_unfold. setoid_rewrite elem_of_seq.
        split; move => ?; destruct!/=.
        * lia.
        * revert select (_ ∈ _) => /elem_of_dom/heap_wf. congruence.
        * left.  eexists (l +ₗ l'.2, _) => /=. split. { apply loc_eq. split!. lia. }
          eexists _. split; [done|]. eexists (Z.to_nat l'.2). lia.
      + rewrite dom_union_L elem_of_union dom_list_to_map_L.
        split; move => ?; destruct!/=. 1: set_solver. all: naive_solver lia.
  Qed.
  Local Opaque heap_alloc_h.

  Lemma rec_alloc_alloc_list szs h h' ls :
    heap_alloc_list szs ls h h' →
    Forall (λ sz, 0 < sz) szs →
    rec_alloc_auth (dom (h_heap h)) ==∗
    rec_alloc_auth (dom (h_heap h')) ∗ [∗ list] l;sz∈ls;szs, rec_alloc l sz.
  Proof.
    iIntros (Ha Hall) "Ha".
    iInduction (szs) as [|sz szs] "IH" forall (ls h h' Ha Hall); destruct!/=. { by iFrame. }
    decompose_Forall.
    iMod (rec_alloc_alloc with "Ha") as "[Ha $]"; [done..|].
    iApply ("IH" with "[//] [//] Ha").
  Qed.

  Lemma rec_alloc_range h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz -∗
    ⌜heap_range h l sz⌝.
  Proof.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iPureIntro. setoid_rewrite elem_of_dom in Hl.
    move => ??. rewrite Hl //. lia.
  Qed.

  Lemma rec_alloc_size h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz -∗
    ⌜0 < sz⌝.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iDestruct (ghost_map_lookup with "[$] [$]") as %?.
    iPureIntro. naive_solver lia.
  Qed.

  Lemma rec_alloc_free h l sz :
    rec_alloc_auth (dom (h_heap h)) -∗
    rec_alloc l sz ==∗
    rec_alloc_auth (dom (h_heap (heap_free h l))).
  Proof.
    unseal. iDestruct 1 as (p Hsz Hl) "?". iIntros "[% ?]".
    iMod (ghost_map_delete with "[$] [$]"). iModIntro. iExists _. iFrame.
    iPureIntro. split => ?? /lookup_delete_Some. 1: naive_solver.
    move => [??] ?? /=. rewrite -Hl //.
    rewrite !elem_of_dom map_lookup_filter_true //. naive_solver.
  Qed.

  Lemma rec_alloc_free_list h ls szs :
    rec_mapsto_auth (h_heap h) -∗
    rec_alloc_auth (dom (h_heap h)) -∗
    ([∗ list] l;sz ∈ ls;szs, rec_alloc l sz) -∗
    ([∗ list] l;n ∈ ls;szs, [∗ list] o ∈ seqZ 0 n, ∃ v0 : val, (l +ₗ o) ↦ v0) ==∗
    ∃ h', ⌜heap_free_list (zip ls szs) h h'⌝ ∗ rec_mapsto_auth (h_heap h') ∗ rec_alloc_auth (dom (h_heap h')).
  Proof.
    iIntros "Hh Ha Has Hls".
    iInduction (szs) as [|sz szs] "IH" forall (h ls).
    { iModIntro. iDestruct (big_sepL2_nil_inv_r with "Has") as %?. simplify_eq/=. iSplit!. iFrame. }
    iDestruct (big_sepL2_cons_inv_r with "Has") as (???) "[??]".
    iDestruct (big_sepL2_cons_inv_r with "Hls") as (???) "[??]". simplify_eq/=.
    iDestruct (rec_alloc_range with "[$] [$]") as %?.
    iDestruct (rec_alloc_size with "[$] [$]") as %?.
    iMod (rec_mapsto_free with "Hh [$]") as "Hh"; [done|lia|].
    iMod (rec_alloc_free with "Ha [$]") as "Ha".
    iMod ("IH" with "Hh Ha [$] [$]") as (??) "[??]". iModIntro. iSplit!; [done|]. iFrame.
  Qed.

  (** fn ghost state  *)
  Global Instance rec_fn_auth_pers fns : Persistent (rec_fn_auth fns).
  Proof. unseal. apply _. Qed.

  Global Instance rec_fn_mapsto_pers f fn : Persistent (f ↪ fn).
  Proof. unseal. apply _. Qed.

  Lemma rec_fn_auth_agree fns1 fns2 :
    rec_fn_auth fns1 -∗ rec_fn_auth fns2 -∗ ⌜fns1 = fns2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hvalid.
    move: Hvalid => /to_agree_op_valid.
    by fold_leibniz.
  Qed.

  Lemma rec_fn_intro f fn fns :
    fns !! f = fn → rec_fn_auth fns -∗ f ↪ fn.
  Proof. unseal. iIntros (?) "Htbl". iExists _. by iFrame. Qed.

  Lemma rec_fn_lookup f fn fns :
    rec_fn_auth fns -∗ f ↪ fn -∗ ⌜fns !! f = fn⌝.
  Proof.
    unseal. iIntros "Htbl Hf".
    iDestruct "Hf" as (fns2 ?) "Hf".
    by iDestruct (rec_fn_auth_agree with "Htbl Hf") as %->.
  Qed.

End lemmas.

Lemma recgs_alloc `{!recPreGS Σ} fns :
  ⊢ |==> ∃ H : recGS Σ, rec_mapsto_auth ∅ ∗ rec_alloc_auth ∅ ∗ rec_fn_auth fns.
Proof.
  iMod (own_alloc (to_fns fns)) as (γf) "#Hfns" => //.
  iMod (ghost_map_alloc (V:=val)) as (γh) "[??]".
  iMod (ghost_map_alloc (V:=Z)) as (γa) "[??]".

  iModIntro. iExists (RecGS _ _ _ _ γh γa γf). iFrame "#∗".
  iExists ∅. iFrame. iPureIntro; split!.
Qed.
