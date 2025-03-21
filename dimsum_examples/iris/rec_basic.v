From iris.algebra Require Import big_op gmap frac agree dfrac_agree.
From iris.base_logic.lib Require Import ghost_map.
From dimsum.core.iris Require Export iris.
From dimsum.examples Require Export rec heapUR.
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
    - move => Hi ??. simplify_eq/=. naive_solver lia.
  Qed.

  Lemma array_lookup_is_Some l l' vs :
    is_Some (array l vs !! l') ↔ l.1 = l'.1 ∧ l.2 ≤ l'.2 < l.2 + length vs.
  Proof.
    rewrite -not_eq_None_Some array_lookup_None.
    destruct (decide (l.1 = l'.1)); naive_solver lia.
  Qed.
End array.

Definition fnsUR : cmra :=
  agreeR (gmapO string (leibnizO fndef)).

Definition to_fns : gmap string fndef → fnsUR :=
  to_agree.


Class recPreGS (Σ : gFunctors) := RecPreGS {
  rec_heapUR_preG :: inG Σ heapUR;
  rec_fn_preG :: inG Σ fnsUR;
}.

Class recGS (Σ : gFunctors) := RecGS {
  rec_heapUR_G :: inG Σ heapUR;
  rec_fnG :: inG Σ fnsUR;
  rec_heap_name : gname;
  rec_fn_name : gname;
}.

Definition recΣ : gFunctors :=
  #[GFunctor heapUR; GFunctor fnsUR ].

Global Instance subG_recΣ Σ :
  subG recΣ Σ → recPreGS Σ.
Proof. solve_inG. Qed.

Notation "l ↦ v" := (heapUR_ptsto (bi_own_own rec_heap_name) l (DfracOwn 1) v)
  (at level 20, format "l  ↦  v") : bi_scope.
Notation "p ↦∗ b" := (heapUR_block (bi_own_own rec_heap_name) p (DfracOwn 1) b)
  (at level 20, format "p  ↦∗  b") : bi_scope.
Notation "p ⤚ d" := (heapUR_dom (bi_own_own rec_heap_name) p (DfracOwn 1) d)
  (at level 20, format "p  ⤚  d") : bi_scope.
Notation rec_inv := (heapUR_inv (bi_own_own rec_heap_name)).

Section definitions.
  Context `{!recGS Σ}.

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
      rec_inv (st_heap σ).
End definitions.

Notation "f ↪ fn" := (rec_fn_mapsto f fn)
  (at level 20, format "f  ↪  fn") : bi_scope.

Local Ltac unseal := rewrite
  ?rec_fn_mapsto_unseal /rec_fn_mapsto_def /rec_fn_auth.

Section lemmas.
  Context `{!recGS Σ}.

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
  ⊢ |==> ∃ H : recGS Σ, rec_inv ∅ ∗ rec_fn_auth fns.
Proof.
  iMod (own_alloc (to_fns fns)) as (γf) "#Hfns" => //.
  iMod (own_alloc heapUR_init) as (γh) "Hh"; [apply heapUR_init_valid|].
  iDestruct (heapUR_init_own (bi_own_own γh) with "Hh") as "?".
  iModIntro. iExists (RecGS _ _ _ γh γf). iFrame "#∗".
Qed.
