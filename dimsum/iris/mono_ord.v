From iris.algebra Require Export cmra local_updates proofmode_classes auth.
From iris.algebra Require Import updates.
From iris.prelude Require Import options.
From dimsum.core Require Export ordinal.

(** This file is based min_nat in iris/algebra/numbers.v and mono_nat in iris/algebra/lib/mono_nat.v . *)

(** * Ordinals with a maximal element *)
(** The maximal element gives us the unit for the RA. *)
Inductive ordinal_max :=
| OrdMax (o : ordinal) | OrdMaxMax.
Definition ord_max_min (x y : ordinal_max) : ordinal_max :=
  if x is OrdMax xo then
    if y is OrdMax yo then
      OrdMax (o_min xo yo)
    else
      x
  else
    y.

Global Instance ord_max_subseteq : SubsetEq ordinal_max :=
  λ x y, if y is OrdMax yo then
           if x is OrdMax xo then xo ⊆ yo else False
         else True.

Definition ord_max_lt (x y : ordinal_max) : Prop :=
  if x is OrdMax xo then
    if y is OrdMax yo then oS xo ⊆ yo else True
  else False.

Global Instance ord_max_equiv : Equiv ordinal_max := λ n1 n2, n1 ⊆ n2 ∧ n2 ⊆ n1.

Global Instance ord_max_preorder : PreOrder (⊆@{ordinal_max}).
Proof.
  constructor.
  - move => n. destruct n => //. by rewrite /subseteq/=.
  - move => x y z. destruct x,y,z => //=. by rewrite /subseteq/= => ->.
Qed.
Global Instance ord_max_equiv_equiv : Equivalence (≡@{ordinal_max}).
Proof.
  constructor.
  - done.
  - move => ?? [??]. done.
  - move => ??? [??] [??]. by split; etrans.
Qed.

Lemma ord_max_min_mono n m n' m':
  n ⊆ n' →
  m ⊆ m' →
  ord_max_min n m ⊆ ord_max_min n' m'.
Proof.
  destruct n,m,n',m' => //=; rewrite /subseteq/=.
  - apply o_min_mono.
  - move => ??. by etrans; [apply o_min_le_l|].
  - move => ??. by etrans; [apply o_min_le_r|].
Qed.

Global Instance ord_max_mono_proper :
  Proper ((⊆) ==> (⊆) ==> (⊆)) ord_max_min.
Proof. move => ??????. by apply: ord_max_min_mono. Qed.
Global Instance o_mono_flip_proper :
  Proper (flip (⊆) ==> flip (⊆) ==> flip (⊆)) ord_max_min.
Proof. move => ??????. by apply: ord_max_min_mono. Qed.
Global Instance o_mono_equiv_proper :
  Proper ((≡) ==> (≡) ==> (≡)) ord_max_min.
Proof. move => ?? [Hn1 Hn2] ?? [Hm1 Hm2]. split; by apply: ord_max_min_mono. Qed.

Lemma ord_max_min_comm n m:
  ord_max_min n m ≡ ord_max_min m n.
Proof. destruct n, m => //. apply o_min_comm. Qed.

Lemma ord_max_min_assoc n m p:
  ord_max_min n (ord_max_min m p) ≡ ord_max_min (ord_max_min n m) p.
Proof. destruct n, m, p => //. apply o_min_assoc. Qed.

Lemma ord_max_min_le_l n m:
  ord_max_min n m ⊆ n.
Proof. destruct n, m => //. apply o_min_le_l. Qed.
Lemma ord_max_min_le_r n m:
  ord_max_min n m ⊆ m.
Proof. destruct n, m => //. apply o_min_le_r. Qed.

Lemma ord_max_min_l n m:
  n ⊆ m → ord_max_min n m ≡ n.
Proof. destruct m, n => //. apply o_min_l. Qed.
Lemma ord_max_min_r n m:
  m ⊆ n → ord_max_min n m ≡ m.
Proof. destruct m, n => //. apply o_min_r. Qed.

Lemma ord_max_min_id n:
  ord_max_min n n ≡ n.
Proof. by apply ord_max_min_r. Qed.

Lemma ord_max_lt_mono n m n' m':
  n ⊆ n' →
  m' ⊆ m →
  ord_max_lt n' m' →
  ord_max_lt n m.
Proof.
  destruct n,m,n',m' => //=. move => ???.
  etrans; [|done]. etrans; [|done]. by constructor.
Qed.

Lemma ord_max_lt_ind (P : ordinal_max → Prop):
  (∀ x : ordinal_max, (∀ y : ordinal_max, ord_max_lt y x → P y) → P x) → ∀ a, P a.
Proof.
  move => HP a. apply HP. move => [y _|//]. clear a.
  move: y. apply o_lt_ind. move => x IH. apply HP. move => [|//]. apply IH.
Qed.

(** ** Ordinals with [min] as the operation. *)
Record min_ord := MinOrd { min_ord_car : ordinal_max }.
Add Printing Constructor min_ord.

Global Instance min_ord_equiv : Equiv min_ord := λ x y, min_ord_car x ≡ min_ord_car y.
Global Instance min_ord_equivalence : Equivalence (≡@{min_ord}).
Proof. constructor => ? *; unfold equiv, min_ord_equiv in *; [done| done | by etrans ]. Qed.
Global Instance MinOrd_proper : Proper ((≡) ==> (≡)) MinOrd.
Proof. move => ???. done. Qed.

Canonical Structure min_ordO := discreteO min_ord.

Section min_ord.
  Local Instance min_ord_unit_instance : Unit min_ord := MinOrd OrdMaxMax.
  Local Instance min_ord_valid_instance : Valid min_ord := λ x, True.
  Local Instance min_ord_validN_instance : ValidN min_ord := λ n x, True.
  Local Instance min_ord_pcore_instance : PCore min_ord := Some.
  Local Instance min_ord_op_instance : Op min_ord := λ n m, MinOrd (ord_max_min (min_ord_car n) (min_ord_car m)).
  Definition min_ord_op_min x y : MinOrd x ⋅ MinOrd y = MinOrd (ord_max_min x y) := eq_refl.

  Lemma min_ord_included (x y : min_ord) :
    x ≼ y ↔ min_ord_car y ⊆ min_ord_car x.
  Proof.
    split.
    - intros [z [-> ?]]. simpl. by apply ord_max_min_le_l.
    - exists y. rewrite /op /min_ord_op_instance. symmetry. by apply ord_max_min_r.
  Qed.
  Lemma min_ord_ra_mixin : RAMixin min_ord.
  Proof.
    apply ra_total_mixin; apply _ || eauto.
    - intros [x] [?] [?] Heq. rewrite !min_ord_op_min. rewrite /equiv/min_ord_equiv/= in Heq. by rewrite Heq.
    - intros [x] [y] [z]. repeat rewrite min_ord_op_min. by apply ord_max_min_assoc.
    - intros [x] [y]. rewrite !min_ord_op_min. apply ord_max_min_comm.
    - intros [x]. rewrite min_ord_op_min. apply ord_max_min_id.
  Qed.
  Canonical Structure min_ordR : cmra := discreteR min_ord min_ord_ra_mixin.

  Global Instance min_ord_cmra_discrete : CmraDiscrete min_ordR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance min_ord_cmra_total : CmraTotal min_ordR.
  Proof. move => ?. done. Qed.

  Lemma min_ord_ucmra_mixin : UcmraMixin min_ord.
  Proof. split; try apply _ || done. Qed.
  Canonical Structure min_ordUR : ucmra := Ucmra min_ord min_ord_ucmra_mixin.

  Global Instance min_ord_core_id (x : min_ord) : CoreId x.
  Proof. by constructor. Qed.

  Lemma min_ord_local_update (x y x' : min_ord) :
    min_ord_car x' ⊆ min_ord_car x → (x,y) ~l~> (x',x').
  Proof.
    move: x y x' => [x] [y] [x'] /= Hle.
    rewrite local_update_discrete. move=> [[z]|] _ /=; last done.
    rewrite 2!min_ord_op_min. intros [Heq1 Heq2]; simpl in *.
    split; first done. rewrite ->Heq1 in Hle.
    split => /=.
    - apply ord_max_min_l. etrans; [done|]. apply ord_max_min_le_r.
    - apply ord_max_min_le_l.
  Qed.

  Global Instance : LeftAbsorb (≡) (MinOrd (OrdMax oO)) (⋅).
  Proof. move => [x]. rewrite min_ord_op_min. apply ord_max_min_l. destruct x => //. constructor. Qed.

  Global Instance : RightAbsorb (≡) (MinOrd (OrdMax oO)) (⋅).
  Proof. move => [x]. rewrite min_ord_op_min. apply ord_max_min_r. destruct x => //. constructor. Qed.

  Global Instance : IdemP (≡@{min_ord}) (⋅).
  Proof. intros [x]. rewrite min_ord_op_min. apply ord_max_min_id. Qed.

  Global Instance min_ord_is_op x y :
    IsOp (MinOrd (ord_max_min x y)) (MinOrd x) (MinOrd y).
  Proof. done. Qed.
End min_ord.

(** Authoritative CMRA over [min_ord]. The authoritative element is a
monotonically decreasing ord, while a fragment is a upper bound. *)

Definition mono_ord   := auth min_ordUR.
Definition mono_ordR  := authR min_ordUR.
Definition mono_ordUR := authUR min_ordUR.

(** [mono_ord_auth] is the authoritative element. The definition includes the
fragment at the same value so that lemma [mono_ord_included], which states that
[mono_ord_ub n ≼ mono_ord_auth q n], does not require a frame-preserving
update. *)
Definition mono_ord_auth (q : Qp) (n : ordinal_max) : mono_ord :=
  ●{#q} MinOrd n ⋅ ◯ MinOrd n.
Definition mono_ord_ub (n : ordinal_max) : mono_ord := ◯ MinOrd n.

Section mono_ord.
  Implicit Types (n : ordinal_max).

  Global Instance mono_ord_ub_core_id n : CoreId (mono_ord_ub n).
  Proof. apply _. Qed.

  Lemma mono_ord_auth_frac_op q1 q2 n :
    mono_ord_auth q1 n ⋅ mono_ord_auth q2 n ≡ mono_ord_auth (q1 + q2) n.
  Proof.
    rewrite /mono_ord_auth -dfrac_op_own auth_auth_dfrac_op.
    rewrite (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    by rewrite -core_id_dup (comm _ (◯ _)).
  Qed.

  Lemma mono_ord_ub_op n1 n2 :
    mono_ord_ub n1 ⋅ mono_ord_ub n2 = mono_ord_ub (ord_max_min n1 n2).
  Proof. rewrite -auth_frag_op min_ord_op_min //. Qed.

  Lemma mono_ord_auth_ub_op q n :
    mono_ord_auth q n ≡ mono_ord_auth q n ⋅ mono_ord_ub n.
  Proof.
    rewrite /mono_ord_auth /mono_ord_ub.
    rewrite -!assoc -auth_frag_op min_ord_op_min.
    do 3 f_equiv. symmetry. apply ord_max_min_id.
  Qed.

  (** rephrasing of [mono_ord_ub_op] useful for weakening a fragment to a
  larger upper-bound *)
  Lemma mono_ord_ub_op_le_l n n' :
    n ⊆ n' →
    mono_ord_ub n ≡ mono_ord_ub n' ⋅ mono_ord_ub n.
  Proof. intros. rewrite mono_ord_ub_op /mono_ord_ub. do 2 f_equiv. symmetry. by apply ord_max_min_r. Qed.

  Lemma mono_ord_auth_frac_valid q n : ✓ mono_ord_auth q n ↔ (q ≤ 1)%Qp.
  Proof.
    rewrite /mono_ord_auth auth_both_dfrac_valid_discrete /=. naive_solver.
  Qed.
  Lemma mono_ord_auth_valid n : ✓ mono_ord_auth 1 n.
  Proof. by apply auth_both_valid. Qed.

  Lemma mono_ord_auth_frac_op_valid q1 q2 n1 n2 :
    ✓ (mono_ord_auth q1 n1 ⋅ mono_ord_auth q2 n2) ↔ (q1 + q2 ≤ 1)%Qp ∧ n1 ≡ n2.
  Proof.
    rewrite /mono_ord_auth (comm _ (●{#q2} _)) -!assoc (assoc _ (◯ _)).
    rewrite -auth_frag_op (comm _ (◯ _)) assoc. split.
    - move=> /cmra_valid_op_l /auth_auth_dfrac_op_valid => -[? ?]. naive_solver.
    - intros [? ->]. rewrite -core_id_dup -auth_auth_dfrac_op.
      by apply auth_both_dfrac_valid_discrete.
  Qed.
  Lemma mono_ord_auth_op_valid n1 n2 :
    ✓ (mono_ord_auth 1 n1 ⋅ mono_ord_auth 1 n2) ↔ False.
  Proof. rewrite mono_ord_auth_frac_op_valid. naive_solver. Qed.

  Lemma mono_ord_both_frac_valid q n m :
    ✓ (mono_ord_auth q n ⋅ mono_ord_ub m) ↔ (q ≤ 1)%Qp ∧ n ⊆ m.
  Proof.
    rewrite /mono_ord_auth /mono_ord_ub -assoc -auth_frag_op.
    rewrite auth_both_dfrac_valid_discrete min_ord_included /=.
    split.
    - move => [?[??]]. split; [done|]. etrans; [done|]. apply ord_max_min_le_r.
    - move => [??]. split; [done|]. split; [|done]. by apply ord_max_min_l.
  Qed.
  Lemma mono_ord_both_valid n m :
    ✓ (mono_ord_auth 1 n ⋅ mono_ord_ub m) ↔ n ⊆ m.
  Proof. rewrite mono_ord_both_frac_valid. naive_solver. Qed.

  Lemma mono_ord_ub_mono n1 n2 : n2 ⊆ n1 → mono_ord_ub n1 ≼ mono_ord_ub n2.
  Proof. intros. by apply auth_frag_mono, min_ord_included. Qed.

  Lemma mono_ord_included q n : mono_ord_ub n ≼ mono_ord_auth q n.
  Proof. apply cmra_included_r. Qed.

  Lemma mono_ord_update {n} n' :
    n' ⊆ n →
    mono_ord_auth 1 n ~~> mono_ord_auth 1 n'.
  Proof.
    intros. rewrite /mono_ord_auth /mono_ord_ub.
    by apply auth_update, min_ord_local_update.
  Qed.
End mono_ord.

Global Typeclasses Opaque mono_ord_auth mono_ord_ub.
