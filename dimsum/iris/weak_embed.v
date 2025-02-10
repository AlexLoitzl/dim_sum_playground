From iris.bi Require Import bi.
From iris.algebra Require Import cmra updates.
From iris.proofmode Require Import proofmode.

Set Default Proof Using "Type".

Record WeakEmbed (A B : Type) := {
  weak_embed : A → B;
  weak_embed_tok : B;
}.
Global Arguments weak_embed {_ _} _ _%_I : simpl never.
Global Arguments weak_embed_tok {_ _} _ : simpl never.
Notation "⌈ P @ W ⌉" := (weak_embed W P) (format "⌈ P  @  W ⌉") : bi_scope.
Notation "⌈{ W }⌉" := (weak_embed_tok W) (format "⌈{ W }⌉") : bi_scope.
Global Instance: Params (@weak_embed) 2 := {}.
Global Typeclasses Opaque weak_embed.
Global Typeclasses Opaque weak_embed_tok.


(* Mixins allow us to create instances easily without having to use Program *)
Record BiWeakEmbedMixin (PROP1 PROP2 : bi) (W : WeakEmbed PROP1 PROP2) := {
  bi_weak_embed_mixin_ne : NonExpansive (weak_embed W);
  bi_weak_embed_mixin_mono : Proper ((⊢) ==> (⊢)) (weak_embed W);
  (* The following does not hold for sat. *)
  (* bi_weak_embed_mixin_emp_valid_inj (P : PROP1) :
    (⊢@{PROP2} ⌈P @ E⌉) → ⊢ P; *)
  (* TODO: Do we care about the following? *)
  (* bi_weak_embed_mixin_interal_inj {PROP' : bi} `{!BiInternalEq PROP'} (P Q : PROP1) :
    ⌈P @ E⌉ ≡ ⌈Q @ E⌉ ⊢@{PROP'} (P ≡ Q); *)
  bi_weak_embed_mixin_emp : ⌈emp @ W⌉ ⊣⊢@{PROP2} emp;
  (* TODO: Is the following necessary? *)
  bi_weak_embed_mixin_True : True ⊢@{PROP2} ⌈True @ W⌉;
  (* This does not hold for sat since it requires commuting ∃ and → *)
  (* bi_weak_embed_mixin_impl_2 (P Q : PROP1) : *)
    (* (⌈P @ W⌉ → ⌈Q @ W⌉) ⊢@{PROP2} ⌈P → Q @ W⌉; *)
  (* This does not hold for sat since it requires commuting ∃ and ∀ *)
  (* bi_weak_embed_mixin_forall_2 A (Φ : A → PROP1) : *)
    (* (∀ x, ⌈Φ x @ W⌉) ⊢@{PROP2} ⌈∀ x, Φ x @ W⌉; *)
  bi_weak_embed_mixin_and_2 P Q :
    (⌈P @ W⌉ ∧ ⌈Q @ W⌉) ⊢@{PROP2} ⌈P ∧ Q @ W⌉;
  bi_weak_embed_mixin_exist_1 A (Φ : A → PROP1) :
    ⌈∃ x, Φ x @ W⌉ ⊢@{PROP2} ∃ x, ⌈Φ x @ W⌉;
  bi_weak_embed_mixin_sep (P Q : PROP1) :
    ⌈P ∗ Q @ W⌉ ⊣⊢@{PROP2} ⌈P @ W⌉ ∗ ⌈Q @ W⌉;
  (* This does not hold for sat since it requires commuting ∃ and -∗ *)
  (* bi_weak_embed_mixin_wand_2 (P Q : PROP1) : *)
  (*   (⎡P⎤ -∗ ⎡Q⎤) ⊢@{PROP2} ⎡P -∗ Q⎤; *)
  bi_weak_embed_mixin_persistently_1 (P : PROP1) :
    ⌈<pers> P @ W⌉ ⊢@{PROP2} <pers> ⌈P @ W⌉;
  (* TODO: Does this hold for sat? *)
  (* bi_weak_embed_mixin_persistently_2 (P : PROP1) : *)
    (* <pers> ⌈P @ W⌉ ⊢@{PROP2} ⌈<pers> P @ W⌉; *)
}.

Record BiWeakEmbed (PROP1 PROP2 : bi) := {
  bi_weak_embed_embed :> WeakEmbed PROP1 PROP2;
  bi_weak_embed_mixin : BiWeakEmbedMixin PROP1 PROP2 bi_weak_embed_embed;
}.
Global Arguments bi_weak_embed_embed : simpl never.


Definition weak_embed_bupd {PROP1 PROP2 : bi} (W : WeakEmbed PROP1 PROP2)
  `{!BiBUpd PROP2} (P : PROP2) : PROP2 :=
  ⌈{W}⌉ ==∗ ⌈{W}⌉ ∗ P.
Global Typeclasses Opaque weak_embed_bupd.

Notation "|==>⌈ W ⌉ Q" := (weak_embed_bupd W Q)
  (at level 99, Q at level 200, format "'[  ' |==>⌈ W ⌉  '/' Q ']'") : bi_scope.
Notation "P ==∗⌈ W ⌉ Q" := (P -∗ |==>⌈W⌉ Q)%I
  (at level 99, Q at level 200, format "'[' P  ==∗⌈ W ⌉  '/' Q ']'") : bi_scope.
Notation "P ==∗⌈ W ⌉ Q" := (P -∗ |==>⌈W⌉ Q) : stdpp_scope.

Class BiWeakEmbedBUpd {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2)
    `{!BiBUpd PROP1, !BiBUpd PROP2} :=
  weak_embed_bupd_bupd P : ⌈|==> P @ W⌉ ==∗⌈W⌉ ⌈P @ W⌉.
Global Hint Mode BiWeakEmbedBUpd ! ! ! - - : typeclass_instances.


Section weak_embed_laws.
  Context {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2).
  Local Notation "⌈ P ⌉" := (weak_embed W P) : bi_scope.
  Implicit Types P : PROP1.

  Global Instance weak_embed_ne n : Proper (dist n ==> dist n) (weak_embed W).
  Proof. eapply bi_weak_embed_mixin_ne, bi_weak_embed_mixin. Qed.
  Global Instance weak_embed_mono : Proper ((⊢) ==> (⊢)) (weak_embed W).
  Proof. eapply bi_weak_embed_mixin_mono, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_emp : ⌈emp⌉ ⊣⊢ emp.
  Proof. eapply bi_weak_embed_mixin_emp, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_True : True ⊢ ⌈True⌉.
  Proof. eapply bi_weak_embed_mixin_True, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_and_2 P Q : ⌈P⌉ ∧ ⌈Q⌉ ⊢ ⌈P ∧ Q⌉.
  Proof. eapply bi_weak_embed_mixin_and_2, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_exist_1 A (Φ : A → PROP1) : ⌈∃ x, Φ x⌉ ⊢ ∃ x, ⌈Φ x⌉.
  Proof. eapply bi_weak_embed_mixin_exist_1, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_sep P Q : ⌈P ∗ Q⌉ ⊣⊢ ⌈P⌉ ∗ ⌈Q⌉.
  Proof. eapply bi_weak_embed_mixin_sep, bi_weak_embed_mixin. Qed.
  Lemma weak_embed_persistently_1 P : ⌈<pers> P⌉ ⊢ <pers> ⌈P⌉.
  Proof. eapply bi_weak_embed_mixin_persistently_1, bi_weak_embed_mixin. Qed.
End weak_embed_laws.

Section weak_embed.
  Context {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2).
  Local Notation "⌈ P ⌉" := (weak_embed W P) : bi_scope.
  Implicit Types P Q R : PROP1.

  Global Instance weak_embed_proper : Proper ((≡) ==> (≡)) (weak_embed W).
  Proof. move => ?? Heq. apply (anti_symm (⊢)); apply weak_embed_mono; by rewrite Heq. Qed.
  Global Instance weak_embed_flip_mono : Proper (flip (⊢) ==> flip (⊢)) (weak_embed W).
  Proof. solve_proper. Qed.

  Lemma weak_embed_emp_valid_2 (P : PROP1) : (⊢ P) → (⊢ ⌈P⌉).
  Proof. rewrite /bi_emp_valid=> HP. by rewrite -HP -weak_embed_emp. Qed.

  Lemma weak_embed_forall_1 A (Φ : A → PROP1) : ⌈∀ x, Φ x⌉ ⊢ ∀ x, ⌈Φ x⌉.
  Proof. apply bi.forall_intro=>?. by rewrite bi.forall_elim. Qed.
  Lemma weak_embed_exist A (Φ : A → PROP1) : ⌈∃ x, Φ x⌉ ⊣⊢ ∃ x, ⌈Φ x⌉.
  Proof.
    apply bi.equiv_entails; split; [apply weak_embed_exist_1|].
    apply bi.exist_elim=>?. by rewrite -bi.exist_intro.
  Qed.
  Lemma weak_embed_and_1 P Q : ⌈P ∧ Q⌉ ⊢ ⌈P⌉ ∧ ⌈Q⌉.
  Proof. rewrite !bi.and_alt weak_embed_forall_1. by f_equiv=>-[]. Qed.
  Lemma weak_embed_and P Q : ⌈P ∧ Q⌉ ⊣⊢ ⌈P⌉ ∧ ⌈Q⌉.
  Proof. apply bi.equiv_entails. eauto using weak_embed_and_1, weak_embed_and_2. Qed.
  Lemma weak_embed_or P Q : ⌈P ∨ Q⌉ ⊣⊢ ⌈P⌉ ∨ ⌈Q⌉.
  Proof. rewrite !bi.or_alt weak_embed_exist. by f_equiv=>-[]. Qed.
  Lemma weak_embed_wand_1 P Q : ⌈P -∗ Q⌉ ⊢ (⌈P⌉ -∗ ⌈Q⌉).
  Proof. apply bi.wand_intro_l. by rewrite -weak_embed_sep bi.wand_elim_r. Qed.
  Lemma weak_embed_pure φ : ⌈⌜φ⌝⌉ ⊣⊢ ⌜φ⌝.
  Proof.
    rewrite (@bi.pure_alt PROP1) (@bi.pure_alt PROP2) weak_embed_exist.
    do 2 f_equiv. apply bi.equiv_entails. split; [apply bi.True_intro|].
    apply weak_embed_True.
  Qed.
  Lemma weak_embed_affinely `{!BiAffine PROP1} `{!BiAffine PROP2}
    P : ⌈<affine> P⌉ ⊣⊢ <affine> ⌈P⌉.
  Proof. by rewrite !bi.affine_affinely. Qed.
  Lemma weak_embed_absorbingly P : ⌈<absorb> P⌉ ⊣⊢ <absorb> ⌈P⌉.
  Proof. by rewrite weak_embed_sep weak_embed_pure. Qed.
  Lemma weak_embed_intuitionistically_1 `{!BiAffine PROP1} `{!BiAffine PROP2} P :
    ⌈□ P⌉ ⊢ □ ⌈P⌉.
  Proof. by rewrite /bi_intuitionistically weak_embed_affinely weak_embed_persistently_1. Qed.

  Lemma weak_embed_affinely_if `{!BiAffine PROP1} `{!BiAffine PROP2}
    P b : ⌈<affine>?b P⌉ ⊣⊢ <affine>?b ⌈P⌉.
  Proof. destruct b; simpl; auto using weak_embed_affinely. Qed.
  Lemma weak_embed_absorbingly_if P b : ⌈<absorb>?b P⌉ ⊣⊢ <absorb>?b ⌈P⌉.
  Proof. destruct b; simpl; auto using weak_embed_absorbingly. Qed.
  Lemma weak_embed_intuitionistically_if_1 `{!BiAffine PROP1} `{!BiAffine PROP2} P b:
    ⌈□?b P⌉ ⊢ □?b ⌈P⌉.
  Proof. destruct b; simpl; auto using weak_embed_intuitionistically_1. Qed.

  Global Instance weak_embed_persistent P : Persistent P → Persistent ⌈P⌉.
  Proof. intros ?. by rewrite /Persistent -weak_embed_persistently_1 -persistent. Qed.

  Global Instance weak_embed_and_homomorphism :
    MonoidHomomorphism bi_and bi_and (≡) (weak_embed W).
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite weak_embed_and|rewrite weak_embed_pure].
  Qed.

  Global Instance weak_embed_or_homomorphism :
    MonoidHomomorphism bi_or bi_or (≡) (weak_embed W).
  Proof.
    by split; [split|]; try apply _;
      [setoid_rewrite weak_embed_or|rewrite weak_embed_pure].
  Qed.

  Global Instance weak_embed_sep_homomorphism :
    MonoidHomomorphism bi_sep bi_sep (≡) (weak_embed W).
  Proof.
    split; [split|]; simpl; try apply _;
      [by setoid_rewrite weak_embed_sep|by rewrite weak_embed_emp].
  Qed.

  Lemma weak_embed_big_sepL {A} (Φ : nat → A → PROP1) l :
    ⌈[∗ list] k↦x ∈ l, Φ k x⌉ ⊣⊢ [∗ list] k↦x ∈ l, ⌈Φ k x⌉.
  Proof. apply (big_opL_commute _). Qed.
  Lemma weak_embed_big_sepM `{Countable K} {A} (Φ : K → A → PROP1) (m : gmap K A) :
    ⌈[∗ map] k↦x ∈ m, Φ k x⌉ ⊣⊢ [∗ map] k↦x ∈ m, ⌈Φ k x⌉.
  Proof. apply (big_opM_commute _). Qed.
  Lemma weak_embed_big_sepS `{Countable A} (Φ : A → PROP1) (X : gset A) :
    ⌈[∗ set] y ∈ X, Φ y⌉ ⊣⊢ [∗ set] y ∈ X, ⌈Φ y⌉.
  Proof. apply (big_opS_commute _). Qed.
  Lemma weak_embed_big_sepMS `{Countable A} (Φ : A → PROP1) (X : gmultiset A) :
    ⌈[∗ mset] y ∈ X, Φ y⌉ ⊣⊢ [∗ mset] y ∈ X, ⌈Φ y⌉.
  Proof. apply (big_opMS_commute _). Qed.

End weak_embed.

(** ** Proof mode for WeakEmbed *)
(** *** Make *)
Class MakeWeakEmbed {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2) (P : PROP1) (Q : PROP2) :=
  make_weak_embed : ⌈P @ W⌉ ⊣⊢ Q.
Global Arguments MakeWeakEmbed {_ _} _ _%_I _%_I.
Global Hint Mode MakeWeakEmbed + + + - - : typeclass_instances.
Class KnownMakeWeakEmbed {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2) (P : PROP1) (Q : PROP2) :=
  #[global] known_make_weak_embed :: MakeWeakEmbed W P Q.
Global Arguments KnownMakeWeakEmbed {_ _} _ _%_I _%_I.
Global Hint Mode KnownMakeWeakEmbed + + + ! - : typeclass_instances.

Section make_weak_embed.
  Context {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2).
  Local Notation "⌈ P ⌉" := (weak_embed W P) : bi_scope.
  Implicit Types P Q R : PROP1.

  Global Instance make_weak_embed_pure φ :
    KnownMakeWeakEmbed W ⌜φ⌝ ⌜φ⌝.
  Proof. apply weak_embed_pure. Qed.
  Global Instance make_weak_embed_emp :
    KnownMakeWeakEmbed W emp emp.
  Proof. apply weak_embed_emp. Qed.
  Global Instance make_weak_embed_default P :
    MakeWeakEmbed W P (⌈P @ W⌉) | 100.
  Proof. by rewrite /MakeWeakEmbed. Qed.
End make_weak_embed.

(** *** Class instances *)
Class IntoWeakEmbed {PROP PROP' : bi} (p : bool) (W: BiWeakEmbed PROP PROP') (P : PROP') (Q : PROP) :=
  into_weak_embed : □?p P ⊢ ⌈□?p Q @ W⌉.
Global Arguments IntoWeakEmbed {_ _} _ _ _%_I _%_I.
Global Arguments into_weak_embed {_ _} _ _ _%_I _%_I {_}.
Global Hint Mode IntoWeakEmbed + + + + ! - : typeclass_instances.


Section weak_embed_class_instances.
  Context {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2).
  Local Notation "⌈ P ⌉" := (weak_embed W P) : bi_scope.
  Implicit Types P Q R : PROP1.

Global Instance as_emp_valid_weak_embed (φ : Prop) (P : PROP1) :
  AsEmpValid0 φ P → AsEmpValid φ ⌈P @ W⌉.
Proof.
  rewrite /AsEmpValid0/AsEmpValid => ->. split; [apply weak_embed_emp_valid_2|].
  admit.
Admitted. (* TODO: remove this, once https://gitlab.mpi-sws.org/iris/iris/-/merge_requests/1104 is merged *)

Global Instance into_pure_weak_embed P φ :
  IntoPure P φ → IntoPure ⌈P⌉ φ.
Proof. rewrite /IntoPure=> ->. by rewrite weak_embed_pure. Qed.

Global Instance from_pure_weak_embed a P φ `{!BiAffine PROP1} `{!BiAffine PROP2} :
  FromPure a P φ → FromPure a ⌈P⌉ φ.
Proof. rewrite /FromPure=> <-. by rewrite -weak_embed_pure weak_embed_affinely_if. Qed.

Global Instance into_wand_weak_embed p q R P Q :
  IntoWand false false R P Q → IntoWand p q ⌈R⌉ ⌈P⌉ ⌈Q⌉.
Proof. by rewrite /IntoWand/= !bi.intuitionistically_if_elim -weak_embed_wand_1=> ->. Qed.

Global Instance from_and_weak_embed P Q1 Q2 :
  FromAnd P Q1 Q2 → FromAnd ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. by rewrite /FromAnd -weak_embed_and => <-. Qed.

Global Instance from_sep_weak_embed P Q1 Q2 :
  FromSep P Q1 Q2 → FromSep ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. by rewrite /FromSep -weak_embed_sep => <-. Qed.

Global Instance maybe_combine_sep_as_weak_embed Q1 Q2 P progress :
  MaybeCombineSepAs Q1 Q2 P progress →
  MaybeCombineSepAs ⌈Q1⌉ ⌈Q2⌉ ⌈P⌉ progress.
Proof. by rewrite /MaybeCombineSepAs -weak_embed_sep => <-. Qed.

Global Instance combine_sep_gives_weak_embed Q1 Q2 P :
  CombineSepGives Q1 Q2 P →
  CombineSepGives ⌈Q1⌉ ⌈Q2⌉ ⌈P⌉.
Proof. by rewrite /CombineSepGives -weak_embed_sep -weak_embed_persistently_1 => ->. Qed.

Global Instance into_and_weak_embed P Q1 Q2 :
  IntoAnd false P Q1 Q2 → IntoAnd false ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. by rewrite /IntoAnd /= -weak_embed_and=> ->. Qed.

Global Instance into_sep_weak_embed P Q1 Q2 :
  IntoSep P Q1 Q2 → IntoSep ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. rewrite /IntoSep -weak_embed_sep=> -> //. Qed.

Global Instance from_or_weak_embed P Q1 Q2 :
  FromOr P Q1 Q2 → FromOr ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. by rewrite /FromOr -weak_embed_or => <-. Qed.

Global Instance into_or_weak_embed P Q1 Q2 :
  IntoOr P Q1 Q2 → IntoOr ⌈P⌉ ⌈Q1⌉ ⌈Q2⌉.
Proof. by rewrite /IntoOr -weak_embed_or => <-. Qed.

Global Instance from_exist_weak_embed {A} P (Φ : A → PROP1) :
  FromExist P Φ → FromExist ⌈P⌉ (λ a, ⌈Φ a⌉%I).
Proof. by rewrite /FromExist -weak_embed_exist => <-. Qed.

Global Instance into_exist_weak_embed {A} P (Φ : A → PROP1) name :
  IntoExist P Φ name → IntoExist ⌈P⌉ (λ a, ⌈Φ a⌉%I) name.
Proof. by rewrite /IntoExist -weak_embed_exist => <-. Qed.

Global Instance into_weak_embed_weak_embed_false P : IntoWeakEmbed false W ⌈P⌉ P.
Proof. by rewrite /IntoWeakEmbed. Qed.

Global Instance into_weak_embed_weak_embed_true P `{!BiAffine PROP1} :
  Persistent P → IntoWeakEmbed true W ⌈P⌉ P.
Proof.
  rewrite /IntoWeakEmbed/=. iIntros (?) "#H".
  iApply (weak_embed_mono with "H"). by iIntros "#?".
Qed.


(* TODO: can we generalize the false to p? *)
Global Instance frame_weak_embed P Q (Q' : PROP2) R :
  Frame false R P Q → MakeWeakEmbed W Q Q' →
  Frame false ⌈R⌉ ⌈P⌉ Q' | 2. (* Same cost as default. *)
Proof.
  rewrite /Frame /MakeWeakEmbed => <- <-.
  by rewrite weak_embed_sep.
Qed.
Global Instance frame_pure_weak_embed P Q (Q' : PROP2) φ :
  Frame false ⌜φ⌝ P Q → MakeWeakEmbed W Q Q' →
  Frame false ⌜φ⌝ ⌈P⌉ Q' | 2. (* Same cost as default. *)
Proof. rewrite /Frame /MakeWeakEmbed -(weak_embed_pure W). apply (frame_weak_embed P Q). Qed.

Lemma modality_weak_embed_mixin :
  modality_mixin (weak_embed W) (MIEnvTransform (IntoWeakEmbed true W)) (MIEnvTransform (IntoWeakEmbed false W)).
Proof.
  split; simpl; split_and?;
      eauto using bi.equiv_entails_1_2, weak_embed_emp, weak_embed_sep, weak_embed_and.
  - by intros P Q ->.
Qed.
Definition modality_weak_embed :=
  Modality _ modality_weak_embed_mixin.

Global Instance from_modal_weak_embed P :
  FromModal True modality_weak_embed ⌈P⌉ ⌈P⌉ P.
Proof. by rewrite /FromModal. Qed.

End weak_embed_class_instances.

(** *** BUpd class instances_ *)
Section weak_embed_bupd_class_instances.
  Context {PROP1 PROP2 : bi} (W : BiWeakEmbed PROP1 PROP2).
  Context `{!BiBUpd PROP1} `{!BiBUpd PROP2} `{!BiWeakEmbedBUpd W}.
  Local Notation "⌈ P ⌉" := (weak_embed W P) : bi_scope.
  Implicit Types P Q R : PROP2.

Global Instance weak_embed_bupd_ne : NonExpansive (weak_embed_bupd W).
Proof. solve_proper. Qed.

Global Instance weak_embed_bupd_proper :
  Proper ((≡) ==> (≡)) (weak_embed_bupd W) := ne_proper _.

Global Instance weak_embed_bupd_mono' : Proper ((⊢) ==> (⊢)) (weak_embed_bupd W).
Proof. solve_proper. Qed.

Global Instance weak_embed_bupd_mono_flip : Proper (flip (⊢) ==> flip (⊢)) (weak_embed_bupd W).
Proof. solve_proper. Qed.

Global Instance from_pure_weak_embed_bupd a P φ :
  FromPure a P φ → FromPure a (|==>⌈W⌉ P) φ.
Proof. rewrite /FromPure=> <-. rewrite /weak_embed_bupd. by iIntros "$ $". Qed.

Global Instance from_modal_weak_embed_bupd P :
  FromModal True modality_id (|==>⌈W⌉ P) (|==>⌈W⌉ P) P.
Proof. rewrite /FromModal /=/weak_embed_bupd. by iIntros (_) "$ $". Qed.

Global Instance elim_modal_weak_embed_bupd p P Q :
  ElimModal True p false (|==>⌈W⌉ P) P (|==>⌈W⌉ Q) (|==>⌈W⌉ Q).
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim/=/weak_embed_bupd.
  iIntros (_) "[H1 H2] Htok". iMod ("H1" with "[$]") as "[??]".
  iApply ("H2" with "[$] [$]").
Qed.

Global Instance elim_modal_weak_embed_bupd_bupd p (P : PROP1) Q :
  ElimModal True p false (⌈|==> P⌉) ⌈P⌉ (|==>⌈W⌉ Q) (|==>⌈W⌉ Q).
Proof using BiWeakEmbedBUpd0.
  rewrite /ElimModal bi.intuitionistically_if_elim/=.
  iIntros (_) "[H1 H2]". iMod (@weak_embed_bupd_bupd with "[$]") as "?".
  iApply ("H2" with "[$]").
Qed.

Global Instance frame_weak_embed_bupd p R P Q :
  Frame p R P Q → Frame p R (|==>⌈W⌉ P) (|==>⌈W⌉ Q) | 2.
Proof. rewrite /Frame/weak_embed_bupd =><-. by iIntros "[$ ?]". Qed.
End weak_embed_bupd_class_instances.


(** ** Instances *)
(** *** weak_embed_id *)
Definition weak_embed_id_embed {A : bi} : WeakEmbed A A := {|
  weak_embed x := x;
  weak_embed_tok := emp%I;
|}.

Lemma weak_embed_id_mixin (PROP : bi) :
  BiWeakEmbedMixin PROP PROP weak_embed_id_embed.
Proof.
  split => //.
  - solve_proper.
  - solve_proper.
Qed.

Definition weak_embed_id {PROP : bi} : BiWeakEmbed PROP PROP :=
  {| bi_weak_embed_mixin := weak_embed_id_mixin PROP |}.

Global Instance weak_embed_id_bupd {PROP : bi} `{!BiBUpd PROP} : BiWeakEmbedBUpd (@weak_embed_id PROP).
Proof. rewrite/BiWeakEmbedBUpd/weak_embed_bupd. iIntros (?) "? $". by rewrite /weak_embed/=. Qed.

(** *** weak_embed_embed *)
Section weak_embed_embed.
  Context {PROP1 PROP2 PROP3 : bi} (W1 : BiWeakEmbed PROP1 PROP2) (W2 : BiWeakEmbed PROP2 PROP3).

  Definition weak_embed_embed_embed :
    WeakEmbed PROP1 PROP3 := {| weak_embed P := ⌈⌈P @ W1⌉ @ W2⌉%I; weak_embed_tok := (⌈⌈{W1}⌉ @ W2⌉ ∗ ⌈{W2}⌉)%I |}.

  Lemma weak_embed_embed_mixin :
    BiWeakEmbedMixin PROP1 PROP3 (weak_embed_embed_embed).
  Proof.
    split; unfold weak_embed; simpl.
    - solve_proper.
    - solve_proper.
    - by rewrite !weak_embed_emp.
    - by rewrite -!weak_embed_True.
    - intros ? ?. by rewrite -!weak_embed_and_2.
    - intros A Φ. by rewrite -!weak_embed_exist.
    - intros P Q. by rewrite -!weak_embed_sep.
    - intros P. by rewrite -!weak_embed_persistently_1.
  Qed.

  Definition weak_embed_embed : BiWeakEmbed PROP1 PROP3 :=
    {| bi_weak_embed_mixin := weak_embed_embed_mixin |}.

  Lemma weak_embed_embed_bupd `{!BiBUpd PROP1} `{!BiBUpd PROP2} `{!BiBUpd PROP3} :
    BiWeakEmbedBUpd W1 →
    BiWeakEmbedBUpd W2 →
    BiWeakEmbedBUpd (weak_embed_embed).
  Proof.
    move => ???. rewrite /weak_embed/weak_embed_tok/=.
    (* This should be provable *)
  Abort.
End weak_embed_embed.
