From iris.algebra Require Export cmra local_updates proofmode_classes auth.
From iris.algebra Require Import updates.
From iris.base_logic.lib Require Export own.
From iris.algebra.lib Require Import gmap_view.
From iris.proofmode Require Export proofmode.
From dimsum.core Require Export satisfiable.
From dimsum.core Require Import axioms.
From dimsum.core.iris Require Export weak_embed.
From iris.prelude Require Import options.

(** * upstream *)
Section cmra.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.
  Implicit Types q : frac.
  Implicit Types dq : dfrac.

  Lemma view_updateP a b P :
    (∀ n bf, rel n a (b ⋅ bf) → ∃ a' b', P (●V a' ⋅ ◯V b') ∧ rel n a' (b' ⋅ bf)) →
    view_auth (rel:=rel) (DfracOwn 1) a ⋅ ◯V b ~~>: P.
  Proof.
    intros Hup; apply cmra_total_updateP=> n [[[dq ag]|] bf] [/=].
    { by intros []%(exclusiveN_l _ _). }
    intros _ (a0 & <-%(inj to_agree) & Hrel).
    rewrite left_id in Hrel. edestruct Hup as [a' [b'[??]]]; [done|].
    eexists _. split; [done|].
    split; simpl; [done|].
    exists a'; split; [done|]. rewrite !left_id. done.
  Qed.

  Lemma view_frag_proj_included b y:
    ◯V b ≼ y → b ≼ view_frag_proj y.
  Proof. move => [? ->]/=. apply cmra_included_l. Qed.

  Lemma view_frag_proj_frag_included x:
    ◯V (view_frag_proj x) ≼ x.
  Proof.
    destruct x as [a f].
    eexists (View a ε).  simpl.
    rewrite /op/=/cmra_op/=/view_op_instance/=.
    by f_equiv; rewrite ?left_id ?right_id.
  Qed.

End cmra.

  Lemma cmra_opM_op_assoc {A : cmra} (x1 : A) x2 x3 :
    x1 ⋅? (x2 ⋅ x3) ≡ x1 ⋅? x2 ⋅? x3.
  Proof. destruct x2, x3 => //=. by rewrite -assoc. Qed.

(** * CoreCancelable *)
Class CoreCancelable {A : cmra} (x : A) :=
  core_cancelableN n y z : ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ⋅? pcore x ≡{n}≡ z ⋅? pcore x
.
Global Arguments core_cancelableN {_} _ {_} _ _ _ _.
Global Hint Mode CoreCancelable + ! : typeclass_instances.
Global Instance: Params (@CoreCancelable) 1 := {}.

Section cmra.
Context {A : cmra}.
Implicit Types x y z : A.

Global Instance CoreCancelable_proper : Proper ((≡) ==> iff) (@CoreCancelable A).
Proof. intros x y Hxy. rewrite /CoreCancelable. by setoid_rewrite Hxy. Qed.

Lemma core_cancelable x `{!CoreCancelable x} y z : ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ⋅? pcore x ≡ z ⋅? pcore x.
Proof. rewrite !equiv_dist cmra_valid_validN. intros. by apply (core_cancelableN x). Qed.
Lemma discrete_core_cancelable x `{CmraDiscrete A}:
  (∀ y z, ✓(x ⋅ y) → x ⋅ y ≡ x ⋅ z → y ⋅? pcore x ≡ z ⋅? pcore x) → CoreCancelable x.
Proof. intros ????. rewrite -!discrete_iff -cmra_discrete_valid_iff. auto. Qed.

Lemma core_cancelableN_total x `{!CoreCancelable x} `{!CmraTotal A} n y z :
  ✓{n}(x ⋅ y) → x ⋅ y ≡{n}≡ x ⋅ z → y ⋅ core x ≡{n}≡ z ⋅ core x.
Proof. move => ??. ogeneralize* (core_cancelableN x); [done..|]. by rewrite cmra_pcore_core. Qed.

Global Instance cancelable_core_cancelable x `{!Cancelable x} : CoreCancelable x.
Proof.
  rewrite /CoreCancelable => n y z Hvalid Hz. ogeneralize* @cancelableN; [done..|]. move => ->. done.
Qed.

Global Instance coreid_core_cancelable x `{!CoreId x} : CoreCancelable x.
Proof. rewrite /CoreCancelable => n y z Hvalid Heq. by rewrite core_id /= comm Heq comm. Qed.

Lemma core_cancelable_op x1 x2 :
  CoreCancelable x1 →
  CoreCancelable x2 →
  (* TODO: Does this hold in general? *)
  pcore (x1 ⋅ x2) ≡ pcore x1 ⋅ pcore x2 →
  CoreCancelable (x1 ⋅ x2).
Proof.
  move => Hx1 Hx2 Hcore. rewrite /CoreCancelable => n y z Hvalid Hz.
  rewrite Hcore !cmra_opM_op_assoc.
  apply Hx2. {
    apply: cmra_validN_includedN; [done|].
    rewrite (comm _ x1) -!assoc. apply: cmra_monoN_l.
    rewrite comm. destruct (pcore x1) eqn:? => /=.
    + apply: cmra_monoN_l. apply cmra_included_includedN. by apply cmra_included_pcore.
    + apply cmra_includedN_l.
  }
  opose proof* (Hx1 n (x2 ⋅ y) (x2 ⋅ z)).
  - by rewrite assoc.
  - by rewrite !assoc.
  - by rewrite -!cmra_op_opM_assoc.
Qed.
End cmra.

Section instances.
Global Instance dfrac_core_cancelable (dq : dfracR) : CoreCancelable dq.
Proof.
  destruct dq as [q| |q]; [apply _..|].
  have -> : DfracBoth q = DfracOwn q ⋅ DfracDiscarded by done.
  by apply: core_cancelable_op.
Qed.

Lemma prod_core_cancelable {A B : cmra} (x1 : A) (x2 : B) :
  CoreCancelable x1 →
  CoreCancelable x2 →
  is_Some (pcore x1) →
  is_Some (pcore x2) →
  CoreCancelable (x1, x2).
Proof.
  move => Hx1 Hx2 [? Hp1] [? Hp2].
  move => n [y1 y2] [z1 z2] /=. rewrite -!pair_op => /pair_validN[/=??] [/= ??].
  ospecialize* Hx1; [done..|].
  ospecialize* Hx2; [done..|].
  rewrite pair_pcore /= Hp1 Hp2 /=.
  rewrite Hp1/= in Hx1. rewrite Hp2/= in Hx2.
  done.
Qed.

Global Instance prod_total_core_cancelable {A B : cmra} (x : A * B) `{!CmraTotal A} `{!CmraTotal B} :
  CoreCancelable x.1 →
  CoreCancelable x.2 →
  CoreCancelable x.
Proof. move => ??. apply: prod_core_cancelable; by rewrite cmra_pcore_core. Qed.

Global Instance core_cancelable_Some {A : cmra} (a : A) :
  IdFree a → CoreCancelable a → CoreCancelable (Some a).
Proof.
  intros Hirr ? n [b|] [c|] ? EQ; inversion_clear EQ => /=.
  - rewrite ?Some_op_opM. constructor. by apply (core_cancelableN a).
  - destruct (Hirr b); [|eauto using dist_le with lia].
    by eapply (cmra_validN_op_l 0 a b), (cmra_validN_le n); last lia.
  - destruct (Hirr c); [|symmetry; eauto using dist_le with lia].
    by eapply (cmra_validN_le n); last lia.
  - done.
Qed.

Global Instance option_core_cancelable {A : cmra} (x : optionR A) :
  (∀ a : A, IdFree a) →
  (∀ a : A, CoreCancelable a) →
  CoreCancelable x.
Proof. destruct x; apply _. Qed.

Global Instance gmap_core_cancelable `{Countable K} {A : cmra} (m : gmap K A) :
  (∀ x : option A, CoreCancelable x) → CoreCancelable m.
Proof.
  intros ? n m1 m2 ?? i.
  rewrite !lookup_opM !cmra_pcore_core /= lookup_core.
  apply (core_cancelableN (m !! i)); by rewrite -!lookup_op.
Qed.


Global Instance prod_dfrac_agree_core_cancelable {A : ofe} (x : prodR dfracR (agreeR A)) :
  CoreCancelable x.
Proof. destruct x as [[q| |q]?]. 1: apply _. all: apply prod_core_cancelable => //; by apply _. Qed.

Global Instance option_prod_dfrac_agree_core_cancelable {A : ofe} (x : optionR (prodR dfracR (agreeR A))) :
  CoreCancelable x.
Proof.
  destruct x as [[[q| |q] a]|]; try apply _.
  have -> : (Some (DfracBoth q, a)) ≡ (Some (DfracOwn q, a)) ⋅ (Some (DfracDiscarded, a)).
  { by rewrite -Some_op -pair_op agree_idemp. }
  apply: core_cancelable_op.
  rewrite /pcore/cmra_pcore/=/option_pcore_instance/=.
  rewrite /pcore/cmra_pcore/=/prod_pcore_instance/=.
  by rewrite agree_idemp.
Qed.

Global Instance view_core_cancelable {A B} (rel : view_rel A B) (x : viewR rel) :
  CoreCancelable (view_frag_proj x) →
  CoreCancelable x.
Proof.
  move => Hfrag n y z Hvalid [Heqa Heqf].
  have ? : ✓{n} view_auth_proj (x ⋅ y). {
    destruct x as [[[??]|]?], y as [[[??]|]?] => //; simplify_eq/=.
    all: move: Hvalid => [? [? [Heq ?]]]; split; try done; simpl in *; by rewrite Heq.
  }
  have ? : ✓{n} view_frag_proj (x ⋅ y). {
    destruct x as [[[??]|]?], y as [[[??]|]?] => //; simplify_eq/=.
    1,2,3: move: Hvalid => [? [? [_ /view_rel_validN ?]]]; done.
    1: move: Hvalid => [? /view_rel_validN ?]; done.
  }
  split.
  - eapply (core_cancelableN (A:=optionUR (prodR (dfracR) (agreeR _)))); try apply _; done.
  - eapply core_cancelableN_total; try apply _; done.
Qed.

Global Instance gmap_view_core_cancelable {A} `{Countable K} (x : gmap_viewR K (agreeR A)) :
  CoreCancelable x.
Proof. apply _. Abort.

End instances.

(** * sat *)
Class satG Σ (M : ucmra) := SatG {
  sat_inG : inG Σ (authR M);
}.
Local Existing Instance sat_inG.

Definition satΣ M : gFunctors :=
  #[ GFunctor (authR M) ].

Global Instance subG_satΣ Σ M :
  subG (satΣ M) Σ → satG Σ M.
Proof. solve_inG. Qed.

(* TODO: make a nice abstraction for this disjunction? Some proofs about it are repeated below. *)
Definition sat_embed {Σ M} `{!satG Σ M} (γ : gname) :
  WeakEmbed (uPred M) (iProp Σ) := {|
    weak_embed P :=
      (∃ m, ⌜uPred_holds P 0 m⌝ ∗ (⌜m ≼ ε⌝ ∨ own γ (auth_frag m)))%I;
    weak_embed_tok := (∃ m, own γ (auth_auth (DfracOwn 1) m))%I;
|}.

Section sat.
  Context {Σ : gFunctors} {M : ucmra}.
  Context {G : satG Σ M} {Hdiscrete : CmraDiscrete M} (γ : gname).
  Local Notation "⌈ P ⌉" := (weak_embed (sat_embed γ) P) : bi_scope.
  Implicit Types (P : uPred M).

  Global Instance sat_ne n :
    Proper ((dist n) ==> (dist n)) (weak_embed (sat_embed γ)).
  Proof.
    move => P1 P2 [Heq].
    rewrite /weak_embed/=. f_equiv => x.
    destruct (AxClassic (✓{0} x)) as [|Hf].
    - do 2 f_equiv. by apply Heq; [lia|].
    - apply equiv_dist. iSplit; iIntros "[_ [%|Hm]]".
      1,3: contradict Hf; apply: cmra_validN_included; [apply ucmra_unit_validN|done].
      all: iDestruct (own_valid with "Hm") as "#Hvalid"; rewrite auth_frag_validI;
        by iDestruct (uPred.cmra_valid_elim with "Hvalid") as %?.
  Qed.

  Lemma sat_mono P1 P2 :
    (P1 ⊢ P2) →
    ⌈P1⌉ ⊢ ⌈P2⌉.
  Proof.
    rewrite /weak_embed/=.
    iIntros ([Hwand]) "[%m [%Hholds [%Hε | Hm]]]". {
      iExists ε. iSplit; [iPureIntro|by iLeft].
      apply Hwand. { by apply cmra_valid_validN, ucmra_unit_valid. }
      apply: uPred_mono; [done| |done]. by apply cmra_included_includedN.
    }
    iDestruct (own_valid with "Hm") as "#Hvalid". rewrite auth_frag_validI.
    iExists _. iFrame.
    (* TODO: Is this use of excluded middle necessary? *)
    destruct (AxClassic (✓{0} m)); [iPureIntro; naive_solver|].
    by iDestruct (uPred.cmra_valid_elim with "Hvalid") as %?.
  Qed.

(*
  Lemma sat_emp_valid_inj P :
    (⊢ ⌈P⌉) → ⊢ P.
  Proof.
    rewrite /weak_embed/=.
    (* move => ?. *)
    (* Set Printing All. *)
    setoid_rewrite <-bi.persistent_and_sep. 2: apply _.
    rewrite /bi_emp_valid/bi_entails.
    uPred.unseal.
    move => [Hx]. ogeneralize* (Hx 0 ε). 1: admit. 1: done.
    rewrite {1}/uPred_holds/= {1}/uPred_holds/= {1}/uPred_holds/=.
    move => [m [? Hor]].
    have ? : m ≼ ε.
    - destruct Hor as [?|Hown] => //.
      move: Hown. rewrite own.own_eq/own.own_def.
      uPred.unseal.
      rewrite /uPred_holds/=/own.iRes_singleton.
      admit.
    - constructor. move => ????. apply: uPred_mono; [done| |].
      1: admit. admit. (* This is a problem, how do we know that P is independent of the step index? *)
  Abort.
*)

  Lemma sat_emp :
    ⊢ ⌈emp⌉.
  Proof. iExists ε. iSplit; [|by iLeft]. iPureIntro. by uPred.unseal. Qed.

  Lemma sat_and_2 P1 P2 :
     ⌈P1⌉ ∧ ⌈P2⌉ ⊢ ⌈P1 ∧ P2⌉.
  Proof using Hdiscrete.
    rewrite /weak_embed/=. rewrite bi.and_exist_l. apply bi.exist_elim => m1.
    rewrite bi.and_exist_r. apply bi.exist_elim => m2.
    rewrite -!bi.persistent_and_sep -!bi.and_assoc. apply bi.pure_elim_l => ?.
    rewrite bi.and_comm -!bi.and_assoc. apply bi.pure_elim_l => ?.
    rewrite bi.and_or_r !bi.and_or_l.
    repeat apply bi.or_elim.
    - iIntros "[% %]". iExists ε. iSplit; [|by iLeft]. iPureIntro.
      uPred.unseal. split; (apply: uPred_mono; [done|by apply cmra_included_includedN |done]).
    - iIntros "[% ?]". iExists m2. iSplit; [|by iRight]. iPureIntro.
      uPred.unseal. split => //. apply: uPred_mono; [done| |done].
      apply cmra_included_includedN. etrans; [done|]. apply ucmra_unit_least.
    - iIntros "[? %]". iExists m1. iSplit; [|by iRight]. iPureIntro.
      uPred.unseal. split => //. apply: uPred_mono; [done| |done].
      apply cmra_included_includedN. etrans; [done|]. apply ucmra_unit_least.
    - rewrite own_and_total. iIntros "[%m [? [%Hi1 %Hi2]]]".
      move: Hi1 =>/view_frag_proj_included Hi1. move: Hi2 =>/view_frag_proj_included Hi2.
      iExists (view_frag_proj m). iSplit.
      + iPureIntro. uPred.unseal. split; (apply: uPred_mono; [done|by apply cmra_included_includedN|done]).
      + iRight. iApply (own_mono with "[$]"). apply view_frag_proj_frag_included.
  Qed.

  Lemma sat_exist_2 A (P : A → _) :
     ⌈∃ x : A, P x⌉ ⊢ ∃ x, ⌈P x⌉.
  Proof.
    rewrite /weak_embed/=.
    iIntros "[%m [%Hholds H]]".
    do [uPred.unseal] in Hholds. destruct Hholds as [??].
    iExists _, _. by iFrame.
  Qed.

  Lemma sat_sep P1 P2 :
    ⌈P1 ∗ P2⌉ ⊣⊢ ⌈P1⌉ ∗ ⌈P2⌉.
  Proof using Hdiscrete.
    rewrite /weak_embed/=.
    iSplit.
    - iIntros "[%m [%Hholds H]]".
      do [uPred.unseal] in Hholds. destruct Hholds as [m1 [m2 [Heq%discrete_iff [??]]]]. 2: apply _.
      rewrite Heq auth_frag_op own_op. iDestruct "H" as "[%Hε | [H1 H2]]".
      + iSplitL; iExists _.
        all: iSplit; [done|]; iLeft; iPureIntro.
        all: etrans; [|done]. 1: apply cmra_included_l. 1: apply cmra_included_r.
      + iSplitL "H1"; iExists _; by iFrame.
    - iIntros "[[%m1 [%Hholds1 H1]] [%m2 [%Hholds2 H2]]]".
      iExists (m1 ⋅ m2). iSplit. { iPureIntro. uPred.unseal. eexists _, _. eauto. }
      iDestruct "H1" as "[%Hincl1 | H1]"; iDestruct "H2" as "[%Hincl2 | H2]".
      + iLeft. iPureIntro. etrans; [by apply: cmra_mono_r|]. by rewrite left_id.
      + iRight. iApply (own_mono _ (ε ⋅ _) with "[H2]"); [|by rewrite left_id].
        rewrite auth_frag_op. by apply cmra_mono_r, auth_frag_mono.
      + iRight. iApply (own_mono _ (_ ⋅ ε) with "[H1]"); [|by rewrite right_id].
        rewrite auth_frag_op. by apply cmra_mono_l, auth_frag_mono.
      + iCombine "H1 H2" as "$".
  Qed.

  Lemma sat_persistently_1 P :
    ⌈<pers> P⌉ ⊢ <pers> ⌈P⌉.
  Proof.
    rewrite /weak_embed/=.
    iIntros "[%m1 [%Hholds1 H1]]".
    iExists (core m1).
    iSplit. { iModIntro. iPureIntro. move: Hholds1. by uPred.unseal. }
    iDestruct "H1" as "[%Hincl |H1]".
    - iModIntro. iLeft. iPureIntro. by etrans; [apply cmra_included_core|].
    - iDestruct (own_mono with "H1") as "H1". { apply cmra_included_core. }
      iDestruct "H1" as "#?".
      iModIntro. by iRight.
  Qed.

  Lemma sat_persistently_2 P :
    <pers> ⌈P⌉ ⊢ ⌈<pers> P⌉.
  Proof.
    rewrite /weak_embed/=.
    iIntros "[%m1 [%Hholds1 H1]]".
    iDestruct "H1" as "#H1".
    (* Likely does not hold?! *)
    iExists (m1). iFrame "H1".
    iPureIntro. move: Hholds1. uPred.unseal.
  Abort.


  Lemma sat_mixin :
    BiWeakEmbedMixin (uPred M) (iProp Σ) (sat_embed γ).
  Proof using Type*.
    split; simpl.
    - solve_proper.
    - move => ??. by apply sat_mono.
    - iSplit; [by iIntros "?"|iIntros "?"; iApply sat_emp].
    - iIntros "?". iApply sat_emp.
    - move => *. by rewrite sat_and_2.
    - move => *. by rewrite sat_exist_2.
    - move => *. by rewrite sat_sep.
    - move => *. apply sat_persistently_1.
  Qed.

  Definition sat : BiWeakEmbed (uPred M) (iProp Σ) :=
    {| bi_weak_embed_mixin := sat_mixin |}.



  Lemma sat_bupd P :
    ⌈|==> P⌉ ==∗⌈sat⌉ ⌈P⌉.
  Proof using Hdiscrete.
    rewrite -weak_embed_bupd_elim /weak_embed/weak_embed_tok/=.
    iIntros "[%mf [%Hholds Hf]] [%ma Ha]".
    iAssert (|==> own γ (◯ mf))%I with "[Hf]" as ">Hf". {
      iDestruct "Hf" as "[%Hincl|$]"; [|done]. iMod (own_unit _ γ) as "Ho".
      iModIntro. iApply (own_mono with "Ho"). by apply auth_frag_mono. }
    iCombine "Ha Hf" as "H".
    do [uPred.unseal] in Hholds.
    iMod (own_updateP (λ x, ∃ ma' mf', x ≡ ● ma' ⋅ ◯ mf' ∧ uPred_holds P 0 mf')  with "H")
      as (?[?[?[-> ?]]]) "[Ha Hf]".
    2: { iModIntro. iSplitL "Ha"; iExists _; by iFrame. }
    apply view_updateP. move => ? f [/cmra_discrete_included_iff [i Heq] /cmra_discrete_valid_iff Hvalid].
    destruct (Hholds 0 (f ⋅ i)) as [x [?%cmra_discrete_valid_iff ?]].
    { done. } { rewrite assoc -Heq. by apply cmra_valid_validN. }
    eexists (x ⋅ f ⋅ i), x.
    split; [by eexists (x ⋅ f ⋅ i), x|].
    split.
    - apply cmra_includedN_l.
    - apply cmra_valid_validN. by rewrite -assoc.
  Qed.

  Global Instance bi_sat_bupd : BiWeakEmbedBUpd sat.
  Proof. unfold BiWeakEmbedBUpd. apply sat_bupd. Qed.
End sat.

Definition sat_closed {Σ M} `{!satG Σ M} `{!CmraDiscrete M} :
  gname → bool → uPred M → iProp Σ :=
  λ γ b F, (∀ P', ⌜satisfiable (P' ∗ F)⌝ ==∗ ⌈{sat γ}⌉ ∗
    ⌈if b then P' ∗ F else P' @ sat γ⌉)%I.


Section sat.
  Context {Σ : gFunctors} {M : ucmra}.
  Context `{!satG Σ M} {Hdiscrete : CmraDiscrete M}.
  Implicit Types (P : uPred M).

  (** ** rules for interacting with [sat] *)
  Lemma sat_alloc_open P :
    satisfiable P →
    ⊢ |==> ∃ γ, ⌈{sat γ}⌉ ∗ ⌈P @ sat γ⌉.
  Proof using Hdiscrete.
    move => [x [/cmra_discrete_valid_iff Hvalid ?]].
    iMod (own_alloc (● x ⋅ ◯ x)) as (γ) "[Ha Hf]". { by apply auth_both_valid_discrete. }
    iModIntro. iExists _. iSplitL "Ha"; iExists _; by iFrame.
  Qed.

  Lemma sat_alloc_closed F :
    ⊢ |==> ∃ γ, sat_closed γ true F.
  Proof using Hdiscrete.
    iMod (own_alloc (● ε)) as (γ) "Ha". { by apply auth_auth_valid, ucmra_unit_valid. }
    iModIntro. iExists γ. iIntros (P [x [?%cmra_discrete_valid_iff ?]]).
    iMod (own_update with "Ha") as "[Ha Hf]".
    - apply auth_update_alloc. apply (op_local_update_discrete _ _ x).
      move => _. by rewrite right_id.
    - rewrite right_id. iModIntro. iSplitL "Ha"; iExists _; by iFrame.
  Qed.

  Lemma sat_switch γ P Q G :
    (P ⊢ ∃ P', P' ∗ ⌜⌈P' @ sat γ⌉ ∗ Q -∗ G⌝) →
    ⌈P @ sat γ⌉ ∗ Q -∗ G.
  Proof using Hdiscrete.
    iIntros (Himpl) "[Hsat HQ]".
    iDestruct (weak_embed_mono with "Hsat") as "Hsat"; [done|].
    iDestruct "Hsat" as (P') "[Hsat1 %HG]".
    iApply HG. iFrame.
  Qed.

  Lemma sat_switch_sep γ P Q G1 G2 :
    (P ⊢ ∃ P', G1 ∗ P' ∗ ⌜⌈P' @ sat γ⌉ ∗ Q -∗ G2⌝) →
    ⌈P @ sat γ⌉ ∗ Q -∗ ⌈G1 @ sat γ⌉ ∗ G2.
  Proof using Hdiscrete.
    iIntros (Himpl). iApply sat_switch.
    iIntros "HP". iDestruct (Himpl with "HP") as (P') "[? [? %HG]]".
    iExists _. iSplit; [iAccu|iPureIntro].
    iIntros "[[??] ?]". iFrame. iApply HG. iFrame.
  Qed.

  Lemma sat_switch_bupd γ P Q G :
    (P ⊢ |==> ∃ P', P' ∗ ⌜⌈P' @ sat γ⌉ ∗ Q ==∗⌈sat γ⌉ G⌝) →
     ⌈P @ sat γ⌉ ∗ Q ==∗⌈sat γ⌉ G.
  Proof using Hdiscrete.
    iIntros (Himpl) "[Hsat HQ]".
    iDestruct (weak_embed_mono with "Hsat") as "Hsat"; [done|].
    iMod (weak_embed_bupd_bupd with "Hsat") as "Hsat".
    iDestruct "Hsat" as (P') "[Hsat1 %HG]".
    iApply HG. by iFrame.
  Qed.

  Lemma sat_close γ P `{!∀ x : M, CoreCancelable x} :
    ⌈P @ sat γ⌉ -∗
    ⌈{sat γ}⌉ -∗
    ∃ F, ⌜satisfiable (P ∗ F)⌝ ∗ sat_closed γ false F.
  Proof using Hdiscrete.
    rewrite /weak_embed/weak_embed_tok/=.
    iIntros "[%m [%Hholds Hm]] [%a Ha]".
    iAssert (own γ (◯ m) ∗ own γ (● a))%I with "[Ha Hm]" as "[Hm Ha]". {
      iDestruct "Hm" as "[%Hincl|$]"; [|done].
      iDestruct (own_mono _ _ (ε ⋅ _) with "Ha") as "Ha"; [by rewrite left_id|].
      iDestruct "Ha" as "[Hε $]". iApply (own_mono with "Hε"). by apply auth_frag_mono.
    }
    iDestruct (own_valid_2 with "Ha Hm") as %[[f Heq] Hvalid]%auth_both_valid_discrete.
    setoid_subst.
    iExists (uPred_ownM (core m ⋅ f)). iSplit.
    - iPureIntro. eexists (m ⋅ core m ⋅ f).
      rewrite cmra_core_r. split; [by apply cmra_discrete_valid_iff|].
      uPred.unseal. eexists m, (core m ⋅ f). split_and!.
      + by rewrite assoc cmra_core_r.
      + done.
      + eexists ε. by rewrite right_id.
    - iIntros (P' [x [Hxvalid Hx]]).
      do [uPred.unseal] in Hx.
      destruct Hx as [a1 [a2 [Ha%discrete_iff [Ha1 [a2' Ha2']%cmra_discrete_included_r]]]].
      2, 3: apply _.
      iMod (own_update_2 _ _ _ (● x ⋅ ◯ (a1 ⋅ core m ⋅ a2')) with "Ha Hm") as "[Ha Hf]".
      + rewrite Ha Ha2'. apply auth_update.
        apply local_update_unital_discrete.
        move => z Hz Heq2. split.
        * rewrite -Ha2' -Ha. by apply/cmra_discrete_valid_iff.
        * opose proof* @core_cancelable as Heq; [done..|].
          rewrite cmra_pcore_core/= comm in Heq.
          rewrite Heq -!assoc. f_equiv.
          by rewrite (comm _ z) assoc.
      + iModIntro. iSplitL "Ha".
        * iExists _. iFrame.
        * iExists _. iFrame. iPureIntro.
          apply: uPred_mono; [done| |done].
          etrans; [|apply cmra_includedN_l].
          apply cmra_includedN_l.
  Qed.
End sat.
