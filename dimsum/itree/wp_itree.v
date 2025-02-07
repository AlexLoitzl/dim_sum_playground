From iris.bi Require Import fixpoint_mono.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From iris.base_logic.lib Require Export ghost_var.
From dimsum.core.itree Require Export upstream events small_itree.
From dimsum.core.iris Require Export ord_later.
From dimsum.core Require Import universes.

Set Default Proof Using "Type".

(** * [iHandler] *)
Record iHandler Σ (E : Type → Type) := IHandler {
  ihandle : ∀ T, option (E T) → (T → iProp Σ) → iProp Σ;
}.
Arguments IHandler {_ _} _.

Coercion ihandle : iHandler >-> Funclass.

Definition subH {Σ E} (J1 J2 : iHandler Σ E) : iProp Σ :=
  ∀ T e Φ, J1 T e Φ -∗ J2 T e Φ.

Definition liftE {E1} E2 {H : E1 -< E2} {T} (e : E1 T) : E2 T :=
  (@resum _ _ _ _ H) _ e.

Definition liftH {Σ E1} E2 (J1 : iHandler Σ E1) `{!E1 -< E2} : iHandler Σ E2 :=
  IHandler (λ T e Φ, ∃ e', ⌜e = (liftE (E1:=E1) E2) <$> e'⌝ ∗ J1 T e' Φ)%I.

Class inH {Σ E1 E2} `{!E1 -< E2} (J1 : iHandler Σ E1) (J2 : iHandler Σ E2) :=
  is_inH : ⊢ subH (liftH E2 J1) J2.

Global Instance iHandler_union Σ E : Union (iHandler Σ E) :=
  λ J1 J2, IHandler (λ T e Φ, J1 T e Φ ∨ J2 T e Φ)%I.

Lemma subH_union_l Σ E J1 J2 :
  ⊢ subH (Σ:=Σ) (E:=E) J1 (J1 ∪ J2).
Proof. iIntros (???) "HJ". by iLeft. Qed.

Lemma subH_union_r Σ E J1 J2 :
  ⊢ subH (Σ:=Σ) (E:=E) J2 (J1 ∪ J2).
Proof. iIntros (???) "HJ". by iRight. Qed.

Import EqNotations.
Definition IHandlerT {Σ} {E : Type → Type} {T : Type}
  (J : (option (E T) → (T → iProp Σ) → iProp Σ)) : iHandler Σ E :=
  IHandler (λ T' e Φ, ∃ x : T' = T, J
    (rew [λ T, option (E T)] x in e)
    (rew [λ T, (T → iProp Σ)%type] x in Φ))%I.


(** * Handler instances *)
Class stateHPreG (Σ : gFunctors) (S : Type) := StateHPreG {
  stateH_pre_ghost_varG :> ghost_varG Σ S;
}.

Class stateHGS (Σ : gFunctors) (S : Type) := StateHGS {
  stateH_ghost_varG :> ghost_varG Σ S;
  stateH_name : gname;
}.

Class stateInterp (Σ : gFunctors) (S : Type) := StateInterp {
  state_interp : S → iProp Σ;
}.

Definition stateHΣ S : gFunctors :=
  #[ ghost_varΣ S ].

Global Instance subG_stateHΣ Σ S :
  subG (stateHΣ S) Σ → stateHPreG Σ S.
Proof. solve_inG. Qed.

Definition state_is {Σ S} `{!stateHGS Σ S} (s : S) :=
  ghost_var stateH_name (1/2) s.

Definition get_stateH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s, ⌜e = Some EGetState⌝ ∗ state_is s ∗ (state_is s -∗ Φ s))%I.
Definition set_stateH {Σ} (S : Type) `{!stateHGS Σ S} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s s', ⌜e = Some (ESetState s')⌝ ∗ state_is s ∗ (state_is s' -∗ Φ tt))%I.
Definition yieldH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HsNoLc Σ} : iHandler Σ (stateE S) :=
  IHandlerT (λ e Φ,
      ∃ s, ⌜e = Some EYield⌝ ∗ state_is s ∗ |={∅, ⊤}=> (state_interp s ∗
                  (∀ s', state_is s' -∗ state_interp s' ={⊤,∅}=∗ Φ tt)))%I.

Definition stateH {Σ} (S : Type) `{!stateHGS Σ S} `{!stateInterp Σ S} `{!invGS_gen HsNoLc Σ} : iHandler Σ (stateE S) :=
  get_stateH S ∪ set_stateH S ∪ yieldH S.


Definition angelicH {Σ} : iHandler Σ choiceE :=
  IHandler (λ T e Φ, ∃ x, ⌜e = Some (EAngelic T)⌝ ∗ Φ x)%I.
Definition weak_angelicH {Σ} : iHandler Σ choiceE :=
  IHandler (λ T e Φ, ∃ x : T, ⌜e = Some (EAngelic T)⌝ ∗ ∀ y, Φ y)%I.
Definition demonicH {Σ} : iHandler Σ choiceE :=
  IHandler (λ T e Φ, ⌜e = Some (EDemonic T)⌝ ∗ ∀ x, Φ x)%I.

Definition choiceH {Σ} : iHandler Σ choiceE :=
  angelicH ∪ demonicH.

Definition weak_choiceH {Σ} : iHandler Σ choiceE :=
  weak_angelicH ∪ demonicH.


Lemma subH_weak_angelic Σ :
  ⊢ subH (Σ:=Σ) weak_angelicH angelicH.
Proof. iIntros (???) "[%x [% Ha]]". iExists x. iSplit; [done|]. iApply "Ha". Qed.

(** * [wp_itree] *)
Section wp_itree.
  Context {Σ : gFunctors} {E : Type → Type} {R : Type} `{!invGS_gen HsNoLc Σ} `{ord_laterGS Σ}.

  Definition wp_itree_pre (J : iHandler Σ E)
    (wp_itree : leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ) :
      leibnizO (itree E R) -d> (leibnizO (R) -d> iPropO Σ) -d> iPropO Σ := λ t Φ,
  (ord_later_ctx -∗ |={∅}=>
     (∃ r, ⌜t ≳ Ret r⌝ ∗ Φ r) ∨

     (∃ t', ⌜t ≳ Tau t'⌝ ∗ ▷ₒ wp_itree t' Φ) ∨

     (∃ T (e : E T) k, ⌜t ≳ Vis e k⌝ ∗ ▷ₒ |={∅}=> bi_mono1 (J T (Some e)) (λ x, wp_itree (k x) Φ)) ∨

     (bi_mono1 (J unit None) (λ x, wp_itree t Φ)))%I.

  Global Instance wp_itree_pre_ne n J:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) (wp_itree_pre J).
  Proof.
    move => ?? Hwp ?? -> ?? HΦ. rewrite /wp_itree_pre/bi_mono1.
    repeat (f_equiv || eapply Hwp || eapply HΦ || reflexivity).
  Qed.

  Lemma wp_itree_pre_mono J wp1 wp2:
    ⊢ □ (∀ t Φ, wp1 t Φ -∗ wp2 t Φ)
    → ∀ t Φ, wp_itree_pre J wp1 t Φ -∗ wp_itree_pre J wp2 t Φ.
  Proof.
    iIntros "#Hinner" (t Φ) "Hwp ?".
    iMod ("Hwp" with "[$]") as "[?|[[%t' [% ?]]|[(%T&%e&%k&%&Hwp)|Hwp]]]"; iModIntro.
    - iLeft. by iFrame.
    - iRight. iLeft. iExists _. iSplit; [done|]. iModIntro. by iApply "Hinner".
    - iRight. iRight. iLeft. iExists _, _, _. iSplit; [done|].
      iModIntro. iMod "Hwp". iModIntro.
      iApply (bi_mono1_mono with "Hwp"). iIntros (?) "?". by iApply "Hinner".
    - iRight. iRight. iRight. iApply (bi_mono1_mono with "Hwp"). iIntros (?) "?". by iApply "Hinner".
  Qed.

  Local Instance wp_itree_pre_monotone J :
    BiMonoPred (λ wp_itree : (prodO (leibnizO (itree E R)) (leibnizO R -d> iPropO Σ)) -d> iPropO Σ, uncurry (wp_itree_pre J (curry wp_itree))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply wp_itree_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => wp_itree Hwp n [??] [??] /= [/=??].
      apply wp_itree_pre_ne; eauto. move => ?????? /=. by apply: Hwp.
  Qed.

  Definition wp_itree (J : iHandler Σ E) : itree E R → (R → iProp Σ) → iProp Σ :=
    curry (bi_least_fixpoint (λ wp_pre : (prodO (leibnizO (itree E R)) (leibnizO R -d> iPropO Σ)) -d> iPropO Σ, uncurry (wp_itree_pre J (curry wp_pre)))).

  Global Instance wp_itree_ne J n:
    Proper ((=) ==> ((=) ==> dist n) ==> dist n) (wp_itree J).
  Proof. move => ?? -> ?? HΦ. unfold wp_itree. f_equiv. intros ?. by apply HΦ. Qed.
End wp_itree.

Notation "'WPi' t @ J {{ Φ } }" := (wp_itree J t%itree Φ)
  (at level 20, t, Φ at level 200, only parsing) : bi_scope.
Notation "'WPi' t @ J {{ v , Q } }" := (wp_itree J t%itree (λ v, Q))
  (at level 20, t, Q at level 200,
   format "'[hv' 'WPi'  t  '/' @  '[' J ']'  '/' {{  '[' v ,  '/' Q  ']' } } ']'") : bi_scope.

Section wp_itree.
  Context {Σ : gFunctors} {E : Type → Type} {J : iHandler Σ E}.
  Context `{!invGS_gen HsNoLc Σ} `{ord_laterGS Σ}.

  Local Existing Instance wp_itree_pre_monotone.
  Lemma wp_itree_unfold {R} (t : itree E R) Φ:
    WPi t @ J {{ Φ }} ⊣⊢ wp_itree_pre J (wp_itree J) t Φ.
  Proof. rewrite /wp_itree /curry. apply: least_fixpoint_unfold. Qed.

  Lemma wp_itree_strong_ind {R} (G: leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 G →
    ⊢ (□ ∀ t Φ, wp_itree_pre J (λ t' Ψ, G t' Ψ ∧ WPi t' @ J {{ Ψ }}) t Φ -∗ G t Φ)
      -∗ ∀ t Φ, WPi t @ J {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (t Φ) "Hwp".
    rewrite {2}/wp_itree {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry G) with "[] Hwp").
    iIntros "!>" ([??]) "Hwp" => /=. by iApply "HPre".
  Qed.

  Lemma wp_itree_ind {R} (G: leibnizO (itree E R) -d> (leibnizO R -d> iPropO Σ) -d> iPropO Σ):
    NonExpansive2 G →
    ⊢ (□ ∀ t Φ, wp_itree_pre J G t Φ -∗ G t Φ)
      -∗ ∀ t Φ, WPi t @ J {{ Φ }} -∗ G t Φ.
  Proof.
    iIntros (Hne) "#HPre". iApply wp_itree_strong_ind. iIntros "!>" (t Φ) "Hwp".
    iApply "HPre". iApply (wp_itree_pre_mono with "[] Hwp").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Global Instance wp_itree_proper R b :
    Proper (flip (eqit (=) b false) ==> (=) ==> (⊢)) (wp_itree (R:=R) J).
  Proof.
    move => t1 t2 Heqit ?? ->. iIntros "Hwp".
    have {}Heqit: t2 ≳ t1. { apply: eqit_mon; [..|by apply Heqit]; naive_solver. }
    rewrite !wp_itree_unfold. iIntros "?".
    iMod ("Hwp" with "[$]") as "[[%r [% Hwp]]|[[%t' [% Hwp]]|[(%T&%e&%k&%&Hwp)|Hwp]]]";
      iModIntro.
    - iLeft. iExists _. iFrame. by rewrite Heqit.
    - iRight. iLeft. iExists _. iFrame. by rewrite Heqit.
    - iRight. iRight. iLeft. iExists _, _, _. iFrame. by rewrite Heqit.
    - iRight. iRight. iRight.
  Admitted.

  Global Instance wp_itree_proper_flip R b :
    Proper ((eqit (=) b false) ==> (=) ==> flip (⊢)) (wp_itree (R:=R) J).
  Proof.
    move => t1 t2 Heqit ?? ->. iIntros "Hwp".
    have {}Heqit: t1 ≳ t2. { apply: eqit_mon; [..|by apply Heqit]; naive_solver. }
    rewrite !wp_itree_unfold. iIntros "?".
    iMod ("Hwp" with "[$]") as "[[%r [% Hwp]]|[[%t' [% Hwp]]|[(%T&%e&%k&%&Hwp)|Hwp]]]";
      iModIntro.
    - iLeft. iExists _. iFrame. by rewrite Heqit.
    - iRight. iLeft. iExists _. iFrame. by rewrite Heqit.
    - iRight. iRight. iLeft. iExists _, _, _. iFrame. by rewrite Heqit.
    - iRight. iRight. iRight.
  Admitted.

  Lemma wp_itree_wand {R} (t : itree E R) Φ Ψ:
    WPi t @ J {{ Φ }} -∗
    (∀ r, Φ r -∗ Ψ r) -∗
    WPi t @ J {{ Ψ }}.
  Proof.
    iIntros "Hwp Hwand".
    pose (G := (λ t Ψ, ∀ Φ, (∀ r : R, Ψ r -∗ Φ r) -∗ WPi t @ J {{ Φ }})%I).
    iAssert (∀ Φ, WPi t @ J {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hwp"). done. }
    iIntros (?) "Hwp".
    iApply (wp_itree_ind with "[] Hwp"). { solve_proper. }
    iIntros "!>" (??) "Hwp". iIntros (?) "Hc".
    rewrite wp_itree_unfold. iIntros "?".
    iMod ("Hwp" with "[$]") as "[[%r [% Hwp]]|[[%t' [% Hwp]]|[(%T&%e&%k&%&Hwp)|Hwp]]]"; iModIntro.
    - iLeft. iExists _. iSplit; [done|]. by iApply "Hc".
    - iRight. iLeft. iExists _. iSplit; [done|]. iModIntro. by iApply "Hwp".
    - iRight. iRight. iLeft. iExists _, _, _. iSplit; [done|].
      iModIntro. iMod "Hwp". iModIntro.
      iApply (bi_mono1_mono with "Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
    - iRight. iRight. iRight. iApply (bi_mono1_mono with "Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
  Qed.

  Lemma wp_itree_bind {R T} (t : itree E T) (k : T → itree E R) Φ :
    WPi t @ J {{ r, WPi (k r) @ J {{ Φ }} }} -∗
    WPi (ITree.bind t k) @ J {{ Φ }}.
  Proof.
    iIntros "Hwp".
    pose (G := (λ t Ψ, ∀ Φ, (∀ r, Ψ r -∗ WPi k r @ J {{ Φ }}) -∗ WPi ITree.bind t k @ J {{ Φ }})%I).
    iAssert (∀ Φ, WPi t @ J {{ Φ }} -∗ G t Φ)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hwp"). iIntros (?) "?". done. }
    iIntros (?) "Hwp".
    iApply (wp_itree_ind with "[] Hwp"). { solve_proper. }
    iIntros "!>" (??) "Hwp". iIntros (?) "Hc".
    rewrite wp_itree_unfold. iIntros "#?".
    iMod ("Hwp" with "[$]") as "[[%r [%Heq Hwp]]|[[%t' [%Heq Hwp]]|[(%X&%e&%j&%Heq&Hwp)|Hwp]]]".
    - iDestruct ("Hc" with "[$]") as "Hc". rewrite wp_itree_unfold.
      iMod ("Hc" with "[$]") as "[[%r' [%Heq' Hwp]]|[[%t' [% Hwp]]|[(%X&%e&%j&%&Hwp)|Hwp]]]"; iModIntro.
      + iLeft. iExists _. iSplit; [iPureIntro|done]. by rewrite Heq bind_ret_l.
      + iRight. iLeft. iExists _. iSplit; [iPureIntro|done]. by rewrite Heq bind_ret_l.
      + iRight. iRight. iLeft. iExists _,_,_. iSplit; [iPureIntro|done].
        by rewrite Heq bind_ret_l.
      + iRight. iRight. iRight.
        iApply (bi_mono1_mono with "Hwp"). iIntros (?) "Hwp".
        by rewrite Heq bind_ret_l.
    - iModIntro. iRight. iLeft. iExists _. iSplit. { iPureIntro. by rewrite Heq bind_tau. }
      iModIntro. by iApply "Hwp".
    - iModIntro. iRight. iRight. iLeft. iExists _, _, _. iSplit.
      { iPureIntro. by rewrite Heq bind_vis. }
      iModIntro. iMod "Hwp". iModIntro.
      iApply (bi_mono1_mono with "Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
    - iModIntro. iRight. iRight. iRight. iApply (bi_mono1_mono with "Hwp"). iIntros (?) "Hwp". by iApply "Hwp".
  Qed.


  Lemma wp_itree_ret {R} Φ (r : R):
    Φ r -∗
    WPi Ret r @ J {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite wp_itree_unfold. iIntros "#? !>".
    iLeft. iExists _. by iFrame.
  Qed.

  Lemma wp_itree_Tau {R} Φ (t : itree E R):
    ▷ₒ WPi t @ J {{ Φ }} -∗
    WPi Tau t @ J {{ Φ }}.
  Proof.
    iIntros "Hwp". iEval (rewrite wp_itree_unfold). iIntros "#? !>".
    iRight. iLeft. iExists _. iSplit; [done|]. by iModIntro.
  Qed.

  Lemma wp_itree_vis {R} Φ T e (k : T → itree E R):
    ▷ₒ J T (Some e) (λ r, WPi k r @ J {{ Φ }}) -∗
    WPi (Vis e k) @ J {{ Φ }}.
  Proof.
    iIntros "Hwp". iEval (rewrite wp_itree_unfold). iIntros "#? !>".
    iRight. iRight. iLeft. iExists _, _, _. iSplit; [done|]. do 2 iModIntro.
    iApply (bi_mono1_intro with "Hwp"). by iIntros (?) "?".
  Qed.

End wp_itree.

Section wp_events.
  Context {Σ : gFunctors} {E : Type → Type} {J : iHandler Σ E}.
  Context `{!invGS_gen HasNoLc Σ} `{ord_laterGS Σ}.

  Lemma wp_demonic {R} Φ T (k : T → itree E R) `{!choiceE -< E} `{!inH demonicH J}:
    (▷ₒ ∀ x, WPi k x @ J {{ Φ }}) -∗
    WPi (ITree.bind (demonic T) k) @ J {{ Φ }}.
  Proof.
  Admitted.
End wp_events.
