From dimsum.core Require Export spec_mod.
From dimsum.core.iris Require Export sim expr2.
Set Default Proof Using "Type".

Class specGS := SpecGS {
  spec_state_name : gname;
}.

Definition spec_state {Σ S} `{!specGS} `{!mstateG Σ} (s : S) : iProp Σ :=
  spec_state_name ⤳ s.

Program Definition spec_mod_lang {Σ} `{!mstateG Σ} `{!specGS} (EV S : Type) : mod_lang EV Σ := {|
  mexpr := spec EV S void;
  mectx := unit;
  mfill _ := id;
  mcomp_ectx _ _:= tt;
  mtrans := spec_trans EV S;
  mexpr_rel σ t := σ.1 ≡ t;
  mstate_interp σ := spec_state σ.2;
|}.
Next Obligation. done. Qed.
Canonical Structure spec_mod_lang.

Section spec.
  Context `{!dimsumGS Σ} `{!specGS} {EV S : Type}.

  Global Instance sim_gen_expr_spec_proper ts J :
    Proper ((≡) ==> (=) ==> (⊣⊢)) (sim_gen_expr (Λ:=spec_mod_lang EV S) ts J).
  Proof.
    move => ?? ? ?? ->.
    rewrite !sim_gen_expr_unfold /sim_gen_expr_pre/=. by repeat f_equiv.
  Qed.

  Lemma sim_gen_TVis ts (k : _ → spec EV S void) Π Φ e :
    (∀ s, spec_state s -∗
         ▷ₒ?ts switch_id ts (spec_trans _ S) Π (Some e) (k tt, s) (λ σ',
          spec_state σ'.2 ∗ WP{ts} σ'.1 @ Π {{ Φ }})) -∗
    WP{ts} (Spec.bind (TVis e) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_gen_expr_steps => /=. iIntros ([t s] ? Hs) "?"; simplify_eq/=.
    iApply (sim_gen_step_end with "[-]").
    iApply (ts_step_dem (m:=spec_trans _ _ ) (λ σ, σ.1 ≡ k () ∧ σ.2 = s)).
    { by econs. } { naive_solver. } {
      move => ?? Hstep. inv/= Hstep.
      all: revert select (_ ≡ _); rewrite {1}Hs; move => /spec_equiv_inv//=.
      move => [-> ?]. split!. }
    iIntros (? [??]).
    iMod ("Hsim" with "[$]") as "Hsim". iModIntro.
    (* iApply (switch_id_mono with "Hsim [-]"). *)

  Admitted.
    (* iApply sim_tgt_expr_step. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
    (* inv/= Hstep. *)
    (* all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
    (* move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. *)
    (* iSplit!. iIntros "Htgt". iApply "Hsim". by iApply "Htgt". *)
  (* Qed. *)

  (* Lemma sim_src_TVis k Π Φ e os : *)
  (*   ▷ₒ imodhandle Π (Some e) (SRC k tt @ ? os, Π {{ Φ }}) -∗ *)
  (*   SRC (Spec.bind (TVis e) k) @ ? os, Π {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (* Admitted. *)
  (*   iApply sim_src_expr_step. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
  (*   iExists _, _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] ?) "!> HΦ". simplify_eq. *)
  (*   iApply "Hsim". iIntros (?) "?". by iApply ("HΦ" with "[//] [$]"). *)
  (* Qed. *)

  Lemma sim_gen_TGet ts (k : _ → spec EV S _) Π Φ s :
    (spec_state s ∧ ▷ₒ?ts WP{ts} (k s) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind TGet k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_gen_expr_steps => /=. iIntros (???) "Hs".
    iAssert (⌜σ.2 = s⌝)%I as %<-. {
      iDestruct "Hsim" as "[? _]".
      by iDestruct (mstate_var_merge with "[$] [$]") as (?) "?".
    }
    iDestruct "Hsim" as "[_ Hsim]".
    iApply (sim_gen_step_end with "[-]").
  Admitted.
  (*   iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep ?). simplify_eq/=. iModIntro. *)
  (*   inv/= Hstep. *)
  (*   all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
  (*   move => /spec_equiv_inv //= Heq2. simplify_eq/=. *)
  (*   iSplit!. iModIntro. rewrite Heq2. iSplit!. by iFrame. *)
  (* Qed. *)

  (* Lemma sim_src_TGet k Π Φ s : *)
  (*   SRC (k s) @ s [{ Π }] {{ Φ }} -∗ *)
  (*   SRC (Spec.bind TGet k) @ s [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]? ?). simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] ?) "!>". simplify_eq. iSplit!. by iFrame. *)
  (* Qed. *)

  Lemma sim_gen_TPut ts (k : _ → spec EV S void) Π Φ (s : S) s' :
    spec_state s -∗
    (spec_state s' -∗ ▷ₒ?ts WP{ts} (k tt) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind (TPut s') k) @ Π {{ Φ }}.
  Proof.
    iIntros "? Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
    iApply sim_gen_expr_steps => /=. iIntros (???) "Hs".
    iDestruct (mstate_var_merge with "[$] [$]") as (?) "?".
    iApply (sim_gen_step_end with "[-]").
  Admitted.
  (*   iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep ?). simplify_eq/=. iModIntro. *)
  (*   inv/= Hstep. *)
  (*   all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
  (*   move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. *)
  (*   iSplit!. iModIntro. rewrite Heq2. iSplit!. by iFrame. *)
  (* Qed. *)

  (* Lemma sim_src_TPut k Π Φ s s' : *)
  (*   SRC (k tt) @ s' [{ Π }] {{ Φ }} -∗ *)
  (*   SRC (Spec.bind (TPut s') k) @ s [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]? ?). simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] ?) "!>". simplify_eq. iSplit!. by iFrame. *)
  (* Qed. *)

  Lemma sim_gen_TAll {T} ts (k : _ → spec EV S void) Π Φ :
    (∃/∀{ts} x, ▷ₒ?ts WP{ts} (k x) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind (TAll T) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  Admitted.

  Lemma sim_tgt_TAll {T} x (k : _ → spec EV S void) Π Φ :
    (▷ₒ TGT (k x) @ Π {{ Φ }}) -∗
    TGT (Spec.bind (TAll T) k) @ Π {{ Φ }}.
  Proof. iIntros "Hsim". iApply sim_gen_TAll => /=. by iExists _. Qed.
  Lemma sim_src_TAll {T} (k : _ → spec EV S void) Π Φ :
    (∀ x, SRC (k x) @ Π {{ Φ }}) -∗
    SRC (Spec.bind (TAll T) k) @ Π {{ Φ }}.
  Proof. iIntros "Hsim". by iApply sim_gen_TAll => /=. Qed.

  (* Lemma sim_src_TAll {T} k Π Φ os : *)
  (*   (∀ x, SRC (k x) @ ? os [{ Π }] {{ Φ }}) -∗ *)
  (*   SRC (Spec.bind (TAll T) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. iApply "Hsim". *)
  (* Qed. *)

  Lemma sim_gen_TExist {T} ts (k : _ → spec EV S void) Π Φ :
    (∀/∃{ts} x, ▷ₒ?ts WP{ts} (k x) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind (TExist T) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  Admitted.

  Lemma sim_tgt_TExist {T} (k : _ → spec EV S void) Π Φ :
    (∀ x, ▷ₒ TGT (k x) @ Π {{ Φ }}) -∗
    TGT (Spec.bind (TExist T) k) @ Π {{ Φ }}.
  Proof. iIntros "Hsim". by iApply sim_gen_TExist => /=. Qed.
  Lemma sim_src_TExist {T} x (k : _ → spec EV S void) Π Φ :
    (SRC (k x) @ Π {{ Φ }}) -∗
    SRC (Spec.bind (TExist T) k) @ Π {{ Φ }}.
  Proof. iIntros "Hsim". iApply sim_gen_TExist => /=. by iExists _. Qed.

  (* Lemma sim_tgt_TExist {T} k Π Φ os : *)
  (*   (∀ x, ▷ₒ TGT (k x) @ ? os [{ Π }] {{ Φ }}) -∗ *)
  (*   TGT (Spec.bind (TExist T) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
  (*   inv/= Hstep. *)
  (*   all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
  (*   move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" $! _). *)
  (*   iSplit!. iModIntro. rewrite Heq2. iSplit!. iFrame. *)
  (* Qed. *)

  (* Lemma sim_src_TExist {T} x k Π Φ os : *)
  (*   SRC (k x) @ ? os [{ Π }] {{ Φ }} -∗ *)
  (*   SRC (Spec.bind (TExist T) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame. *)
  (* Qed. *)

  (* TODO: Can these proofs be derived from the proofs before? *)
  Lemma sim_tgt_TNb T (k : T → spec EV S void) Π Φ :
    ⊢ TGT (Spec.bind TNb k) @ Π {{ Φ }}.
  Proof.
    rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  Admitted.
    (* iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
    (* inv/= Hstep. *)
    (* all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
    (* move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void. *)
  (* Qed. *)

  Lemma sim_tgt_TNb_end Π Φ :
    ⊢ TGT (TNb :> spec EV S _) @ Π {{ Φ }}.
  Proof.
  Admitted.
    (* iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
    (* inv/= Hstep. *)
    (* all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
    (* move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. destruct_all void. *)
  (* Qed. *)

  Lemma sim_src_TUb T (k : T → spec EV S void) Π Φ :
    ⊢ SRC (Spec.bind TUb k) @ Π {{ Φ }}.
  Proof.
  Admitted.
    (* rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
    (* iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
    (* iExists _. iSplit. { iPureIntro. by econs. } *)
    (* iIntros ([??] [??]) "!>". destruct_all void. *)
  (* Qed. *)

  Lemma sim_src_TUb_end Π Φ :
    ⊢ SRC (TUb :> spec EV S void) @ Π {{ Φ }}.
  Proof.
  Admitted.
    (* iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
    (* iExists _. iSplit. { iPureIntro. by econs. } *)
    (* iIntros ([??] [??]) "!>". destruct_all void. *)
  (* Qed. *)

  Lemma sim_gen_TAssume ts (k : _ → spec EV S void) Π Φ (P : Prop) :
    (⌜P⌝ ∗/-∗{ts} ▷ₒ?ts WP{ts} (k tt) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind (TAssume P) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  Admitted.

  Lemma sim_tgt_TAssume (k : _ → spec EV S void) Π Φ (P : Prop) :
    P →
    (▷ₒ TGT (k tt) @ Π {{ Φ }}) -∗
    TGT (Spec.bind (TAssume P) k) @ Π {{ Φ }}.
  Proof. iIntros (?) "?". iApply sim_gen_TAssume. by iFrame. Qed.
  Lemma sim_src_TAssume (k : _ → spec EV S void) Π Φ (P : Prop) :
    (⌜P⌝ -∗ SRC (k tt) @ Π {{ Φ }}) -∗
    SRC (Spec.bind (TAssume P) k) @ Π {{ Φ }}.
  Proof. iIntros "?". by iApply sim_gen_TAssume. Qed.
  (*   iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
  (*   inv/= Hstep. *)
  (*   all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
  (*   move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. *)
  (*   iSplit!. iModIntro. rewrite Heq2. iSplit!. iFrame. *)
  (*   Unshelve. done. *)
  (* Qed. *)

  (* Lemma sim_src_TAssume k Π Φ P os : *)
  (*   (⌜P⌝ -∗ SRC (k tt) @ ? os [{ Π }] {{ Φ }}) -∗ *)
  (*   SRC (Spec.bind (TAssume P) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] [??]) "!>". simplify_eq. iSplit!. iFrame. by iApply "Hsim". *)
  (* Qed. *)

  Lemma sim_gen_TAssert ts (k : _ → spec EV S void) Π Φ (P : Prop) :
    (⌜P⌝ -∗/∗{ts} ▷ₒ?ts WP{ts} (k tt) @ Π {{ Φ }}) -∗
    WP{ts} (Spec.bind (TAssert P) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl.
  Admitted.

  Lemma sim_tgt_TAssert (k : _ → spec EV S void) Π Φ (P : Prop) :
    (⌜P⌝ -∗ ▷ₒ TGT (k tt) @ Π {{ Φ }}) -∗
    TGT (Spec.bind (TAssert P) k) @ Π {{ Φ }}.
  Proof. iIntros "?". by iApply sim_gen_TAssert. Qed.
  Lemma sim_src_TAssert (k : _ → spec EV S void) Π Φ (P : Prop) :
    P →
    (SRC (k tt) @ Π {{ Φ }}) -∗
    SRC (Spec.bind (TAssert P) k) @ Π {{ Φ }}.
  Proof. iIntros (?) "?". iApply sim_gen_TAssert. by iFrame. Qed.

  (* Lemma sim_tgt_TAssert k Π Φ (P : Prop) os : *)
  (*   (⌜P⌝ -∗ ▷ₒ TGT (k tt) @ ? os [{ Π }] {{ Φ }}) -∗ *)
  (*   TGT (Spec.bind (TAssert P) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_tgt_expr_step_None. iIntros (?[??]?? Heq Hstep) "Hs". simplify_eq/=. iModIntro. *)
  (*   inv/= Hstep. *)
  (*   all: revert select (_ ≡ _); rewrite {1}Heq; try by move => /spec_equiv_inv. *)
  (*   move => /spec_equiv_inv //= [? Heq2]. simplify_eq/=. iSpecialize ("Hsim" with "[//]"). *)
  (*   iSplit!. iModIntro. rewrite Heq2. iSplit!. iFrame. *)
  (* Qed. *)

  (* Lemma sim_src_TAssert k Π Φ (P : Prop) os : *)
  (*   P → *)
  (*   SRC (k tt) @ ? os [{ Π }] {{ Φ }} -∗ *)
  (*   SRC (Spec.bind (TAssert P) k) @ ? os [{ Π }] {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros (?) "Hsim". rewrite unfold_bind/=. setoid_rewrite unfold_bind; simpl. *)
  (*   iApply sim_src_expr_step_None. iIntros (?[??]?) "?". simplify_eq/=. iModIntro. *)
  (*   iExists _. iSplit. { iPureIntro. by econs. } *)
  (*   iIntros ([??] ?) "!>". simplify_eq. iSplit!. iFrame. *)
  (*   Unshelve. done. *)
  (* Qed. *)

  Lemma sim_tgt_TAssumeOpt {T} o (x : T) (k : _ → spec EV S void) Π Φ :
    o = Some x →
    TGT k x @ Π {{ Φ }} -∗
    TGT (Spec.bind (TAssumeOpt o) k) @ Π {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.

  Lemma sim_src_TAssumeOpt {T} (k : _ → spec EV S void) (o : option T) Π Φ :
    (∀ x, ⌜o = Some x⌝ -∗ SRC k x @ Π {{ Φ }}) -∗
    SRC (Spec.bind (TAssumeOpt o) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_src_TUb.
  Qed.

  Lemma sim_tgt_TAssertOpt {T} (o : option T) (k : _ → spec EV S void) Π Φ :
    (∀ x, ⌜o = Some x⌝ -∗ TGT k x @ Π {{ Φ }}) -∗
    TGT (Spec.bind (TAssertOpt o) k) @ Π {{ Φ }}.
  Proof.
    iIntros "Hsim".
    destruct o => /=.
    - rewrite unfold_bind/=. by iApply "Hsim".
    - iApply sim_tgt_TNb.
  Qed.

  Lemma sim_src_TAssertOpt {T} o (x : T) (k : _ → spec EV S void) Π Φ :
    o = Some x →
    SRC k x @ Π {{ Φ }} -∗
    SRC (Spec.bind (TAssertOpt o) k) @ Π {{ Φ }}.
  Proof. iIntros (->) "Hsim". simpl. by rewrite unfold_bind/=. Qed.
End spec.
