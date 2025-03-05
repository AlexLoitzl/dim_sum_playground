From iris.proofmode Require Import proofmode.
From iris.bi.lib Require Import fixpoint.
From dimsum.examples.iris Require Import asm rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Arguments subst_static _ !_ /.

Definition echo_rec : fndef := {|
  fd_args := [];
  fd_static_vars := [];
  fd_vars := [];
  fd_body := LetE "c" (rec.Call (Val (ValFn "getc")) []) $
             LetE "_" (rec.Call (Val (ValFn "putc")) [Var "c"]) $
             LetE "c" (rec.Call (Val (ValFn "getc")) []) $
             LetE "_" (rec.Call (Val (ValFn "putc")) [Var "c"]) $
             Val (ValNum 0);
  fd_static := I
|}.

Definition echo_prog : gmap string fndef :=
  <["echo" := echo_rec]> $ ∅.

(* Call with direct return *)
Definition TCallRet {S} (f : string) (vs : list val) (h : heap_state) :
  spec rec_event S (val * heap_state) :=
  TVis (Outgoing, ERCall f vs h);;
  e ← TExist _;
  TVis (Incoming, e);;
  if e is ERReturn v h' then
    TRet (v, h')
  else
    TUb.

Section TCallRet.

  Context `{!dimsumGS Σ} `{!specGS} {S : Type}.

  Lemma sim_src_TCallRet f vs h (k: _ → spec rec_event S void) Π Φ :
    switch Π ({{κ σ POST,
      ∃ f' vs' h1,
      ⌜f' = f⌝ ∗ ⌜vs' = vs⌝ ∗ ⌜h1 = h⌝ ∗ ⌜κ = Some (Outgoing, ERCall f vs h)⌝ ∗
    POST Src _ (spec_trans rec_event S) ({{σ' Π',
      ⌜σ = σ'⌝ ∗  ∃ e,
    switch Π' ({{κ σ POST,
      ⌜κ = Some (Incoming, e)⌝ ∗
    POST Src _ (spec_trans rec_event S) ({{ σ'' Π'',
      ⌜σ = σ''⌝ ∗ ⌜Π = Π''⌝ ∗ (∀ v h', ⌜e = ERReturn v h'⌝ -∗ Φ (k (v, h'))) }})}})}})}}) -∗
    SRC (Spec.bind (TCallRet f vs h) k) @ Π {{ Φ }}.
  Proof.
    iIntros "HC" => /=. rewrite /TCallRet bind_bind.
    iApply sim_gen_TVis. iIntros (s) "Hs". iIntros "% % /=". iIntros "[% [% HΠ]]". subst.
    iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]" => /=. subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs] [-]"); simpl; [done..|]. rewrite bind_bind.
    iApply (sim_src_TExist _). rewrite bind_bind.
    iApply sim_gen_TVis. iIntros (s') "Hs". iIntros (??) "[% [% HΠ']]" => /=.
    subst. iApply "HC" => /=. iSplit!.
    iIntros (??) "[% [% HC]]". destruct!/=.
    iApply "HΠ". iSplit!. iSplitL "Hs". 1: done.
    destruct e. iApply sim_src_TUb.
    rewrite bind_ret_l.
    iApply sim_gen_expr_stop.
    by iApply "HC".
  Qed.

End TCallRet.

(* ********************************************************************************************** *)
(* combined rec program that will return increasing numbers with each call *)
(* ********************************************************************************************** *)
Section sim_getc.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition getc_spec : spec rec_event Z void :=
    Spec.forever(
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn (ValNum v) h)).

  Definition getc_spec_body : spec rec_event Z unit :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "getc");;
    TAssume (vs = []);;
    v ← TGet;
    TPut (v + 1);;
    TVis (Outgoing, ERReturn (ValNum v) h).

  Lemma mstate_var_agree {S : TypeState} `{!mstateG Σ} γ (σ1 σ2 : S) :
    γ ⤳ σ1 -∗ γ ⤳ σ2 -∗ ⌜σ1 = σ2⌝.
  Proof.
    iIntros "H1 H2". iDestruct (ghost_var_agree with "[H1] [H2]") as %[=]; [done..|].
    inv H0. by dimsum.core.axioms.simplify_K.
  Qed.

  Lemma sim_getc_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ ({{ σ' Π',
      ∃ v, ⌜f = "getc"⌝ ∗ ⌜es = []⌝ ∗ spec_state v ∗ ⌜σ' = σ1⌝ ∗
    switch Π' (λ κ (σ : m_state (spec_trans rec_event Z)) POST,
      ⌜κ = Some (Outgoing, ERReturn (ValNum v) h)⌝ ∗ spec_state (v + 1) ∗ ⌜σ = (getc_spec, (v + 1)%Z)⌝
    )}})}}) -∗
    TGT getc_spec @ Π {{ Φ }}.
  Proof.
    iIntros "Hs".
    rewrite {2}/getc_spec unfold_forever /TReceive bind_bind -/getc_spec bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (v') "Hs' !>".
    iIntros (??) "[% [% HΠ]]".
    subst.
    iApply "Hs" => /=. iSplit!. iIntros (??) => /=.
    iDestruct 1 as (???) "[Hs [% HC]]". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs']"); simpl; [done..|]. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". rewrite bind_bind.
    iApply (sim_gen_TGet with "[-]").
    iSplit. 1: done.
    iIntros "!>". rewrite bind_bind.
    iApply (sim_gen_TPut with "[Hs]"). 1: done.
    iIntros "Hs". iIntros "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (v'') "Hs'".
    iDestruct (mstate_var_agree with "Hs Hs'") as "<-".
    iIntros "!> /=".
    iIntros (??) "[% [% HΠ']]" => /=. simplify_eq.
    iApply "HC". iSplit!.
Qed.

  Definition getc_fn_spec (P : Z → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v, P v ∗ ⌜es = []⌝ ∗ POST (λ ret, ⌜ret = v⌝ ∗ P (v + 1))%I.

  Lemma sim_getc fns Π_l (P : Z → iProp Σ):
    rec_fn_auth fns -∗
    "getc" ↪ None -∗
    switch_link Tgt Π_l ({{σ_l POST,
      ∃ h v, P v ∗
    POST (ERCall "getc" [] h) (spec_trans _ Z) (getc_spec, v) ({{σ_r'' Π_r',
    switch_link Tgt Π_r' ({{σ_r''' POST,
      ∃ h', ⌜σ_r''' = (getc_spec, (v + 1)%Z)⌝ ∗
    POST (ERReturn (ValNum v) h') _ σ_l ({{σ_l''' Π_l',
      ⌜Π_l' = Π_l⌝ ∗ P (v + 1)
    }})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π_l "getc" (getc_fn_spec P).
  Proof.
    iIntros "#? ? Hs". iIntros (es Φ) "[% [HP [-> HΦ]]]".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iIntros (??) "[% [% HΠ]]". subst. iApply "Hs". iFrame. iSplit!. iIntros (??) "[-> Hs]".

    iMod (mstate_var_alloc Z) as (γ) "?".
    iMod (mstate_var_split γ v with "[$]") as "[Hγ Hγ']".
    pose (Hspec := SpecGS γ).

    iApply (sim_gen_expr_intro _ tt with "[Hγ]"); simpl; [done..|].

    iApply sim_getc_spec.
    iIntros (??) "[% [% [% [% Hσ]]]]" => /=.
    iApply "Hs" => /=. iSplit!.
    iIntros (??) "[% [% HΠ0]]" => /=. simplify_eq.
    iApply "Hσ". iFrame. iSplit!.
    iIntros (??) "[% [? %]]" => /=. simplify_eq.
    iApply "HΠ0" => /=. iSplit!.
    iIntros (??) "[% Hs]" => /=. subst.

    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs" => /=. iSplit!.
    iIntros (??) "[% [% [% ?]]]" => /=. subst.

    iApply "HΠ" => /=. iSplit!. iFrame. iApply "HΦ". by iFrame.
  Qed.

End sim_getc.

(* ********************************************************************************************** *)
(* Prove ⟦echo⟧_rec ⊕ ⟦getc⟧_spec ⪯ ⟦echo_getc⟧_spec *)
(* ********************************************************************************************** *)
Section echo_getc.

  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition echo_getc_spec_body : spec rec_event Z unit :=
    v ← TGet;
    TPut (v + 1);;
    h ← TExist _;
    '(_, h') ← TCallRet "putc" [(ValNum v)] h;
    TAssume (h = h').

  Definition echo_getc_spec : spec rec_event Z void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "echo");;
    TAssume (vs = []);;
    echo_getc_spec_body;;
    echo_getc_spec_body;;
    h' ← TExist _;
    TVis (Outgoing, ERReturn (ValNum 0) h');;
    TUb.

  Definition echo_left_linkP γ_oe γ_q γ_r : Z → iProp Σ :=
    (λ v, γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ [None : seq_product_case] ∗ γ_r ⤳ (getc_spec, v))%I.

  (* Here I will take two things, one is the state of the tgt and one of the src *)
  Definition putc_echo_fn_spec (P : Z → (spec rec_event Z void) → iProp Σ) (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
    ∃ v k, P v (Spec.bind echo_getc_spec_body (fun _ => k)) ∗ ⌜es = [Val v]⌝ ∗ POST (λ _, P (v + 1)%Z k)%I.

  Lemma sim_echo_body Π_t Π_s (P : Z → (spec rec_event Z void) → iProp Σ) :
    "putc" ↪ None -∗
    switch_external_fixed Π_t (spec_trans _ Z) Π_s ({{κ0 σ_t POST0,
      ∃ vs h v k, P v (Spec.bind echo_getc_spec_body (fun _ => k)) ∗
      ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
    POST0 (Spec.bind echo_getc_spec_body (fun _ => k), v) ({{σ_s1' Π_s',
      ∃ e : rec_ev, ⌜Π_s' = Π_s⌝ ∗
    switch Π_s' ({{ κ3 σ_s2 POST2,
      ⌜κ3 = Some (Incoming, e)⌝ ∗
    POST2 Src _ (spec_trans _ Z) ({{ σ_s2' Π_s'',
      ⌜Π_s'' = Π_s'⌝ ∗ ⌜σ_s2 = σ_s2'⌝ ∗
    switch Π_s ({{ κ4 σ_s3 POST3,
      ∃ v' h', ⌜e = ERReturn v' h'⌝ ∗ ⌜κ4 = None⌝ ∗
    POST3 Tgt _ _ ({{ σ_t1 Π_t',
      ⌜σ_t1 = σ_t⌝ ∗ ⌜Π_t' = Π_t⌝ ∗
    switch Π_t ({{ κ5 σ_t2 POST4,
      ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
    POST4 Tgt rec_event rec_trans ({{ σ_t3 Π_t',
      ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π_t = Π_t'⌝ ∗ P (v + 1) k
      }})}})}})}})}})}})}})}}) -∗
    rec_fn_spec_hoare Tgt Π_t "putc" (putc_echo_fn_spec P).
  Proof.
    iIntros "#? Hs %% [% [% [? [-> HΦ]]]]".

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#? ? ? !> %% [-> [-> HΠ]]" => /=.
    iApply "Hs" => /=. iFrame. iSplit!.
    iIntros (? Πs) "[-> [-> Hs']]" => /=.

    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s v with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. rewrite bind_bind.
    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. rewrite bind_bind.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". rewrite bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind.

    iApply sim_src_TCallRet.

    iIntros (??) "[% [% [% [% [% [% [% Hσ]]]]]]]" => /=. simplify_eq.
    iApply "Hs'". iSplit!.
    iIntros (??) "[% [% [% Hs']]]" => /=. subst.
    iApply "Hσ". iSplit!. iIntros (??) "[% Hσ0]".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% Hs']]". subst.
    iApply "Hσ0". iSplit!. iIntros (??) "% % /= % Hγs_s'". subst.
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s'] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
    iIntros (?) "/= % Hγs_s'". iApply sim_gen_stop.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??) "[-> [-> Hs']]".
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% [% ?]]]" => /=. subst.
    iApply "HΠ" => /=. iSplit!. iFrame. by iApply "HΦ".
  Qed.

  Lemma sim_echo Π (P : Z → iProp Σ) (Q : Z → (spec rec_event Z void) → iProp Σ) :
    "echo" ↪ Some echo_rec -∗
    □ rec_fn_spec_hoare Tgt Π "getc" (getc_fn_spec P) -∗
    □ rec_fn_spec_hoare Tgt Π "putc" (putc_echo_fn_spec Q) -∗
    rec_fn_spec_hoare Tgt Π "echo" (λ es POST, ∃ v k, ⌜es = []⌝ ∗
      P v ∗
      Q v (Spec.bind echo_getc_spec_body (fun _ => (Spec.bind echo_getc_spec_body (fun _ => k)))) ∗
      POST (λ ret, P (v + 2) ∗ Q (v + 2) k ∗ ⌜ret = 0⌝)).
  Proof.
    iIntros "#? #Hgetc #Hputc".
    iIntros (es Φ) => /=. iDestruct 1 as (v k ->) "[HP [HQ HΦ]]".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hoof !>".
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    (* getc 1 *)
    iApply "Hgetc". iFrame. iSplit!. iIntros (?) "[-> ?]".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    (* putc 1 *)
    iApply "Hputc". iFrame. iSplit!. iIntros (?) "?".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    (* getc 2 *)
    iApply "Hgetc". iFrame. iSplit!. iIntros (?) "[-> ?]".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    (* putc 2 *)
    iApply "Hputc". iFrame. iSplit!. iIntros (?) "?".
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.

    iApply sim_gen_expr_stop. iSplit!.
    iSplitL "Hoof".
    { destruct ls; [by iApply big_sepL2_nil |done]. }
    replace (v + 1 + 1) with (v + 2) by lia.
    iApply "HΦ". by iFrame.
  Qed.

  (* Definition echo_left_external γs : Z → iProp Σ := *)
  (*   (λ v, γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ [None : seq_product_case] ∗ γ_r ⤳ (getc_spec, v))%I. *)

  Lemma sim_echo_full Π_t Π_s γs (σ_s : m_state (spec_trans _ Z)) γ_oe γ_q γ_r k :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γs ⤳ σ_s -∗
    γ_oe ⤳ @None rec_ev -∗
    γ_q ⤳ [(None : seq_product_case)] -∗
    γ_r ⤳ (getc_spec, 0) -∗
    □ rec_fn_spec_hoare Tgt Π_t "getc" (getc_fn_spec (echo_left_linkP γ_oe γ_q γ_r)) -∗
    □ rec_fn_spec_hoare Tgt Π_t "putc" (getc_fn_spec (echo_left_linkP γ_oe γ_q γ_r)) -∗
    ⌜σ_s.1 ≡ Spec.bind echo_getc_spec_body (fun _ => k)⌝ -∗
    ⌜σ_s.2 = 0⌝ -∗
    rec_fn_spec_hoare Tgt Π_t "echo" ({{ es POST_e,
      ⌜es = []⌝ ∗
      □ switch_external_fixed Π_t (spec_trans _ Z) Π_s ({{κ0 σ_t POST0,
          ∃ vs h (σs : m_state (spec_trans rec_event Z)) (q' : list seq_product_case) (r : m_state (spec_trans rec_event Z)),
          γs ⤳ σs ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ q' ∗ γ_r ⤳ r ∗
          ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
        POST0 σs ({{σ_s1' Π_s',
          ∃ e : rec_ev, ⌜Π_s' = Π_s⌝ ∗
        switch Π_s' ({{ κ3 σ_s2 POST2,
          ⌜κ3 = Some (Incoming, e)⌝ ∗
        POST2 Src _ (spec_trans _ Z) ({{ σ_s2' Π_s'',
          ⌜Π_s'' = Π_s'⌝ ∗ ⌜σ_s2 = σ_s2'⌝ ∗
        switch Π_s ({{ κ4 σ_s3 POST3,
          ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
        POST3 Tgt _ _ ({{ σ_t1 Π_t',
          ⌜σ_t1 = σ_t⌝ ∗ γs ⤳ σ_s3 ∗ ⌜Π_t' = Π_t⌝ ∗
        switch Π_t ({{ κ5 σ_t2 POST4,
          ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
        POST4 Tgt rec_event rec_trans ({{ σ_t3 Π_t',
          ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π_t = Π_t'⌝ ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ q' ∗ γ_r ⤳ r
      }})}})}})}})}})}})}})}}) ∗
      POST_e (λ v, ∃ (σs r: m_state (spec_trans rec_event Z)), ⌜v = 0⌝ ∗ γs ⤳ σs ∗ ⌜σs.1 ≡ k⌝ ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ [(None : seq_product_case)] ∗ γ_r ⤳ r)
    }}).

  Lemma sim_echo_full Π_t Π_s γs (σ_s : m_state (spec_trans _ Z)) γ_oe γ_q γ_r k :
    "echo" ↪ Some echo_rec -∗
    "getc" ↪ None -∗
    "putc" ↪ None -∗
    γs ⤳ σ_s -∗
    γ_oe ⤳ @None rec_ev -∗
    γ_q ⤳ [(None : seq_product_case)] -∗
    γ_r ⤳ (getc_spec, 0) -∗
    □ rec_fn_spec_hoare Tgt Π_t "getc" (getc_fn_spec (echo_left_linkP γ_oe γ_q γ_r)) -∗
    ⌜σ_s.1 ≡ Spec.bind echo_getc_spec_body (fun _ => k)⌝ -∗
    ⌜σ_s.2 = 0⌝ -∗
    rec_fn_spec_hoare Tgt Π_t "echo" ({{ es POST_e,
      ⌜es = []⌝ ∗
      □ switch_external_fixed Π_t (spec_trans _ Z) Π_s ({{κ0 σ_t POST0,
          ∃ vs h (σs : m_state (spec_trans rec_event Z)) (q' : list seq_product_case) (r : m_state (spec_trans rec_event Z)),
          γs ⤳ σs ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ q' ∗ γ_r ⤳ r ∗
          ⌜κ0 = Some (Outgoing, ERCall "putc" vs h)⌝ ∗
        POST0 σs ({{σ_s1' Π_s',
          ∃ e : rec_ev, ⌜Π_s' = Π_s⌝ ∗
        switch Π_s' ({{ κ3 σ_s2 POST2,
          ⌜κ3 = Some (Incoming, e)⌝ ∗
        POST2 Src _ (spec_trans _ Z) ({{ σ_s2' Π_s'',
          ⌜Π_s'' = Π_s'⌝ ∗ ⌜σ_s2 = σ_s2'⌝ ∗
        switch Π_s ({{ κ4 σ_s3 POST3,
          ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
        POST3 Tgt _ _ ({{ σ_t1 Π_t',
          ⌜σ_t1 = σ_t⌝ ∗ γs ⤳ σ_s3 ∗ ⌜Π_t' = Π_t⌝ ∗
        switch Π_t ({{ κ5 σ_t2 POST4,
          ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
        POST4 Tgt rec_event rec_trans ({{ σ_t3 Π_t',
          ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π_t = Π_t'⌝ ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ q' ∗ γ_r ⤳ r
      }})}})}})}})}})}})}})}}) ∗
      POST_e (λ v, ∃ (σs r: m_state (spec_trans rec_event Z)), ⌜v = 0⌝ ∗ γs ⤳ σs ∗ ⌜σs.1 ≡ k⌝ ∗ γ_oe ⤳ @None rec_ev ∗ γ_q ⤳ [(None : seq_product_case)] ∗ γ_r ⤳ r)
    }}).
  Proof. 
    iIntros "#?#?#? Hγs Hγ_oe Hγ_q Hγ_r #Hgetc %Hσ_s1 %Hσ_s2 %% [-> [#Hs Hend]]" => /=.

    iApply (sim_echo with "[//] [$]").

    { iModIntro.
      iIntros (??) "[% [[? [? ?]] [-> ?]]]".


      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst.
      iApply "Hs" => /=. iSplit!. iFrame. iSplit!.
      iIntros (? Πs) "[% [% Hs']]" => /=. subst.

      iMod (mstate_var_alloc Z) as (γs_s) "?".
      iMod (mstate_var_split γs_s σ_s.2 with "[$]") as "[Hγs_s Hγs_s']".
      pose (HSrcSpec := SpecGS γs_s).

      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. rewrite bind_bind.
      iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. rewrite bind_bind.
      iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". rewrite bind_bind.
      iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind.

      iApply sim_src_TCallRet.

      iIntros (??) "[% [% [% [% [% [% [% Hσ]]]]]]]" => /=. simplify_eq.
      iApply "Hs'". iSplit!. by rewrite Hσ_s2.
      iIntros (??) "[% [% [% Hs']]]" => /=. subst.
      iApply "Hσ". iSplit!. iIntros (??) "[% Hσ0]".
      iApply "Hs'". iSplit!. iIntros (??) "[% [% Hs']]". subst.
      iApply "Hσ0". iSplit!. iIntros (??) "% % /= % Hγs_s'". subst.
      iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s'] [-]"); [simpl; done..|]. rewrite bind_bind.
      iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
      iIntros (?) "/= % Hγs_s'". iApply sim_gen_stop.
      iApply "Hs'" => /=. iSplit!.
      iIntros (??)"[% [? [% Hs']]]". subst.
      iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
      iApply "Hs'". iSplit!. iIntros (??) "[% [% [% ?]]]" => /=. subst.
      iApply "HΠ" => /=. iSplit!. iFrame. iApply "HΦ'".
      iFrame.


    }


    iSplit!. iFrame.

    (* putc 1 *)
    iIntros (??) "[[Hγ_oe [Hγ_q Hγ_r]] [-> HΦ']]".

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst.
    iApply "Hs" => /=. iSplit!. iFrame. iSplit!.
    iIntros (? Πs) "[% [% Hs']]" => /=. subst.

    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s σ_s.2 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|]. rewrite bind_bind.
    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. rewrite bind_bind.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". rewrite bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind.

    iApply sim_src_TCallRet.

    iIntros (??) "[% [% [% [% [% [% [% Hσ]]]]]]]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. by rewrite Hσ_s2.
    iIntros (??) "[% [% [% Hs']]]" => /=. subst.
    iApply "Hσ". iSplit!. iIntros (??) "[% Hσ0]".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% Hs']]". subst.
    iApply "Hσ0". iSplit!. iIntros (??) "% % /= % Hγs_s'". subst.
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s'] [-]"); [simpl; done..|]. rewrite bind_bind.
    iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
    iIntros (?) "/= % Hγs_s'". iApply sim_gen_stop.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??)"[% [? [% Hs']]]". subst.
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% [% ?]]]" => /=. subst.
    iApply "HΠ" => /=. iSplit!. iFrame. iApply "HΦ'".
    iFrame.

    (* putc2 *)
    iIntros (??) "[[Hγ_oe [Hγ_q Hγ_r]] [-> HΦ']]".

    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#? ? ? !> %% [% [% HΠ]]" => /=. subst.
    iApply "Hs" => /=. iSplit!. iFrame. iSplit!.
    iIntros (? Πs2) "[% [% Hs']]" => /=. subst.

    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "%".

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s'] [-]"); [simpl; done..|]. rewrite bind_bind.

    iApply (sim_gen_TGet (H := HSrcSpec) with "[-]"). iSplit. 1: done. rewrite bind_bind.
    iApply (sim_gen_TPut (H := HSrcSpec) with "[$]"). iIntros "Hγs_s". rewrite bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec)). rewrite bind_bind.

    iApply sim_src_TCallRet.
    iIntros (??) "[% [% [% [% [% [% [% Hσ]]]]]]]" => /=. simplify_eq.
    iApply "Hs'". iSplit!. by rewrite Hσ_s2.
    iIntros (??) "[% [% [% Hs']]]" => /=. subst.
    iApply "Hσ". iSplit!. iIntros (??) "[% Hσ0]".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% Hs']]". subst.
    iApply "Hσ0". iSplit!. iIntros (??) "% % /= % Hγs_s'". subst.
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s'] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros "->". iApply sim_gen_expr_stop.
    iIntros (?) "/= % Hγs_s'". iApply sim_gen_stop.
    iApply "Hs'" => /=. iSplit!.
    iIntros (??)"[% [? [% Hs']]]". subst.
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "Hs'". iSplit!. iIntros (??) "[% [% [% ?]]]" => /=. subst.
    iApply "HΠ" => /=. iSplit!. iFrame.
    iApply "HΦ'".
    iFrame. iIntros "% [[? [? ?]] %]".
    iApply "Hend". iSplit!. by iFrame.
  Qed.

  Let m_t := rec_link_trans {["echo"]} {["getc"]} rec_trans (spec_trans rec_event Z).

  Lemma echo_getc_sim :
    rec_state_interp (rec_init echo_prog) None -∗
    (MLFRun None, [], rec_init echo_prog, (getc_spec, 0)) ⪯{m_t,
      spec_trans rec_event Z} (echo_getc_spec, 0).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=".

    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γs) "Hγs".
    (* Entire Target Module *)
    iMod (mstate_var_alloc (m_state m_t)) as (γt) "Hγt".
    (* Event *)
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".

    (* Source's spec state *)
    iMod (mstate_var_alloc Z) as (γs_s) "?".
    iMod (mstate_var_split γs_s 0 with "[$]") as "[Hγs_s Hγs_s']".
    pose (HSrcSpec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γt γs γκ with "Hγt Hγs Hγκ [-]"). iIntros "Hγs".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
    destruct!/=. case_match; destruct!/=.

    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".
    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iEval (unfold echo_getc_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (H := HSrcSpec) (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis (H := HSrcSpec)). iIntros "% Hγs_s %% [-> [-> _ ]]".

    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iDestruct (mstate_var_agree with "Hγs_s Hγs_s'") as "->".

    iIntros "Hγs". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
    iIntros "Hγs Hγt Hγκ".

    iApply (sim_gen_expr_intro (Λ := spec_mod_lang (H := HSrcSpec) _ _ ) _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?).
    iApply (sim_src_TAssume (H := HSrcSpec)). iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs_s".

    iIntros (??) "[-> [-> _]]".
    rewrite bool_decide_true; [|done].
    iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
    iIntros "Hγs".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!> %". simplify_map_eq.

    (* Target's spec module (Right linking case - getc) *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event Z))) as (γt_r) "Hγt_r".

    iMod (mstate_var_alloc (list seq_product_case)) as (γt_q) "Hγt_q".

    (* Linking event to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γt_oe) "Hγt_oe".

    iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [$] [$] [-]").
    iIntros "Hγt_q Hγt_r Hγt_oe".

    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }

    iApply (sim_gen_expr_intro _ [] with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (Π_s := sim_src_constP γκ γt (EV := rec_event) (m_t := m_t) (m_s := spec_trans rec_event Z)).
    set (Π_t := tgt_link_left_constP _ _ _ _ _).

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.

    iDestruct (mstate_var_merge with "Hγs_s Hγs_s'") as "[% Hγs_s]".

    rewrite /echo_prog in Hin. simplify_map_eq.

    iApply (sim_echo_full with "[] [] [] Hγs Hγt_oe Hγt_q Hγt_r [] [//] [//]"). 1-3: by iApply (rec_fn_intro with "[$]") => /=.
    {
      iModIntro. iApply (sim_getc with "[//]"). by iApply (rec_fn_intro with "[$]").
      iIntros (??) => /=.
      iDestruct 1 as (??) "[[Hγt_oe [Hγt_q Hγt_r]] [-> HC]]" => /=.

      iIntros "%%% Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iIntros (??????). destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_recv_right with "[-]"). iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_run_right with "[-]"). iApply "HC". iSplit!.
      iIntros (??). iDestruct 1 as (??) "[% HC]" => /=. simplify_eq.
      iIntros (??????). destruct!/=.
      iApply (sim_tgt_link_left_const_recv γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply "HC". iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros "%%% Hγt_q' Hγt_r' Hγt_oe'".
      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]". iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply ("HC" with "[-]"). iSplit!. iFrame.
    }
    iSplit!.
    - iIntros "!> %% [% [% [% [% [% [Hγs [Hγt_oe [Hγt_q [Hγt_r [% HC]]]]]]]]]]" => /=.
      subst. iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iIntros (??????). destruct!/=. rewrite bool_decide_false //.

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (->) "HC".
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??) "[% HC]". simplify_eq.
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs". iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (?? -> ->) "HC".
      iApply (sim_src_constP_next with "[Hγt] [Hγκ] [Hγs] [%] [-]"); [done..|].
      iIntros "Hγs". destruct!/=.
      iApply (sim_tgt_link_left_const_recv γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "Hγt_q Hγt_r Hγt_oe".
      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC".
      iIntros (???) "Hγt_q' Hγt_r' Hγt_oe'".

      iDestruct (mstate_var_merge with "Hγt_r Hγt_r'") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe Hγt_oe'") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q Hγt_q'") as "[<- Hγt_q]".
      iIntros (?). simplify_eq.

      iApply (sim_tgt_link_left_const_run γt_q γt_r γt_oe with "[$] [Hγt_r] [$] [-]"). 1: done.
      iIntros "???".

      iApply "HC". iSplit!. iFrame.
    - iIntros (?) "[% [% [% [Hγs [% [Hγt_oe [Hγt_q Hγt_r]]]]]]]".
      iApply sim_tgt_rec_ReturnExt. iIntros (???) "#? ? ? !> %% [% [% ?]] /=".
      subst.
      iIntros (???) "???".

      iDestruct (mstate_var_merge with "Hγt_r [$]") as "[<- Hγt_r]".
      iDestruct (mstate_var_merge with "Hγt_oe [$]") as "[<- Hγt_oe]".
      iDestruct (mstate_var_merge with "Hγt_q [$]") as "[<- Hγt_q]".
      iIntros (??????). destruct!/=.

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      
      iMod (mstate_var_split γs_s σs.2 with "[$]") as "[Hγs_s Hγs_s']".
      iApply (sim_gen_expr_intro _ tt with "[Hγs_s]"); simpl; [done..|].
      iApply (sim_src_TExist with "[-]").
      iApply (sim_gen_TVis with "[-]").
      iIntros (?) "Hγs_s %% [% [% ?]] /=".

      iApply (sim_src_constP_elim with "[Hγt] [Hγκ] [-]"); [done..|].
      iIntros "Hγt Hγκ". iSplit!.

      iApply (sim_tgt_constP_intro γt γs γκ with "[Hγt] [Hγs] [Hγκ] [-]"); [done..|].
      iIntros "Hγs".

      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????).
      destruct!/=. case_match; destruct!/=.

      iApply (sim_tgt_constP_elim γt γs γκ with "[Hγs] [-]"); [done..|].
      iIntros "Hγs Hγt Hγκ".
      iApply (sim_gen_expr_intro _ tt with "[Hγs_s]"); simpl; [done..|].
      iApply sim_src_TUb_end.
    Qed.

End echo_getc.
