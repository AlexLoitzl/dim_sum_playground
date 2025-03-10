From dimsum.core.iris Require Export iris expr2 spec2.
From dimsum.examples Require Export rec.
From dimsum.examples.iris Require Export rec_basic.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO: upstream *)
Global Instance spec_inhabited EV S R : Inhabited (spec EV S R) := populate TUb.
Global Instance link_case_inhabited EV : Inhabited (link_case EV) := populate (MLFUb inhabitant).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Global Instance rec_state_inhabited : Inhabited rec_state := populate (Rec inhabitant inhabitant inhabitant).

Program Canonical Structure rec_mod_lang {Σ} `{!recGS Σ} := {|
  mexpr := expr;
  mectx := list expr_ectx;
  mfill := expr_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := st_expr σ = e;
  mstate_interp σ := rec_state_interp σ None;
|}.
Next Obligation. move => ?????/=. by rewrite expr_fill_app. Qed.

Definition rec_fn_spec `{!dimsumGS Σ} `{!recGS Σ} (ts : tgt_src) (Π : option rec_event → _ → iProp Σ)
  (f : string) (C : list expr → (val → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ es Φ, C es (λ v, Φ (Val v)) -∗ TGT Call (Val (ValFn f)) es @ Π {{ Φ }}).

Definition rec_fn_spec_hoare `{!dimsumGS Σ} `{!recGS Σ} (ts : tgt_src) (Π : option rec_event → _ → iProp Σ)
  (f : string) (pre : list expr → ((val → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  rec_fn_spec ts Π f (λ es Φ, pre es (λ POST, (∀ v', POST v' -∗ Φ v')))%I.

Section fn_spec.
  Context `{!dimsumGS Σ} `{!recGS Σ}.
  Lemma rec_fn_spec_ctx ts Π f C :
    (ord_later_ctx -∗ rec_fn_spec ts Π f C) -∗
    rec_fn_spec ts Π f C.
  Proof. iIntros "Hc" (??) "?". iApply sim_gen_expr_ctx. iIntros "?". by iApply ("Hc" with "[$]"). Qed.
  Lemma rec_fn_spec_hoare_ctx ts Π f C :
    (ord_later_ctx -∗ rec_fn_spec_hoare ts Π f C) -∗
    rec_fn_spec_hoare ts Π f C.
  Proof. iIntros "Hc" (??) "?". iApply sim_gen_expr_ctx. iIntros "?". by iApply ("Hc" with "[$]"). Qed.
End fn_spec.


Section lifting.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_tgt_rec_Waiting_raw fns K Π (b : bool) h :
    ((∀ f fn vs h', ⌜fns !! f = Some fn⌝ -∗
         ▷ₒ Π (Some (Incoming, ERCall f vs h'))
             (Rec (expr_fill K (ReturnExt b (Call (Val (ValFn f)) (Val <$> vs)))) h' fns)) ∧
      ∀ v h', ⌜b⌝ -∗
         ▷ₒ Π (Some (Incoming, ERReturn v h'))
             (Rec (expr_fill K (Val v)) h' fns)) -∗
    Rec (expr_fill K (Waiting b)) h fns ≈{rec_trans}≈>ₜ Π.
  Proof.
    iIntros "HΠ". iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    - iDestruct "HΠ" as "[HΠ _]". iDestruct ("HΠ" with "[//]") as "HΠ".
      iModIntro. iSplit!. do 2 iModIntro. done.
    - iDestruct "HΠ" as "[_ HΠ]". iDestruct ("HΠ" with "[//]") as "HΠ".
      iModIntro. iSplit!. do 2 iModIntro. done.
  Qed.

  Lemma sim_tgt_rec_ReturnExt v Π Φ (b : bool) :
    (∀ K h fns,
      rec_fn_auth fns -∗
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
      ▷ₒ switch_id Tgt rec_trans Π (Some (Outgoing, ERReturn v h)) (Rec (expr_fill K (Waiting b)) h fns) ({{ σ,
         ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
         rec_mapsto_auth (h_heap (st_heap σ)) ∗
         rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e'}})) -∗
    TGT ReturnExt b (Val v) @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$] [$] [$]"). iModIntro. iSplit!.
    do 2 iModIntro. iApply (switch_id_mono with "HΦ").
    iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_static f (fd_static_vars fn) (subst_l (fd_args fn) vs (fd_body fn))) @ Π {{ Φ }}) -∗
    TGT Call (Val (ValFn f)) es @ Π {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iSplit!. iFrame "∗#".
  Qed.

  Lemma sim_tgt_rec_Call_external f es Π Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ K h fns,
      rec_fn_auth fns -∗
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
      ▷ₒ switch_id Tgt rec_trans Π (Some (Outgoing, ERCall f vs h))
        (Rec (expr_fill K (Waiting true)) h fns) ({{ σ,
          ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
           rec_mapsto_auth (h_heap (st_heap σ)) ∗
      rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e'}})) -∗
    TGT Call (Val (ValFn f)) es @ Π {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros "Hfn HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$] [$] [$]"). iModIntro. iSplit!. do 2 iModIntro.
    iApply (switch_id_mono with "HΦ"). iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_BinOp Π Φ v1 v2 v3 op :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3)) -∗
    TGT BinOp (Val v1) op (Val v2) @ Π {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_Load Π Φ l v :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v)) -∗
    TGT Load (Val (ValLoc l)) @ Π {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. do 2 iModIntro. iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_Store Π Φ l v v' :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val v')) -∗
    TGT Store (Val (ValLoc l)) (Val v') @ Π {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_mapsto_update with "[$] [$]") as "[??]".
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. { by eexists. } do 2 iModIntro. iSplit!.
    iFrame "∗#" => /=. rewrite dom_alter_L. iFrame. by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_AllocA e Π Φ vs :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e @ Π {{ e',
     ∃ v, ⌜e' = Val v⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' }}) -∗
    TGT AllocA vs e @ Π {{ Φ }}.
  Proof.
    iIntros (Hall) "HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_mapsto_alloc_list with "Hh") as "[Hh ?]"; [done|].
    iMod (rec_alloc_alloc_list with "Ha") as "[Ha Has]"; [done..|].
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. do 2 iModIntro. iSplit!.
    iFrame "∗#" => /=.

    iApply (sim_gen_expr_bind _ [FreeACtx _] _ with "[-]") => /=.
    iApply (sim_gen_expr_wand with "HΦ") => /=.
    iIntros (?) "[% [% [Hl HΦ]]]" => /=. simplify_eq/=.
    iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? h1 fns1] ??) "[#Hfns1 [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_alloc_free_list with "Hh Ha [$] [$]") as (??) "[??]".
    iModIntro. iSplit!. { done. } do 2 iModIntro. iSplit!.
    iFrame "∗#" => /=. by iApply sim_gen_expr_stop.
  Qed.

  Lemma sim_tgt_rec_LetE Π Φ s v e :
    (▷ₒ TGT (subst s v e) @ Π {{ Φ }}) -∗
    TGT LetE s (Val v) e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iSplit!.
    iFrame "∗#" => /=.
  Qed.

  Lemma sim_tgt_rec_If Π Φ (b : bool) e1 e2 :
    (▷ₒ TGT (if b then e1 else e2) @ Π {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps_None with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iSplit!.
    iFrame "∗#" => /=.
  Qed.

End lifting.
