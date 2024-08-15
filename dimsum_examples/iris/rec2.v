From dimsum.core.iris Require Export iris expr2 spec2.
From dimsum.examples Require Export rec.
From dimsum.examples.iris Require Export rec_basic.
From dimsum.examples Require Import memmove.
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
      ▷ₒ switch_id Tgt rec_trans Π (Some (Outgoing, ERReturn v h)) (Rec (expr_fill K (Waiting b)) h fns) (λ σ,
         ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
         rec_mapsto_auth (h_heap (st_heap σ)) ∗
         rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e')) -∗
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
        (Rec (expr_fill K (Waiting true)) h fns) (λ σ,
          ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
           rec_mapsto_auth (h_heap (st_heap σ)) ∗
      rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e')) -∗
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

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_memcpy Π :
    "memcpy" ↪ Some memcpy_rec -∗
    rec_fn_spec_hoare Tgt Π "memcpy" (λ es POST,
      ∃ d s n o d' s' hvss hvsd, ⌜es = [Val $ ValLoc d; Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o]⌝ ∗
      ⌜n = Z.of_nat (length hvss)⌝ ∗
      ⌜length hvss = length hvsd⌝ ∗
      ⌜o = 1 ∨ o = -1⌝ ∗
      ⌜d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1))⌝ ∗
      ⌜s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1))⌝ ∗
      ⌜(if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2)⌝ ∗
      ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) ∗
      (POST (λ v, ⌜v = 0⌝ ∗ ([∗ map] l↦v∈array d' hvss ∪ array s' hvss, l ↦ v)))).
  Proof.
    iIntros "#Hf". iApply rec_fn_spec_hoare_ctx. iIntros "#?".
    iApply ord_loeb; [done|]. iIntros "!> #IH". iIntros (es Φ) "HΦ".
    iDestruct "HΦ" as (d s n o d' s' hvss hvsd ? Hn Hlen Ho Hd' Hs' Hle) "[Hm HΦ]"; simplify_eq/=.
    iApply (sim_tgt_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] _ with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. case_bool_decide (0 < _).
    2: { destruct hvss, hvsd => //. iApply sim_gen_expr_stop. iSplit!. iApply "HΦ". iSplit!. }
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [StoreRCtx _] with "[-]") => /=.
    destruct Ho; simplify_eq; case_bool_decide => //.
    - destruct hvss as [|v hvss]; [done|] => /=.
      destruct hvsd as [|vd hvsd]; [done|] => /=.
      rewrite !array_cons.
      iDestruct (big_sepM_lookup_acc _ _ s v with "[$]") as "[Hsv Hm]". { by simplify_map_eq. }
      iApply (sim_tgt_rec_Load with "Hsv"). iIntros "Hsv !>" => /=.
      iDestruct ("Hm" with "[$]") as "Hm".
      have [? Hx]: is_Some ((<[s:=v]> (array (s +ₗ 1) hvss) ∪ <[d:=vd]> (array (d +ₗ 1) hvsd)) !! d).
      { apply lookup_union_is_Some. simplify_map_eq. naive_solver. }
      rewrite (big_sepM_delete _ _ _ _ Hx).
      iDestruct "Hm" as "[Hdv Hm]".
      iApply (sim_tgt_rec_Store with "Hdv"). iIntros "Hdv !>" => /=.
      iApply (sim_tgt_rec_LetE). iIntros "!>" => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_; _] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      destruct (decide (d.1 = s.1 ∧ s.2 ≤ d.2 + length hvss)) as [[??]|Hn]; simplify_eq.
      + rewrite -(insert_union_l _ _ s) insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_union. rewrite delete_notin. 2: { apply array_lookup_None => /=. naive_solver lia. }
        destruct (decide (d = s)); simplify_eq.
        * rewrite delete_insert_delete delete_insert. 2: { apply array_lookup_None => /=. lia. }
          iApply "IH". iFrame. iSplit!. { lia. }
          iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
          rewrite -insert_union_l -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s ( d+ₗ1)) //=; [|naive_solver lia].
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite insert_length. done. } { simpl. naive_solver lia. }
          iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
          rewrite -insert_union_l. iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
          rewrite -insert_union_r_Some //. apply array_lookup_is_Some. split!; naive_solver lia.
      + rewrite delete_union delete_insert. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_insert_ne. 2: { move => ?. subst. naive_solver lia. }
        rewrite delete_notin. 2: {
          apply array_lookup_None => /=.
          destruct (decide (s.2 ≤ d.2 + length hvss)); naive_solver lia. }
        rewrite -!insert_union_l (big_sepM_delete _ (<[s:=_]>_) s v). 2: by simplify_map_eq.
        iDestruct "Hm" as "[Hsv Hm]".
        rewrite delete_insert. 2: {
          apply lookup_union_None. rewrite !array_lookup_None => /=.
          destruct (decide (s.2 ≤ d.2 + length hvss)); naive_solver lia. }
        iApply "IH". iFrame. iSplit!. { lia. } { simpl. naive_solver lia. }
        iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
        rewrite -insert_union_r. 2: {
          apply array_lookup_None => /=.
          destruct (decide (s.2 ≤ d.2 + length hvss)); naive_solver lia. }
        iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        iApply (big_sepM_insert_2 with "[Hsv]"); [done|].
        done.
    - destruct hvss as [|v hvss _] using rev_ind; [done|] => /=.
      destruct hvsd as [|vd hvsd _] using rev_ind; [simplify_eq/=; lia|] => /=.
      rewrite app_length/=. rewrite !app_length/= in Hlen.
      have -> : (- (length hvss + 1)%nat + 1) = - Z.of_nat (length hvss) by lia.
      rewrite !array_app /= !array_cons !array_nil.
      have -> : s +ₗ - length hvss +ₗ length hvss = s by apply loc_eq; split!; lia.
      have -> : d +ₗ - length hvss +ₗ length hvss = d by apply loc_eq; split!; lia.
      have -> : d +ₗ - length hvss +ₗ length hvsd = d by apply loc_eq; split!; lia.
      rewrite -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
      rewrite -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
      rewrite !right_id_L.
      iDestruct (big_sepM_lookup_acc _ _ s v with "[$]") as "[Hsv Hm]". { by simplify_map_eq. }
      iApply (sim_tgt_rec_Load with "Hsv"). iIntros "Hsv !>" => /=.
      iDestruct ("Hm" with "[$]") as "Hm".
      have [? Hx]: is_Some ((<[s:=v]> (array (s +ₗ - length hvss) hvss) ∪ <[d:=vd]> (array (d +ₗ - length hvss) hvsd)) !! d).
      { apply lookup_union_is_Some. simplify_map_eq. naive_solver. }
      rewrite (big_sepM_delete _ _ _ _ Hx).
      iDestruct "Hm" as "[Hdv Hm]".
      iApply (sim_tgt_rec_Store with "Hdv"). iIntros "Hdv !>" => /=.
      iApply (sim_tgt_rec_LetE). iIntros "!>" => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_; _] _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      destruct (decide (d.1 = s.1 ∧ d.2 ≤ s.2 + length hvss)) as [[??]|Hn]; simplify_eq.
      + rewrite -(insert_union_l _ _ s) insert_union_r. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_union. rewrite delete_notin. 2: { apply array_lookup_None => /=. naive_solver lia. }
        destruct (decide (d = s)); simplify_eq.
        * rewrite delete_insert_delete delete_insert. 2: { apply array_lookup_None => /=. lia. }
          iApply "IH". iFrame. iSplit!. { lia. } { lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. }
          iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s (d +ₗ - length hvss)) //=; [|naive_solver lia].
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite insert_length. lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. naive_solver lia. }
          iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite right_id_L -insert_union_l. iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
          rewrite -insert_union_r_Some //. apply array_lookup_is_Some. split!; naive_solver lia.
      + rewrite delete_union delete_insert. 2: { apply array_lookup_None => /=. lia. }
        rewrite delete_insert_ne. 2: { move => ?. subst. naive_solver lia. }
        rewrite delete_notin. 2: {
          apply array_lookup_None => /=.
          destruct (decide (d.2 ≤ s.2 + length hvss)); naive_solver lia. }
        rewrite -!insert_union_l (big_sepM_delete _ (<[s:=_]>_) s v). 2: by simplify_map_eq.
        iDestruct "Hm" as "[Hsv Hm]".
        rewrite delete_insert. 2: {
          apply lookup_union_None. rewrite !array_lookup_None => /=.
          destruct (decide (d.2 ≤ s.2 + length hvss)); naive_solver lia. }
        iApply "IH". iFrame. iSplit!. { lia. } { lia. }
        { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. naive_solver lia. }
        iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
        rewrite -(insert_union_r _ _ d). 2: { apply array_lookup_None => /=. lia. }
        rewrite -insert_union_l right_id_L -insert_union_r. 2: {
          apply array_lookup_None => /=.
          destruct (decide (d.2 ≤ s.2 + length hvss)); naive_solver lia. }
        iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        iApply (big_sepM_insert_2 with "[Hsv]"); [done|].
        done.
  Qed.

  Definition locle_fn_spec (es : list expr) (POST : (val → iProp Σ) → iProp Σ) : iProp Σ :=
      ∃ l1 l2, ⌜es = [Val (ValLoc l1); Val $ ValLoc l2]⌝ ∗
       POST (λ v, ∃ b, ⌜v = ValBool b⌝ ∗ ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝).

  Lemma sim_memmove Π :
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ rec_fn_spec_hoare Tgt Π "locle" locle_fn_spec -∗
    rec_fn_spec_hoare Tgt Π "memmove" (λ es POST,
      ∃ hvss hvsd d s n, ⌜es = [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n]⌝ ∗
        ⌜n = Z.of_nat (length hvss)⌝ ∗
        ⌜length hvss = length hvsd⌝ ∗
        ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) ∗
        (POST (λ v, ⌜v = 0⌝ ∗ ([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v)))).
  Proof.
    iIntros "#Hmemmove #Hmemcpy #Hlocle". iIntros (es Φ) "HΦ".
    iDestruct "HΦ" as (hvss hvsd d s n -> -> ?) "[Hs HΦ]".
    iApply (sim_gen_expr_bind _ []).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] with "[-]") => /=.
    iApply "Hlocle". iExists _, _. iSplit!. iIntros (? [b [-> Hb]]) => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. destruct b.
    - iApply (sim_memcpy with "[//]"). iFrame. iSplit!. { case_bool_decide; naive_solver. }
      iIntros (?) "[-> ?]". iSplit!. iApply sim_gen_expr_stop. iApply ("HΦ" with "[-]"). by iFrame.
    - iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
      iApply (sim_gen_expr_bind _ [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_] _] with "[-]") => /=.
      iApply (sim_gen_expr_bind _ [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_memcpy with "[//]"). iFrame. iSplit!.
      { rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. }
      { rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. } {
        move => /Hb Hx. symmetry in Hx. rewrite bool_decide_eq_false in Hx.
        simpl. lia.
      }
      iIntros (?) "[-> ?]". iSplit!. iApply sim_gen_expr_stop. iApply ("HΦ" with "[-]"). by iFrame.
  Qed.

  (* This spec is tricky to use since one needs to pick one Π upfront *)
  Lemma sim_locle_spec `{!specGS} Π Φ :
    (∀ f vs h σ, switch_id Tgt _ Π (Some (Incoming, ERCall f vs h)) σ (λ σ', ∃ l1 l2, ⌜σ' = σ⌝ ∗
      ⌜f = "locle"⌝ ∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ ∗ (∀ b,
        ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ ∀ σ,
          switch_id Tgt _ Π (Some (Outgoing, ERReturn (ValBool b) h)) σ (λ σ', ⌜σ' = σ⌝ ∗
            TGT locle_spec @ Π {{ Φ }})))) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>".
    iApply (switch_id_mono with "HC"). iIntros (?). iDestruct 1 as (l1 l2 -> -> ->) "HC" => /=. iFrame.
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>".
    iApply (switch_id_mono with "[HC]"). { iApply ("HC" with "[//]"). }
    simpl. iIntros (?). iDestruct 1 as (->) "HC". iFrame.
  Qed.

  (* The following is not strong enough. Ideally we would write a
  version where we directly pass a function to K, but this would
  require a proof that K is monotonic. *)
  (* Lemma switch_to_id {EV} ts m (Π : option EV → m.(m_state) → iProp Σ) κ σ K C : *)
  (*   switch Π K -∗ *)
  (*   (∀ X, (∀ Y, (∀ σ Π', Y σ Π' -∗ ⌜Π' = Π⌝ ∗ C σ) -∗ X ts m Y) -∗ K κ σ X) -∗ *)
  (*   switch_id ts m Π κ σ C. *)
  (* Proof. *)
  (*   iIntros "Hs Hmono" (??) "[-> [-> HC]]". *)
  (*   iApply "Hs". iApply "Hmono". iIntros (?) "Hmono". *)
  (*   iIntros (??) "?". iApply "HC". by iApply "Hmono". *)
  (* Qed. *)

  (* This spec does not require one to pick Π upfront *)
  Lemma sim_locle_spec2 `{!specGS} Π Φ :
    switch Π (λ κ σ POST,
      ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
    POST Tgt (spec_trans _ unit) (λ σ' Π',
      ∃ l1 l2, ⌜σ' = σ⌝ ∗ ⌜f = "locle"⌝ ∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ ∗
    switch Π' (λ κ σ POST,
      ∃ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ ∗
      ⌜κ = (Some (Outgoing, ERReturn (ValBool b) h))⌝ ∗ ⌜σ = (locle_spec, tt)⌝ ∗
      spec_state ()
      ))) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "Hs !>".
    (* iApply (switch_to_id with "HC"). iIntros (?) "HX". *)
    iIntros (??) "[% [% _]]". subst.
    iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (?????) "HC". subst.
    iApply (sim_gen_expr_intro _ tt with "[Hs]"); simpl; [done..|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>".
    iIntros (??) "[% [% _]]". subst. iApply "HC". iSplit!.
  Qed.

  Lemma sim_locle2 fns Π :
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    switch_link Tgt Π (λ σ0 POST,
      ∃ vs h,
    POST (ERCall "locle" vs h) (spec_trans _ _) (locle_spec, tt) (λ _ Πr,
    switch_link Tgt Πr (λ σ POST,
      ∃ v h', ⌜σ = (locle_spec, tt)⌝ ∗
    POST (ERReturn v h') _ σ0 (λ _ Πx,
      ⌜Πx = Π⌝)))) -∗
    rec_fn_spec_hoare Tgt Π "locle" locle_fn_spec.
  Proof.
    iIntros "#Hfns #Hf HΠ" (es Φ) "HΦ". iDestruct "HΦ" as (l1 l2 ->) "HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iIntros (??) "[% [% Hσ]]". subst. iApply "HΠ". iSplit!. iIntros (??) "[-> HΠi]".
    iApply (fupd_sim_gen with "[-]").
    iMod (mstate_var_alloc unit) as (γ) "?".
    iMod (mstate_var_split γ tt with "[$]") as "[Hγ ?]".
    iModIntro.
    pose (Hspec := SpecGS γ).
    iApply (sim_gen_expr_intro _ tt with "[Hγ]"); simpl; [done..|].
    iApply sim_locle_spec2 => /=. iIntros (??). iDestruct 1 as (????) "HC". subst.
    iApply "HΠi". iSplit!. iIntros (??) "[% [% HΠr]]". simplify_eq/=.
    iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (????) "HC".
    iApply "HΠr". iSplit!. iIntros (??) "[% HΠf]". simplify_eq.
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HΠf". iSplit!. iIntros (??) "[% [% ?]]". simplify_eq. }
    iIntros (???) "!>". iApply "HΠf". iSplit!. iIntros (??[?[??]]). simplify_eq.
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ". iSplit!.
  Qed.

  Lemma sim_main Π :
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    "main" ↪ Some main_rec -∗
    □ rec_fn_spec_hoare Tgt Π "locle" locle_fn_spec -∗
    rec_fn_spec_hoare Tgt Π "main" (λ es POST, ⌜es = []⌝ ∗
      rec_fn_spec_hoare Tgt Π "print" (λ es POST1, ⌜es = [Val 1]⌝ ∗ POST1 (λ _,
        rec_fn_spec_hoare Tgt Π "print" (λ es POST2, ⌜es = [Val 2]⌝ ∗ POST2 (λ _, POST (λ v, ⌜v = 0⌝)))))).
  Proof.
    iIntros "#? #? #? #?". iIntros (es Φ). iDestruct 1 as (->) "HΦ".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [by econs|] => /=. iIntros (?) "Hl".
    destruct ls as [|l []] => //=. 2: by iDestruct!.
    have -> : (0%nat + 0) = 0 by []. have -> : (1%nat + 0) = 1 by []. have -> : (2%nat + 0) = 2 by [].
    iDestruct "Hl" as "[[Hl0 [Hl1 [Hl2 _]]] _]". iModIntro.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [StoreLCtx _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl0"). iIntros "Hl0 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [StoreLCtx _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Store with "Hl1"). iIntros "Hl1 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [_] _] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_memmove); [done..|].
    iExists [ValNum 1; ValNum 2], [ValNum 2; ValNum 0].
    iSplit!. iSplitL "Hl0 Hl1 Hl2".
    { rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
      rewrite !offset_loc_assoc insert_insert.
      iApply (big_sepM_insert_2 with "[Hl0]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl1]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl2]"); [done|].
      done. }
    iIntros (?) "[-> Hl]" => /=. rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
    rewrite !offset_loc_assoc.
    rewrite (big_sepM_delete _ _ (l +ₗ 1)). 2: { by simplify_map_eq. }
    rewrite delete_insert_delete.
    rewrite delete_insert_ne //. 2: apply/loc_eq; split!; lia.
    rewrite delete_insert_ne //. 2: apply/loc_eq; split!; lia.
    rewrite delete_insert //.
    rewrite big_sepM_insert. 2: { rewrite lookup_insert_ne //. apply/loc_eq; split!; lia. }
    rewrite big_sepM_insert. 2: done.
    iDestruct "Hl" as "[Hl1 [Hl2 [Hl0 _]]]".
    iApply sim_tgt_rec_LetE. iModIntro => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl1"). iIntros "Hl1 !>" => /=.

    iApply "HΦ". iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.

    iApply "HΦ". iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_gen_expr_stop => /=. iSplit!. iFrame. by iApply "HΦ".
  Qed.

  Definition main_spec_body : spec rec_event unit void :=
    h' ← TExist _;
    TVis (Outgoing, ERCall "print" [ValNum 1] h');;
    e ← TExist _;
    TVis (Incoming, e);;
    TAssume (if e is ERReturn _ h'' then h' = h'' else false);;
    h' ← TExist _;
    TVis (Outgoing, ERCall "print" [ValNum 2] h');;
    e ← TExist _;
    TVis (Incoming, e);;
    TAssume (if e is ERReturn _ h'' then h' = h'' else false);;
    TUb.

  Lemma sim_main_full Π γσ_s (σ : m_state (spec_trans _ unit)) :
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    "main" ↪ Some main_rec -∗
    "print" ↪ None -∗
    □ rec_fn_spec_hoare Tgt Π "locle" locle_fn_spec -∗
    γσ_s ⤳ σ -∗
    ⌜σ.1 ≡ main_spec_body⌝ -∗
    rec_fn_spec_hoare Tgt Π "main" (λ es POST,
      ⌜es = []⌝ ∗
      □ switch_external Π (λ σ POST,
          ∃ vs h σ_s, γσ_s ⤳ σ_s ∗
        POST (Outgoing, ERCall "print" vs h) (spec_trans _ unit) σ_s (λ _ Π',
        (* TODO: Some nice abstraction for the following? *)
          ∃ e,
        switch Π' (λ κ'' σ_s3 POST,
          ⌜κ'' = Some (Incoming, e)⌝ ∗
        POST Src _ (λ σ_s3' Π_s'',
          ⌜σ_s3' = σ_s3⌝ ∗
        switch Π_s'' (λ κ'' σ'' POST,
          ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ'' = None⌝ ∗
        POST Tgt _ (λ σ' Π',
          ⌜σ' = σ⌝ ∗ γσ_s ⤳ σ'' ∗
        switch Π' (λ κ σ POST,
          ∃ e', ⌜κ = Some (Incoming, e')⌝ ∗
        POST Tgt _ (λ σ' Π',
          ⌜σ' = σ⌝ ∗ ⌜e = e'⌝ ∗ ⌜Π = Π'⌝)))))))) ∗
      POST (λ vr, ∃ σ_s, γσ_s ⤳ σ_s ∗ (∀ Π, σ_s ≈{ spec_trans rec_event () }≈>ₛ Π) ∗ ⌜vr = 0⌝)).
  Proof.
    set (X := (switch_external _) _).
    iIntros "#?#?#?#?#? Hσs". iIntros (??). iDestruct 1 as (?) "[#Hs Hend]".
    iApply (fupd_sim_gen_expr with "[-]").
    iMod (mstate_var_alloc unit) as (γ) "?".
    iMod (mstate_var_split γ σ.2 with "[$]") as "[Hγ ?]".
    iModIntro.
    pose (Hspec := SpecGS γ).

    iApply sim_main; [done..|]. iSplit!.

    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hs". iSplit!. iFrame. iSplit!. iIntros (??) "[-> HC]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    unfold main_spec_body.
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> [% HC]]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); [simpl; done..|].
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> HC]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq/=.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> [? HC]]".
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HC". iSplit!. iIntros (??) "[% [% %]]". simplify_eq. }
    iIntros (?? _) "!>". iApply "HC". iSplit!. iIntros (??[?[??]]). simplify_eq/=.
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ".

    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns'' Hh Ha !>". iIntros (??) "[-> [-> Hσ]]".
    iApply "Hs". iSplit!. iFrame. iSplit!. iIntros (??) "[-> HC]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    unfold main_spec_body.
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> [% HC]]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); [simpl; done..|].
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> HC]".
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq/=.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγ".
    iIntros (??) "[-> [-> ?]]".
    iApply "HC". iSplit!. iIntros (??) "[-> [? HC]]".
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HC". iSplit!. iIntros (??) "[% [% %]]". simplify_eq. }
    iIntros (?? _) "!>". iApply "HC". iSplit!. iIntros (??[?[??]]). simplify_eq/=.
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ". iIntros (? ->).

    iApply ("Hend" with "[-]"). iFrame. iSplit!. iIntros (?).
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); [simpl; done..|].
    iApply sim_src_TUb_end.
  Qed.



  (* (* Writing this spec for main_spec probably does not gain much / if *)
  (* anything compared to reasoning about the spec module directly *) *)
  (* Lemma sim_main_spec Π Φ : *)
  (*   (∃ f vs h, ∀ σ, handle_cont _ Src Π (Some (Incoming, ERCall f vs h)) σ (λ σ', ⌜σ' = σ⌝ ∗ ( *)
  (*     ⌜f = "main"⌝ -∗ ⌜vs = []⌝ -∗ *)
  (*     ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗ *)
  (*     (∃ h', ∀ σ, handle_cont _ Src Π (Some (Outgoing, ERCall "print" [ValNum 1] h')) σ (λ σ', ⌜σ' = σ⌝ ∗ *)
  (*     (∃ e, ∀ σ, handle_cont _ Src Π (Some (Incoming, e)) σ (λ σ', ⌜σ' = σ⌝ ∗ (∀ v', ⌜e = ERReturn v' h'⌝ -∗ *)
  (*     ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗ *)
  (*     (∃ h', ∀ σ, handle_cont _ Src Π (Some (Outgoing, ERCall "print" [ValNum 2] h')) σ (λ σ', ⌜σ' = σ⌝ ∗ *)
  (*     (∃ e, ∀ σ, handle_cont _ Src Π (Some (Incoming, e)) σ (λ σ', ⌜σ' = σ⌝ ∗ (∀ v', ⌜e = ERReturn v' h'⌝ -∗ *)
  (*     ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗ True)))))))))))))))) -∗ *)
  (*   SRC main_spec @ Π {{ Φ }}. *)
  (* Proof. *)
  (*   iIntros "HΦ". iDestruct "HΦ" as (f vs h) "HΦ". *)
  (*   iEval (unfold main_spec). rewrite /TReceive bind_bind. *)
  (*   iApply (sim_src_TExist (_, _, _)). *)
  (*   rewrite bind_bind. setoid_rewrite bind_ret_l. *)
  (*   iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> HΦ]". iSplit; [done|]. *)
  (*   iApply sim_src_TAssume. iIntros (?). *)
  (*   iApply sim_src_TAssume. iIntros (?). simplify_eq. *)
  (*   iDestruct ("HΦ" with "[//] [//]") as "HΦ". *)
  (*   iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> [% HΦ]]". iExists _. iSplit; [done|]. iSplit!. *)
  (*   iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> [% HΦ]]". iSplit; [done|]. *)
  (*   iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> HΦ]". iSplit; [done|]. *)
  (*   iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq. *)
  (*   iDestruct ("HΦ" with "[//]") as "HΦ". *)
  (*   iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> [% HΦ]]". iExists _. iSplit; [done|]. iSplit!. *)
  (*   iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> [% HΦ]]". iSplit; [done|]. *)
  (*   iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> HΦ]". iSplit; [done|]. *)
  (*   iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq. *)
  (*   iDestruct ("HΦ" with "[//]") as "HΦ". *)
  (*   iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ"). *)
  (*   iIntros (?) "[-> HΦ]". iExists _. iSplit; [done|]. iSplit!. *)
  (*   iApply sim_src_TUb_end. *)
  (* Qed. *)
End memmove.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Let m_t := rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()).

  Lemma memmove_sim :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) None -∗
    (MLFRun None, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{m_t,
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=".
    iApply (fupd_sim with "[-]").
    iMod (mstate_var_alloc (m_state (spec_trans rec_event ()))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (m_state m_t)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".
    (* iMod (mstate_var_alloc (list seq_product_case)) as (γs) "Hγs". *)
    (* iMod (mstate_var_alloc (m_state (spec_trans rec_event ()))) as (γσ_locle) "Hγσ_locle". *)
    iMod (mstate_var_alloc unit) as (γs) "?".
    iMod (mstate_var_split γs tt with "[$]") as "[Hγs ?]".
    iModIntro.
    pose (Hspec := SpecGS γs).

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt with "[Hγs] [-]"); [simpl; done..|].
    iEval (unfold main_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_gen_TVis. iIntros ([]) "Hγs". iIntros (??) "[-> [-> _]]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt with "[Hγs] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs".
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply fupd_sim_gen.
    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }
    iModIntro.

    iApply (sim_gen_expr_intro _ [] with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (Π := link_tgt_leftP _ _ _ _).

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply (sim_main_full with "[] [] [] [] [] Hγσ_s"). 1-4: by iApply (rec_fn_intro with "[$]").
    { iIntros "!>". iApply sim_locle2. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). }
      iIntros (??). iDestruct 1 as (?? ->) "HC" => /=.
      iIntros (??????). destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_recv with "[-]"). iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_right with "[-]"). iApply "HC". iSplit!.
      iIntros (??). iDestruct 1 as (?? -> ->) "HC" => /=.
      iIntros (??????). destruct!/=.
      iApply (sim_tgt_link_left_recv with "[-]"). iApply "HC". iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left with "[-]"). by iApply "HC". } { done. }
    iSplit!.
    - iIntros "!>" (??). iDestruct 1 as (???) "[Hγσ_s [-> HC]]" => /=.
      iIntros  (??????). destruct!/=. rewrite !bool_decide_false //.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (->) "HC".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iSplit!. iIntros (??) "[% HC]". simplify_eq.
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iSplit!. iIntros (??). iDestruct 1 as (?? -> ->) "HC".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". destruct!/=.
      iApply (sim_tgt_link_left_recv with "[-]").
      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??). iDestruct 1 as (? ->) "HC".
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left with "[-]").
      iApply "HC". iSplit!.
    - iIntros (?) "[% [Hγσ_s [Hs %]]]". iApply sim_tgt_rec_ReturnExt.
      iIntros (???) "Hfns''' Hh Ha !>".
      iIntros (??) "[-> [-> _]]" => /=. iIntros (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "Hs".
  Qed.

End memmove.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  eapply (sim_adequacy #[dimsumΣ; recΣ]); [eapply _..|].
  iIntros (??) "!>". simpl.
  iApply (fupd_sim with "[-]").
  iMod recgs_alloc as (?) "[?[??]]". iModIntro.
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
