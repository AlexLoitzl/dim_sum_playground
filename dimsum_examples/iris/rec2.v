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
  mstate := heap_state;
  mfill := expr_fill;
  mcomp_ectx := flip app;
  mtrans := rec_trans;
  mexpr_rel σ e := st_expr σ = e;
  mstate_interp := rec_state_interp;
|}.
Next Obligation. move => ?????/=. by rewrite expr_fill_app. Qed.

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

  Lemma sim_tgt_rec_ReturnExt v J Φ (b : bool) :
    (∀ K h fns,
      rec_fn_auth fns -∗
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
      ▷ₒ imodhandle (S:=m_state rec_trans) J (Some (Outgoing, ERReturn v h)) (Rec (expr_fill K (Waiting b)) h fns) (λ σ,
         ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
         rec_mapsto_auth (h_heap (st_heap σ)) ∗
         rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e')) -∗
    TGT ReturnExt b (Val v) @ J {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$] [$] [$]"). iModIntro. iSplit!.
    do 2 iModIntro. iApply (imodhandle_mono with "[$]"). iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_end.
  Qed.

  (* TODO: can we somehow get rid of the nopMH requirement? *)
  Lemma sim_tgt_rec_Call_internal f fn es J Φ vs `{!AsVals es vs None} `{!inMH nopMH J} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_static f (fd_static_vars fn) (subst_l (fd_args fn) vs (fd_body fn))) @ J {{ Φ }}) -∗
    TGT Call (Val (ValFn f)) es @ J {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!. iFrame "∗#".
  Qed.

  Lemma sim_tgt_rec_Call_external f es J Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ K h fns,
      rec_fn_auth fns -∗
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
      ▷ₒ imodhandle (S:=m_state rec_trans) J (Some (Outgoing, ERCall f vs h))
        (Rec (expr_fill K (Waiting true)) h fns) (λ σ,
          ∃ e', ⌜st_expr σ = expr_fill K e'⌝ ∗ ⌜st_fns σ = fns⌝ ∗
           rec_mapsto_auth (h_heap (st_heap σ)) ∗
      rec_alloc_auth (dom (h_heap (st_heap σ))) ∗ Φ e')) -∗
    TGT Call (Val (ValFn f)) es @ J {{ Φ }}.
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
    iApply (imodhandle_mono with "[$]"). iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_BinOp J Φ v1 v2 v3 op `{!inMH nopMH J} :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3)) -∗
    TGT BinOp (Val v1) op (Val v2) @ J {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_Load J Φ l v `{!inMH nopMH J} :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v)) -∗
    TGT Load (Val (ValLoc l)) @ J {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_Store J Φ l v v' `{!inMH nopMH J} :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val v')) -∗
    TGT Store (Val (ValLoc l)) (Val v') @ J {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iDestruct (rec_mapsto_lookup with "[$] [$]") as %?.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_mapsto_update with "[$] [$]") as "[??]".
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. { by eexists. } do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!.
    iFrame "∗#" => /=. rewrite dom_alter_L. iFrame. by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_AllocA e J Φ vs `{!inMH nopMH J} :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e @ J {{ e',
     ∃ v, ⌜e' = Val v⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' }}) -∗
    TGT AllocA vs e @ J {{ Φ }}.
  Proof.
    iIntros (Hall) "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_mapsto_alloc_list with "Hh") as "[Hh ?]"; [done|].
    iMod (rec_alloc_alloc_list with "Ha") as "[Ha Has]"; [done..|].
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!.
    iFrame "∗#" => /=.

    iApply (sim_gen_expr_bind _ [FreeACtx _] _ with "[-]") => /=.
    iApply (sim_gen_expr_wand with "HΦ") => /=.
    iIntros (?) "[% [% [Hl HΦ]]]" => /=. simplify_eq/=.
    iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h1 fns1] ??) "[#Hfns1 [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (???). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (rec_alloc_free_list with "Hh Ha [$] [$]") as (??) "[??]".
    iModIntro. iSplit!. { done. } do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!.
    iFrame "∗#" => /=. by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_LetE J Φ s v e `{!inMH nopMH J} :
    (▷ₒ TGT (subst s v e) @ J {{ Φ }}) -∗
    TGT LetE s (Val v) e @ J {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!.
    iFrame "∗#" => /=.
  Qed.

  Lemma sim_tgt_rec_If J Φ (b : bool) e1 e2 `{!inMH nopMH J} :
    (▷ₒ TGT (if b then e1 else e2) @ J {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 @ J {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH). iSplit!.
    iFrame "∗#" => /=.
  Qed.

End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.


  (* TODO: create a version of the target triple where the Π stays unchanged *)
  Lemma sim_memcpy J Φ d d' s' s n o hvss hvsd `{!inMH nopMH J}:
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    o = 1 ∨ o = -1 →
    d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
    s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
    (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
    "memcpy" ↪ Some memcpy_rec -∗
    ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d' hvss ∪ array s' hvss, l ↦ v) -∗
     Φ (Val 0)) -∗
    TGT Call (Val (ValFn "memcpy")) [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] @ J {{ Φ }}.
  Proof.
    iIntros (Hn Hlen Ho Hd' Hs' Hle) "#Hf Hm HΦ".
    iApply sim_gen_expr_ctx. iIntros "#?".
    iRevert (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ".
    iApply ord_loeb; [done|].
    iIntros "!> #IH" (hvss hvsd d d' s s' n Φ Hn Hlen Hd' Hs' Hle) "Hm HΦ". simplify_eq.
    iApply (sim_tgt_rec_Call_internal with "Hf"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] _ with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. case_bool_decide (0 < _).
    2: { destruct hvss, hvsd => //. iApply sim_gen_expr_end. iSplit!. iApply "HΦ".
         by rewrite /array !kmap_empty. }
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
          iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { done. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -insert_union_l -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s ( d+ₗ1)) //=; [|naive_solver lia].
          iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { rewrite insert_length. done. } { simpl. naive_solver lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
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
        iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { done. } { simpl. naive_solver lia. }
        iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
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
          iApply ("IH" with "[%] [%] [%] [%] [%] Hm"). { lia. } { lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s (d +ₗ - length hvss)) //=; [|naive_solver lia].
          iApply ("IH" with "[%] [%] [%] [%] [%] Hm"). { lia. } { rewrite insert_length. lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. naive_solver lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
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
        iApply ("IH" $! hvss hvsd with "[%] [%] [%] [%] [%] Hm"). { lia. } { lia. }
        { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. } { simpl. naive_solver lia. }
        iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
        rewrite -(insert_union_r _ _ d). 2: { apply array_lookup_None => /=. lia. }
        rewrite -insert_union_l right_id_L -insert_union_r. 2: {
          apply array_lookup_None => /=.
          destruct (decide (d.2 ≤ s.2 + length hvss)); naive_solver lia. }
        iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        iApply (big_sepM_insert_2 with "[Hsv]"); [done|].
        done.
  Qed.

  Lemma sim_memmove hvss hvsd J Φ d s n `{!inMH nopMH J}:
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ (∀ l1 l2 Φ,
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b))) -∗
          TGT Call (Val (ValFn "locle")) [Val (ValLoc l1); Val $ ValLoc l2] @ J {{ Φ }}) -∗
    ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v) -∗ Φ (Val 0)) -∗
    TGT Call (Val (ValFn "memmove")) [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] @ J {{ Φ }}.
  Proof.
    iIntros (-> ?) "#Hmemmove #Hmemcpy #Hlocle Hs HΦ".
    iApply (sim_gen_expr_bind _ []).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] with "[-]") => /=.
    iApply "Hlocle". iIntros (b Hb) => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. destruct b.
    - iApply (sim_memcpy with "[//] Hs"). { done. } { done. } { by left. } { by rewrite bool_decide_true. }
      { by rewrite bool_decide_true. } {
        rewrite bool_decide_true // => /Hb Hx. symmetry in Hx. by rewrite bool_decide_eq_true in Hx.
      }
      iIntros "?". iSplit!. iApply sim_gen_expr_end. iApply ("HΦ" with "[$]").
    - iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
      iApply (sim_gen_expr_bind _ [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_gen_expr_bind _ [CallCtx _ [_] _] with "[-]") => /=.
      iApply (sim_gen_expr_bind _ [BinOpRCtx _ _] with "[-]") => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
      iApply (sim_memcpy with "[//] Hs"). { done. } { done. } { by right. }
      { rewrite bool_decide_false; [|done]. rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. }
      { rewrite bool_decide_false; [|done]. rewrite offset_loc_assoc.
        have -> : (length hvss + -1 + (- length hvss + 1)) = 0 by lia.
        rewrite offset_loc_0. done. } {
        rewrite bool_decide_false // => /Hb Hx. symmetry in Hx. rewrite bool_decide_eq_false in Hx.
        simpl. lia.
      }
      iIntros "?". iSplit!. iApply sim_gen_expr_end. iApply ("HΦ" with "[$]").
  Qed.

  Local Canonical Structure spec_mod_lang_unit.
  Program Definition locleMH m1 : iModHandler Σ (m_state m1) rec_event := {|
    imodhandle κ σ C := ∀ fns1 Π_s s,
      let Π := (link_tgt_leftP (m2:=spec_trans _ _) (rec_link_filter fns1 {["locle"]}) Π_s s (locle_spec, tt)) in
        (∀ σ', C σ' -∗ σ' ≈{ m1 }≈>ₜ Π) -∗ Π κ σ
  |}%I.
  Next Obligation.
    simpl. iIntros (?????) "HP HC". iIntros (???) "Hw". iApply "HP". iIntros (?) "?".
    iApply "Hw". by iApply "HC".
  Qed.

  Lemma sim_locle fns Φ l1 l2 J `{!inMH (locleMH _) J}:
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b))) -∗
    TGT Call (Val (ValFn "locle")) [Val (ValLoc l1); Val $ ValLoc l2] @ J {{ Φ }}.
  Proof.
    iIntros "#Hfns #Hf HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iApply (inMH_apply (locleMH _)). iIntros (???) "Hσ".
    iIntros (??????). destruct!/=. case_bool_decide => //. rewrite (bool_decide_true (_ ∈ _)) //.
    iApply (sim_tgt_link_right_recv with "[-]").
    iApply (sim_gen_expr_intro _ tt _ None); simpl; [done..|].
    unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (?) "!>". iIntros "_" (?). simplify_eq/=.
    iApply (sim_tgt_link_right with "[-]").
    iApply (sim_gen_expr_intro _ tt _ None); simpl; [done..|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros (?) "!> _".
    iIntros (??????). destruct!/=.
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iIntros (?). simplify_eq. }
    iIntros (???) "!>". iIntros (?). iApply (sim_tgt_link_left with "[-]"). destruct_all unit.
    iApply "Hσ". simplify_eq/=. iExists _. iFrame. iSplit!. by iApply "HΦ".
  Qed.

End memmove.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Local Canonical Structure spec_mod_lang_unit.

  Let m_t := rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()).

  Lemma memmove_sim
    `{!mstateG Σ (m_state m_t)}
    `{!mstateG Σ (option rec_event)}
    `{!mstateG Σ (m_state (spec_trans rec_event unit))} :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) None -∗
    (MLFRun None, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{m_t,
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[#Hfns [Hh Ha]] /=".
    iApply (fupd_sim with "[-]").
    iMod (mstate_var_alloc (S := m_state (spec_trans rec_event ()))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (S := m_state m_t)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (S := option rec_event)) as (γκ) "Hγκ".
    iModIntro.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply (sim_gen_expr_wand _ _ _ _ _ (λ _, False%I) with "[-] []"); [|by iIntros].
    iEval (unfold main_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_gen_TVis. iIntros ([]) "HC".
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "HC". iSplit!.
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    rewrite bool_decide_true; [|done].
    iApply sim_gen_expr_None. iIntros (???) "_ Hs". simplify_eq/=.
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply fupd_sim_gen.
    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }
    iModIntro.

    iApply (sim_gen_expr_intro _ [] _ None with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (J := directMH Tgt _).

    have MHnop : inMH nopMH J. {
      unfold inMH. iIntros "!>" (???) "HJ Hσ".
      iDestruct "HJ" as (->) "C" => /=.
      iIntros (?) "Hγσ_s ??". iApply sim_gen_stop.
      iIntros (??) "??".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγσ_t".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγκ".
      iSplit!.
      iApply (sim_tgt_constP_intro_weak with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
      iApply (sim_tgt_link_left with "[-]"). by iApply "Hσ".
    }

    have MHlocle : inMH (locleMH rec_trans) J. {
      unfold inMH. iIntros "!>" (???) "HJ Hσ".
      by iApply "HJ".
    }

    set Pκ : (option rec_event → m_state rec_trans → (m_state m_t → iProp Σ) → iProp Σ) := (λ κ σ C,
        ⌜κ = None⌝ ∗ C (MLFRun (Some SPLeft), [None], σ, (locle_spec, ())) ∨ (
        ∃ vs h, ⌜κ = Some (Outgoing, ERCall "print" vs h)⌝ ∗ C (MLFRun None, [Some SPLeft; None], σ, (locle_spec, ()))) ∨
        (∃ v h, ⌜κ = Some (Outgoing, ERReturn v h)⌝ ∗ C (MLFRun None, [], σ, (locle_spec, ()))))%I.

    eassert (inMH (sim_tgtMH γσ_t γσ_s γκ _ Pκ _ _) J) as MHsrc. {
      unfold inMH. iIntros "!>" (???) "HJ Hσ".
      iDestruct ("HJ" with "Hσ") as "[[-> Hs]|[(%&%&->&Hs)|(%&%&->&Hs)]]" => /=.
        + done.
        + iIntros (??????). destruct!/=. rewrite bool_decide_false//.
        + iIntros (??????). destruct!/=. done.
    }

    clearbody J.

    (* iApply (sim_gen_expr_handler_wand _ ( *)
    (*   nopMH ∪ locleMH rec_trans ∪ sim_tgtMH γσ_t γσ_s γκ _ Pκ _ _) with "[-]"); last first. { *)
    (*   iIntros "!>" (???) "[[HJ|HJ]|HJ] Hσ". *)
    (*   - iDestruct "HJ" as (->) "C" => /=. *)
    (*     iIntros (?) "Hγσ_s ??". iApply sim_gen_stop. *)
    (*     iIntros (??) "??". *)
    (*     iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγσ_t". *)
    (*     iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγκ". *)
    (*     iSplit!. *)
    (*     iApply (sim_tgt_constP_intro_weak with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|]. *)
    (*     iApply (sim_tgt_link_left with "[-]"). by iApply "Hσ". *)
    (*   - by iApply "HJ". *)
    (*   - iDestruct ("HJ" with "Hσ") as "[[-> Hs]|[(%&%&->&Hs)|(%&%&->&Hs)]]" => /=. *)
    (*     + done. *)
    (*     + iIntros (??????). destruct!/=. rewrite bool_decide_false//. *)
    (*     + iIntros (??????). destruct!/=. done. *)
    (* } *)
    (* set (J := nopMH ∪ _ ∪ _). *)

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply sim_tgt_rec_Call_internal. 2: { by iApply (rec_fn_intro with "[$]"). } { done. }
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
    iApply (sim_memmove [ValNum 1; ValNum 2] [ValNum 2; ValNum 0] with "[] [] [] [Hl0 Hl1 Hl2]").
    { done. } { done. }
    { by iApply (rec_fn_intro with "[$]"). }
    { by iApply (rec_fn_intro with "[$]"). }
    { iIntros "!>" (???) "HΦ".
      iApply sim_locle. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). } 1: done. }
    { rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
      rewrite !offset_loc_assoc insert_insert.
      iApply (big_sepM_insert_2 with "[Hl0]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl1]"); [done|].
      iApply (big_sepM_insert_2 with "[Hl2]"); [done|].
      done. }
    iIntros "Hl" => /=. rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
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
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }

    iIntros (???) "Hfns' Hh Ha !>". iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)).
    iIntros "HC". iRight. iLeft. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iExists _. iSplit; [iPureIntro; eassumption|]. iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]) "Hs".
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]) "Hs".
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!.
    iApply sim_src_TAssume. iIntros (?). iApply sim_gen_expr_None => /=. iIntros (???) "_ Hs".
    case_match; destruct!/=.
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply sim_tgt_rec_Waiting_raw.
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply "HC". iSplit!. iFrame.

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }

    iIntros (???) "Hfns'' Hh Ha !>". iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)).
    iIntros "HC". iRight. iLeft. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iExists _. iSplit; [iPureIntro; eassumption|]. iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]) "Hs".
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]) "Hs".
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!.
    iApply sim_src_TAssume. iIntros (?). iApply sim_gen_expr_None => /=. iIntros (???) "_ Hs".
    case_match; destruct!/=.
    iApply (sim_src_constP_elim with "[Hγσ_t] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_t Hγκ". iSplit!.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply sim_tgt_rec_Waiting_raw.
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply "HC". iSplit!. iFrame.

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_gen_expr_end => /=. iSplit!. iFrame.
    iApply sim_tgt_rec_ReturnExt. iIntros (???) "Hfns''' Hh Ha !>".
    iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)). iIntros "HC". iRight. iRight. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iExists _. iSplit; [done|]. iSplit!.
    iApply sim_src_TUb_end.
  Qed.
End memmove.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  eapply (sim_adequacy #[dimsumΣ; recΣ;
       mstateΣ (m_state (rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_trans) (spec_trans rec_event ())));
       mstateΣ (m_state (spec_trans rec_event ()));
       mstateΣ (option rec_event)]); [eapply _..|].
  iIntros (??) "!>". simpl.
  iApply (fupd_sim with "[-]").
  iMod recgs_alloc as (?) "[?[??]]". iModIntro.
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
