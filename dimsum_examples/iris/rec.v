From dimsum.core.iris Require Export iris expr spec.
From dimsum.examples Require Export rec.
From dimsum.examples.iris Require Export rec_basic.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

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

  Lemma sim_tgt_rec_Waiting fns Π Φ (b : bool) h :
    rec_fn_auth fns -∗
    ((∀ f fn vs h' σ, ⌜fns !! f = Some fn⌝ -∗
         (rec_inv h' -∗
          σ ⤇ₜ λ Π', TGT ReturnExt b (Call (Val (ValFn f)) (Val <$> vs)) [{ Π' }] {{ Φ }}) -∗
        ▷ₒ Π (Some (Incoming, ERCall f vs h')) σ) ∧
      ∀ v h' σ, ⌜b⌝ -∗
          (rec_inv h' -∗
           σ ⤇ₜ λ Π', TGT Val v [{ Π' }] {{ Φ }}) -∗
       ▷ₒ Π (Some (Incoming, ERReturn v h')) σ) -∗
    TGT Waiting b @ h [{ Π }] {{ Φ }}.
  Proof.
    iIntros "#Hfns HΦ".
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' %]". simplify_eq/=.
    iDestruct (rec_fn_auth_agree with "Hfns' Hfns") as %?. subst.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    - iDestruct "HΦ" as "[HΦ _]". iDestruct ("HΦ" with "[//]") as "HΦ".
      iModIntro. iSplit!. iIntros "Htgt". iApply "HΦ".
      iIntros "?". iApply "Htgt"; [done|]. iFrame.
    - iDestruct "HΦ" as "[_ HΦ]". iDestruct ("HΦ" with "[//]") as "HΦ".
      iModIntro. iSplit!. iIntros "Htgt". iApply "HΦ". iIntros "?". iApply "Htgt"; [done|]. iFrame.
  Qed.

  Lemma sim_tgt_rec_ReturnExt v Π Φ (b : bool) :
    (∀ h σ,
      rec_inv h -∗
      (σ ⤇ₜ λ Π', TGT Waiting b @ h [{ Π' }] {{ Φ }}) -∗
      ▷ₒ Π (Some (Outgoing, ERReturn v h)) σ) -∗
    TGT ReturnExt b (Val v) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$]"). iModIntro. iSplit!.
    iIntros "Htgt". iApply "HΦ". iApply "Htgt"; [done|]. by iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_static f (fd_static_vars fn) (subst_l fn.(fd_args) vs fn.(fd_body))) [{ Π }] {{ Φ }}) -∗
    TGT Call (Val (ValFn f)) es [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros (?) "Hfn HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_Call_external f es Π Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ h σ,
      rec_inv h -∗
      (σ ⤇ₜ λ Π', TGT Waiting true @ h [{ Π' }] {{ Φ }}) -∗
      ▷ₒ Π (Some (Outgoing, ERCall f vs h)) σ) -∗
    TGT Call (Val (ValFn f)) es [{ Π }] {{ Φ }}.
  Proof.
    destruct AsVals0. iIntros "Hfn HΦ".
    iApply sim_tgt_expr_step => /=. iIntros (? [e h0 fns0] ?? ? Hp) "[Hfns' Hh]". simplify_eq/=.
    iDestruct (rec_fn_lookup with "[$] [$]") as %?.
    rewrite right_id_L in Hp.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; try naive_solver.
      move => /= ??? e' [_ Heq]. by apply: list_expr_val_inv. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" $! _ with "[$]"). iModIntro. iSplit!.
    iIntros "Htgt". iApply "HΦ". iApply "Htgt"; [done|]. by iFrame.
  Qed.

  Lemma sim_tgt_rec_BinOp Π Φ v1 v2 v3 op :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3) None Π) -∗
    TGT BinOp (Val v1) op (Val v2) [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!. iFrame.
    by iApply sim_gen_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Load Π Φ l v :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v) None Π) -∗
    TGT Load (Val (ValLoc l)) [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ???  Hp) "[Hfns Hh]". simplify_eq/=.
    iDestruct (heapUR_lookup with "[$] [$]") as %?.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iSpecialize ("HΦ" with "[$]").
    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!.
    iFrame. by iApply sim_gen_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_Store Π Φ l v v' :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val v') None Π) -∗
    TGT Store (Val (ValLoc l)) (Val v') [{ Π }] {{ Φ }}.
  Proof.
    iIntros "Hl HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    iDestruct (heapUR_lookup with "[$] [$]") as %?.
    iMod (heapUR_update with "[$] [$]") as "[??]".
    iSpecialize ("HΦ" with "[$]").
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. { by eexists. } iModIntro. iExists None, _. iSplit!.
    iFrame => /=. by iApply sim_gen_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_AllocA e Π Φ vs :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e [{ Π }] {{ e', os', Π',
     ∃ v, ⌜e' = Val v⌝ ∗ ⌜os' = None⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' None Π' }}) -∗
    TGT AllocA vs e [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Hall) "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iMod (heapUR_alloc_list with "Hh") as "[Hh Hb]"; [done|].
    iDestruct (big_sepL2_sep with "Hb") as "[Hd Hl]".
    iSpecialize ("HΦ" with "[Hl]"). {
      iApply (big_sepL2_impl with "Hl"). iIntros "!>" (?????) "?".
      rewrite big_sepM_kmap_intro big_sepM_zero_block.
      iApply (big_sepL_impl with "[$]"). iIntros "!>" (???) "?".
      rewrite /offset_loc. by erewrite heap_alloc_list_offset_zero.
    }

    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!. iFrame => /=.
    iApply (sim_gen_expr_bind _ [FreeACtx _] _ with "[-]") => /=.
    iApply (sim_gen_expr_wand with "HΦ") => /=.
    iIntros (? ? ?) "[% [% [% [Hl HΦ]]]]" => /=. simplify_eq/=.

    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h'' fns'] ?? ? Hp') "[Hfns Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iDestruct (big_sepL2_sep_2 with "Hd Hl") as "Hb".
    iMod (heapUR_free_list with "[$] [Hb]") as (??) "?". 2: {
       iApply (big_sepL2_impl with "Hb").
       iIntros "!>" (?????) "[$ ?]".
       rewrite big_sepS_map big_sepS_dom big_sepM_zero_block.
       iApply (big_sepL_impl with "[$]").
       iIntros "!>" (???) "[% ?]". rewrite /offset_loc.
       erewrite heap_alloc_list_offset_zero => //. iFrame.
    } { apply Forall_lookup_2 => ???. split; [by apply: heap_alloc_list_is_block|by apply:heap_alloc_list_offset_zero]. }
    iModIntro. iSplit!; [done|]. iModIntro. iExists None, _. iSplit!. iFrame => /=.
    by iApply sim_gen_expr_stop2.
  Qed.

  Lemma sim_tgt_rec_LetE Π Φ s v e :
    (▷ₒ TGT (subst s v e) [{ Π }] {{ Φ }}) -∗
    TGT LetE s (Val v) e [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!. iFrame.
  Qed.

  Lemma sim_tgt_rec_If Π Φ (b : bool) e1 e2 :
    (▷ₒ TGT (if b then e1 else e2) [{ Π }] {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 [{ Π }] {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply sim_tgt_expr_step_None => /=. iIntros (? [e' h fns] ?? ? Hp) "[Hfns Hh]". simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. iModIntro. iExists None, _. iSplit!. iFrame.
  Qed.

End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.


  (* TODO: create a version of the target triple where the Π stays unchanged *)
  Lemma sim_memcpy Π Φ d d' s' s n o hvss hvsd :
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    o = 1 ∨ o = -1 →
    d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1)) →
    s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1)) →
    (if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2) →
    "memcpy" ↪ Some memcpy_rec -∗
    ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d' hvss ∪ array s' hvss, l ↦ v) -∗
     Φ (Val 0) None Π) -∗
    TGT Call (Val (ValFn "memcpy")) [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o] [{ Π }] {{ Φ }}.
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
    2: { destruct hvss, hvsd => //. iApply sim_gen_expr_stop2. iSplit!. iApply "HΦ".
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
          iApply ("IH" with "[%] [%] [//] [//] [%] Hm"). { lia. } { rewrite length_insert. done. } { simpl. naive_solver lia. }
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
      rewrite length_app/=. rewrite !length_app/= in Hlen.
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
          iApply ("IH" with "[%] [%] [%] [%] [%] Hm"). { lia. } { rewrite length_insert. lia. }
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

  Lemma sim_memmove hvss hvsd Π Φ d s n :
    n = Z.of_nat (length hvss) →
    length hvss = length hvsd →
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ (∀ l1 l2 Φ,
        (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) None Π) -∗
          TGT Call (Val (ValFn "locle")) [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}) -∗
    ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) -∗
    (([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v) -∗ Φ (Val 0) None Π) -∗
    TGT Call (Val (ValFn "memmove")) [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n] [{ Π }] {{ Φ }}.
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
      iIntros "?". iSplit!. iApply sim_gen_expr_stop2. iApply ("HΦ" with "[$]").
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
      iIntros "?". iSplit!. iApply sim_gen_expr_stop2. iApply ("HΦ" with "[$]").
  Qed.

  Local Canonical Structure spec_mod_lang_unit.
  Lemma sim_locle s fns fns1 Φ l1 l2 Π_s :
    let Π := λ κ P, (∀ σl, (σl ⤇ₜ λ Π, TGT locle_spec [{Π}] {{_, _, _, False}}) -∗
              tgt_link_run_leftP (rec_link_filter fns1 {["locle"]}) Π_s s σl κ P)%I in
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (Val (ValBool b)) None Π) -∗
    TGT Call (Val (ValFn "locle")) [Val (ValLoc l1); Val $ ValLoc l2] [{ Π }] {{ Φ }}.
  Proof.
    iIntros (Π) "#Hfns #Hf HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (? σ') "? Hσ' !>".
    iIntros (σl) "Hσl".
    iIntros (??????). destruct!/=. case_bool_decide => //. rewrite (bool_decide_true (_ ∈ _)) //.
    iApply (sim_tgt_link_recv_right with "[-]"). iApply "Hσl".
    rewrite /locle_spec unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_tgt_TVis with "[-]"). iIntros (?) "Hσl !>". iIntros (?). simplify_eq/=.
    iApply (sim_tgt_link_run_right with "[-]"). iApply "Hσl".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_tgt_TVis with "[-]"). iIntros (?) "Hσl !>".
    iIntros (??????). destruct!/=.
    iApply (sim_tgt_link_recv_left with "[-]"). iApply "Hσ'".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit. { iIntros. iModIntro. iIntros (?). simplify_eq. }
    iIntros (????) "Hσ' !>". iIntros (?). simplify_eq/=.
    iApply (sim_tgt_link_run_left with "[-]"). iApply ("Hσ'" with "[$]").
    iApply (sim_gen_expr_wand1 with "[HΦ]").
    { iApply sim_gen_expr_stop2. by iApply "HΦ". }
    iIntros (??) "HΠ". by iApply "HΠ".
  Qed.

End memmove.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Local Canonical Structure spec_mod_lang_unit.

  Lemma memmove_sim  :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) None -∗
    (MLFRun None, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{
      rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]} rec_trans (spec_trans rec_event ()),
      spec_trans rec_event ()} (main_spec, ()).
  Proof.
    iIntros "[#Hfns Hh] /=". iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    unfold sim_tgtP.
    iApply (sim_gen_expr_elim _ None with "[] [-]"); [simpl; done..|].
    unfold main_spec. rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_src_TVis. iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgtP_intro with "[-]"). iApply sim_gen_stop.
    iApply "Hsrc".
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    rewrite bool_decide_true; [|done].
    iApply sim_gen_expr_stop1. iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_gen_expr_elim _ (Some _) [] with "[] [-]"); [done| by iSplit |] => /=.
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [|by iIntros].
    iIntros (????? Hin) "Htgt !>". iIntros (?). simplify_map_eq.
    iApply (sim_tgt_link_run_left with "[-]").
    iApply fupd_sim_gen.
    iMod (heapUR_alloc_blocks _ (h_blocks h) with "Hh") as "[Hh _]". { set_solver. } iModIntro.
    rewrite right_id_L heap_from_blocks_h_blocks.
    iApply ("Htgt" with "Hh").
    iApply (sim_gen_expr_bind _ [ReturnExtCtx _]).
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
    iApply (sim_gen_expr_wand1 with "[-]"). 2: shelve.
    iApply (sim_memmove [ValNum 1; ValNum 2] [ValNum 2; ValNum 0] with "[] [] [] [Hl0 Hl1 Hl2]").
    { done. } { done. }
    { by iApply (rec_fn_intro with "[$]"). }
    { by iApply (rec_fn_intro with "[$]"). }
    { iIntros "!>" (???) "HΦ".
      iApply sim_locle. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). } 1: done.
      Unshelve. all: shelve_unifiable. 1: exact tt. {
        iIntros (??) "HΦ". iApply "HΦ". iIntros (?) "?".
        by iApply (sim_gen_expr_elim _ None with "[] [-]"); [simpl; done..|].
      }
    }
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
    iIntros (??) "Hh Htgt !>". iIntros (?) "Hlocle".
    iIntros (??????). destruct!/=. rewrite bool_decide_false//.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgtP_intro with "[-]"). iApply sim_gen_stop.
    iApply "Hsrc". iApply sim_src_TAssume. iIntros (?). iApply sim_gen_expr_stop1.
    iIntros (?) "Hsrc". iSplit!. case_match; destruct!/=.
    iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply "Htgt".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [iIntros; iModIntro; by iIntros(?)|].
    iIntros (????) "Htgt !>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_run_left with "[-]").
    iApply ("Htgt" with "[$]").
    iApply sim_gen_expr_stop2 => /=.
    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }
    iIntros (??) "Hh Htgt !>".
    iIntros (??????). destruct!/=. rewrite bool_decide_false//.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!. iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TExist. iApply sim_src_TVis.
    iIntros (?) "Hsrc". iSplit!.
    iApply (sim_tgtP_intro with "[-]"). iApply sim_gen_stop.
    iApply "Hsrc". iApply sim_src_TAssume. iIntros (?). iApply sim_gen_expr_stop1.
    iIntros (?) "Hsrc". iSplit!. case_match; destruct!/=.
    iApply (sim_tgtP_intro with "[-]").
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply "Htgt".
    iApply (sim_tgt_rec_Waiting with "[$]").
    iSplit; [iIntros; iModIntro; by iIntros(?)|].
    iIntros (????) "Htgt !>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_run_left with "[-]").
    iApply ("Htgt" with "[$]").
    iApply sim_gen_expr_stop2 => /=.
    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_gen_expr_stop2 => /=. iSplit!. iFrame.
    iApply sim_tgt_rec_ReturnExt. iIntros (??) "Hh ? !>".
    iIntros (??????). destruct!/=.
    iApply "Hsrc". iApply sim_src_TUb_end.
    Unshelve. exact: tt.
  Qed.
End memmove.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  eapply (sim_adequacy #[dimsumΣ; recΣ]); [apply _..|].
  iIntros (??) "!>". simpl.
  iApply (fupd_sim with "[-]").
  iMod recgs_alloc as (?) "[??]". iModIntro.
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
