From dimsum.core.iris Require Export iris expr2 spec2.
From dimsum.examples Require Export rec.
From dimsum.examples.iris Require Export rec_basic.
From dimsum.examples Require Import memmove.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

Definition letstar {A B} (t : A → B) : A → B := t.

Notation "'let*' x , .. , z := t 'in' f" :=
  (letstar t (fun x => .. (fun z => f) ..))
    (at level 200, x closed binder, z closed binder) : stdpp_scope.
Notation "'let*' := t 'in' f" := (t f) (only parsing, at level 200) : stdpp_scope.


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

Definition rec_fn_spec `{!dimsumGS Σ} `{!recGS Σ} (ts : tgt_src) (Π : option rec_event → _ → iProp Σ)
  (f : string) (C : list expr → (val → iProp Σ) → iProp Σ) : iProp Σ :=
  (∀ es Φ, C es (λ v, Φ (Val v)) -∗ TGT Call (Val (ValFn f)) es @ Π {{ Φ }}).

Definition rec_fn_spec_hoare `{!dimsumGS Σ} `{!recGS Σ} (ts : tgt_src) (Π : option rec_event → _ → iProp Σ)
  (f : string) (pre : list expr → ((val → iProp Σ) → iProp Σ) → iProp Σ) : iProp Σ :=
  rec_fn_spec ts Π f (λ es Φ, pre es (λ post, (∀ v', post v' -∗ Φ v')))%I.

Section fn_spec.
  Context `{!dimsumGS Σ} `{!recGS Σ}.
  Lemma rec_fn_spec_ctx ts Π f C :
    (ord_later_ctx -∗ rec_fn_spec ts Π f C) -∗
    rec_fn_spec ts Π f C.
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
      ▷ₒ handle_cont rec_trans Tgt Π (Some (Outgoing, ERReturn v h)) (Rec (expr_fill K (Waiting b)) h fns) (λ σ,
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
    do 2 iModIntro. iApply (handle_cont_mono with "HΦ"). iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_end.
  Qed.

  (* TODO: can we somehow get rid of the nopMH requirement? *)
  Lemma sim_tgt_rec_Call_internal f fn es Π Φ vs `{!AsVals es vs None} `{!inMH _ Tgt nopMH Π} :
    length vs = length (fd_args fn) →
    f ↪ Some fn -∗
    (▷ₒ TGT AllocA fn.(fd_vars) (subst_static f (fd_static_vars fn) (subst_l (fd_args fn) vs (fd_body fn))) @ Π {{ Φ }}) -∗
    TGT Call (Val (ValFn f)) es @ Π {{ Φ }}.
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
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!. iFrame "∗#".
  Qed.

  Lemma sim_tgt_rec_Call_external f es Π Φ vs `{!AsVals es vs None} :
    f ↪ None -∗
    (∀ K h fns,
      rec_fn_auth fns -∗
      rec_mapsto_auth (h_heap h) -∗
      rec_alloc_auth (dom (h_heap h)) -∗
      ▷ₒ handle_cont rec_trans Tgt Π (Some (Outgoing, ERCall f vs h))
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
    iApply (handle_cont_mono with "HΦ"). iIntros (?) "[% [% [% [?[??]]]]]".
    iSplit!; [done|]. iFrame. subst. iFrame "#". by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_BinOp Π Φ v1 v2 v3 op `{!inMH _ Tgt nopMH Π} :
    eval_binop op v1 v2 = Some v3 →
    (▷ₒ Φ (Val v3)) -∗
    TGT BinOp (Val v1) op (Val v2) @ Π {{ Φ }}.
  Proof.
    iIntros (Hop) "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([e h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_Load Π Φ l v `{!inMH _ Tgt nopMH Π} :
    l ↦ v -∗
    (l ↦ v -∗ ▷ₒ Φ (Val v)) -∗
    TGT Load (Val (ValLoc l)) @ Π {{ Φ }}.
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
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!. iFrame "∗#".
    by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_Store Π Φ l v v' `{!inMH _ Tgt nopMH Π} :
    l ↦ v -∗
    (l ↦ v' -∗ ▷ₒ Φ (Val v')) -∗
    TGT Store (Val (ValLoc l)) (Val v') @ Π {{ Φ }}.
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
    iModIntro. iSplit!. { by eexists. } do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!.
    iFrame "∗#" => /=. rewrite dom_alter_L. iFrame. by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_AllocA e Π Φ vs `{!inMH _ Tgt nopMH Π} :
    Forall (λ z, 0 < z) vs.*2 →
    (∀ ls, ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, (l +ₗ o) ↦ 0) -∗
     ▷ₒ TGT subst_l vs.*1 (ValLoc <$> ls) e @ Π {{ e',
     ∃ v, ⌜e' = Val v⌝ ∗ ([∗ list] l;n∈ls; vs.*2, [∗ list] o∈seqZ 0 n, ∃ v, (l +ₗ o) ↦ v) ∗ Φ e' }}) -∗
    TGT AllocA vs e @ Π {{ Φ }}.
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
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!.
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
    iModIntro. iSplit!. { done. } do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!.
    iFrame "∗#" => /=. by iApply sim_gen_expr_end.
  Qed.

  Lemma sim_tgt_rec_LetE Π Φ s v e `{!inMH _ Tgt nopMH Π} :
    (▷ₒ TGT (subst s v e) @ Π {{ Φ }}) -∗
    TGT LetE s (Val v) e @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!.
    iFrame "∗#" => /=.
  Qed.

  Lemma sim_tgt_rec_If Π Φ (b : bool) e1 e2 `{!inMH _ Tgt nopMH Π} :
    (▷ₒ TGT (if b then e1 else e2) @ Π {{ Φ }}) -∗
    TGT If (Val (ValBool b)) e1 e2 @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply (sim_gen_expr_steps with "[-]") => /=.
    iIntros ([? h0 fns0] ??) "[#Hfns [Hh Ha]]". simplify_eq/=.
    iApply (sim_tgt_step_end with "[-]"). iIntros (?? Hp). simplify_eq/=.
    exploit prim_step_inv_head; [done|..].
    { apply sub_redexes_are_values_item; case; naive_solver. }
    { done. }
    move => [? [Hstep ?]]. inv Hstep.
    iModIntro. iSplit!. do 2 iModIntro. iApply (inMH_apply nopMH with "[-]"). iSplit!.
    iFrame "∗#" => /=.
  Qed.

End lifting.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_memcpy Π `{!inMH _ Tgt nopMH Π}:
    "memcpy" ↪ Some memcpy_rec -∗
    rec_fn_spec Tgt Π "memcpy" (λ es Φ,
      ∃ d s n o d' s' hvss hvsd, ⌜es = [Val $ ValLoc d; Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o]⌝ ∗
      ⌜n = Z.of_nat (length hvss)⌝ ∗
      ⌜length hvss = length hvsd⌝ ∗
      ⌜o = 1 ∨ o = -1⌝ ∗
      ⌜d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1))⌝ ∗
      ⌜s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1))⌝ ∗
      ⌜(if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2)⌝ ∗
      ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) ∗
      (([∗ map] l↦v∈array d' hvss ∪ array s' hvss, l ↦ v) -∗ Φ 0)).
  Proof.
    iIntros "#Hf". iApply rec_fn_spec_ctx. iIntros "#?".
    iApply ord_loeb; [done|]. iIntros "!> #IH". iIntros (es Φ) "HΦ".
    iDestruct "HΦ" as (d s n o d' s' hvss hvsd ? Hn Hlen Ho Hd' Hs' Hle) "[Hm HΦ]"; simplify_eq/=.
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
          iApply "IH". iFrame. iSplit!. { lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -insert_union_l -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s ( d+ₗ1)) //=; [|naive_solver lia].
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite insert_length. done. } { simpl. naive_solver lia. }
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
        iApply "IH". iFrame. iSplit!. { lia. } { simpl. naive_solver lia. }
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
          iApply "IH". iFrame. iSplit!. { lia. } { lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. }
          iIntros "?". iSplit!. iApply ("HΦ" with "[-]").
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s (d +ₗ - length hvss)) //=; [|naive_solver lia].
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite insert_length. lia. }
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
        iApply "IH". iFrame. iSplit!. { lia. } { lia. }
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

  Definition locle_fn_spec (es : list expr) (Φ : val → iProp Σ) : iProp Σ :=
      ∃ l1 l2, ⌜es = [Val (ValLoc l1); Val $ ValLoc l2]⌝ ∗
       (∀ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ Φ (ValBool b)).

  Lemma sim_memmove Π `{!inMH _ Tgt nopMH Π}:
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ rec_fn_spec Tgt Π "locle" locle_fn_spec -∗
    rec_fn_spec Tgt Π "memmove" (λ es Φ,
      ∃ hvss hvsd d s n, ⌜es = [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n]⌝ ∗
        ⌜n = Z.of_nat (length hvss)⌝ ∗
        ⌜length hvss = length hvsd⌝ ∗
        ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) ∗
        (([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v) -∗ Φ 0)).
  Proof.
    iIntros "#Hmemmove #Hmemcpy #Hlocle". iIntros (es Φ) "HΦ".
    iDestruct "HΦ" as (hvss hvsd d s n -> -> ?) "[Hs HΦ]".
    iApply (sim_gen_expr_bind _ []).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] with "[-]") => /=.
    iApply "Hlocle". iExists _, _. iSplit!. iIntros (b Hb) => /=.
    iApply sim_tgt_rec_If. iModIntro => /=. destruct b.
    - iApply (sim_memcpy with "[//]"). iFrame. iSplit!. { case_bool_decide; naive_solver. }
      iIntros "?". iSplit!. iApply sim_gen_expr_end. iApply ("HΦ" with "[$]").
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
      iIntros "?". iSplit!. iApply sim_gen_expr_end. iApply ("HΦ" with "[$]").
  Qed.

  Local Canonical Structure spec_mod_lang_unit.
  (* This spec is tricky to use since one needs to pick one Π upfront *)
  Lemma sim_locle_spec Π Φ :
    (∀ f vs h σ, handle_cont _ Tgt Π (Some (Incoming, ERCall f vs h)) σ (λ σ', ∃ l1 l2, ⌜σ' = σ⌝ ∗
      ⌜f = "locle"⌝ ∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ ∗ (∀ b,
        ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ ∀ σ,
          handle_cont _ Tgt Π (Some (Outgoing, ERReturn (ValBool b) h)) σ (λ σ', ⌜σ' = σ⌝ ∗
            TGT locle_spec @ Π {{ Φ }})))) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    iApply (handle_cont_mono with "HC"). iIntros (?). iDestruct 1 as (l1 l2 -> -> ->) "HC" => /=. iSplit; [done|].
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    iApply (handle_cont_mono with "[HC]"). { iApply ("HC" with "[//]"). }
    simpl. iIntros (?). iDestruct 1 as (->) "HC". iSplit; [done|].
    done.
  Qed.

  (* This spec does not require one to pick Π upfront, but it has the
  downside that it is written in extreme continuation passing style *)
  Lemma sim_locle_spec2 Π Φ :
      (∀ f vs h σ C,
        (∀ l1 l2 σ' Π' Φ',
        ⌜σ' = σ⌝ -∗ ⌜f = "locle"⌝ -∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ -∗
         (∀ b C', ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗
         handle_cont (spec_trans _ _) Tgt Π' (Some (Outgoing, ERReturn (ValBool b) h)) (locle_spec, tt) C') -∗
        TGT σ'.1 @ Π' {{ Φ' }}) -∗
      handle_cont (spec_trans _ _) Tgt Π (Some (Incoming, ERCall f vs h)) σ C) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    iApply "HC". iIntros (????? -> -> ->) "HC". simpl.
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    by iApply "HC".
  Qed.

(*
  Definition imodhandle_spec {EV S} (Π : iModHandler Σ S EV)
    (C : option EV → S → (S → iProp Σ) → iProp Σ) : iProp Σ :=
    ∀ κ σ Φ, C κ σ Φ -∗ imodhandle Π κ σ Φ.

  Definition sim_gen_expr_spec {EV} {Λ : mod_lang _ _} (ts : tgt_src)
    (C : (option EV → _ → _) → mexpr Λ → option (mstate Λ) → (mexpr Λ → iProp Σ) → iProp Σ) : iProp Σ :=
    ∀ Π e os Φ, C Π e os Φ -∗ sim_gen_expr ts Π e os Φ.

  (* Maybe a bit less extreme continuation passing style? *)
  Lemma sim_locle_spec3 Π Φ :
    imodhandle_spec Π (λ κ σ _, ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
      sim_gen_expr_spec Tgt (λ Π' σ' os _, ∃ l1 l2,
      ⌜σ' = σ.1⌝ ∗ ⌜os = None⌝ ∗ ⌜f = "locle"⌝ ∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ ∗
        imodhandle_spec Π' (λ κ σ _, ∃ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ ∗
        ⌜κ = Some (Outgoing, ERReturn (ValBool b) h)⌝ ∗ ⌜σ = (locle_spec, tt)⌝))) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    iApply "HC". iSplit!. iIntros (????). iDestruct 1 as (?? -> -> -> ->) "HC".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>".
    rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>".
    rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "!>".
    iApply "HC". iSplit!.
  Qed.
*)

  Program Definition locleMH m1 : iModHandler Σ (m_state m1) rec_event := {|
    imodhandle κ σ C := ∀ fns1 Π_s s,
      let Π := (link_tgt_leftP (m2:=spec_trans _ _) (rec_link_filter fns1 {["locle"]}) Π_s s (locle_spec, tt)) in
        (∀ σ', C σ' -∗ σ' ≈{ m1 }≈>ₜ Π) -∗ Π κ σ
  |}%I.
  Next Obligation.
    simpl. iIntros (?????) "HP HC". iIntros (???) "Hw". iApply "HP". iIntros (?) "?".
    iApply "Hw". by iApply "HC".
  Qed.

  (* Program Definition locleMH m1 : iModHandler Σ (m_state m1) rec_event := {| *)
  (*   imodhandle κ σ C := ∀ fns1 Π_s γ_s γσ_locle (s : list seq_product_case),  *)
  (*          γ_s ⤳ s -∗ γσ_locle ⤳ (locle_spec, tt) -∗ *)
  (*     let Π := (link_tgt_left_constP (m2:=spec_trans _ unit) (rec_link_filter fns1 {["locle"]}) Π_s γ_s γσ_locle) in *)
  (*       (∀ σ', C σ' -∗ σ' ≈{ m1 }≈>ₜ Π) -∗ Π κ σ *)
  (* |}%I. *)
  (* Next Obligation. *)
  (*   simpl. iIntros (?????) "HP HC". iIntros (?????) "?? Hw". iApply ("HP" with "[$] [$]"). iIntros (?) "?". *)
  (*   iApply "Hw". by iApply "HC". *)
  (* Qed. *)



  Lemma sim_locle fns Π `{!inMH _ Tgt (locleMH _) Π}:
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    rec_fn_spec Tgt Π "locle" locle_fn_spec.
  Proof.
    iIntros "#Hfns #Hf" (es Φ) "HΦ". iDestruct "HΦ" as (l1 l2 ->) "HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iApply (inMH_apply (locleMH _)). iIntros (???) "Hσ".
    iIntros (??????). destruct!/=. case_bool_decide => //. rewrite (bool_decide_true (_ ∈ _)) //.
    iApply (sim_tgt_link_right_recv with "[-]").
    iApply (sim_gen_expr_intro _ tt _ None); simpl; [done..|].
    (* iApply sim_locle_spec => /=. iIntros (????) "Hc". iIntros (?). simplify_eq/=. *)
    unfold locle_spec at 2. rewrite unfold_forever -/locle_spec.
    rewrite /TReceive bind_bind bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (?) "!>". simpl. iIntros "_" (?). simplify_eq/=.
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


  Definition locleMH1 m1 Π Πi : iModHandler Σ (m_state m1) rec_event :=
    switchMH Π (λ κ σ C, ∃ vs h, ⌜κ = Some (Outgoing, ERCall "locle" vs h)⌝ ∗
      C Tgt (spec_trans _ unit) (locle_spec, tt) Πi)%I.

  Definition locleMH2 {S} Πi Πr : iModHandler Σ (m_state (spec_trans _ S)) rec_event :=
    switchMH Πi (λ κ σ C, ∃ f vs h, ⌜κ = Some (Incoming, ERCall f vs h)⌝ ∗
      C Tgt (spec_trans _ S) σ Πr)%I.

  Definition switch_spec {S EV} (Π : option EV → S → iProp Σ)
    (K : option EV → S → (tgt_src → ∀ m : mod_trans EV, _ →_ → iProp Σ) → iProp Σ) : iProp Σ :=
    (∀ κ σ, K κ σ (λ ts' m' σ' PΠ', ∀ Π', PΠ' Π' -∗ σ' ≈{ ts', m' }≈> Π') -∗  Π κ σ).

  Lemma sim_locle2 fns Π :
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    switch_spec Π (λ κ σ0 C, ∃ vs h, ⌜κ = Some (Outgoing, ERCall "locle" vs h)⌝ ∗
      C Tgt (spec_trans _ _) (locle_spec, tt) (λ Πi,
       switch_spec Πi (λ κ' σ C, ∃ e, ⌜κ' = Some (Incoming, e)⌝ ∗
         (⌜e = ERCall "locle" vs h⌝ -∗ C Tgt _ σ (λ Πr,
          switch_spec Πr (λ κ'' σ C, ∃ v h', ⌜κ'' = Some (Outgoing, ERReturn v h')⌝ ∗ ⌜σ = (locle_spec, tt)⌝ ∗
              C Tgt _ σ0 (λ Πf,
               (switch_spec Πf (λ κ σ C, ∃ e, ⌜κ = Some (Incoming, e)⌝ ∗
                     (⌜e = ERReturn v h'⌝ -∗ C Tgt _ σ (λ Πx, ⌜Πx = Π⌝))))
      ))))))) -∗
    rec_fn_spec Tgt Π "locle" locle_fn_spec.
  Proof.
    iIntros "#Hfns #Hf HΠ" (es Φ) "HΦ". iDestruct "HΦ" as (l1 l2 ->) "HΦ".
    iApply (sim_tgt_rec_Call_external with "[$]"). iIntros (???) "#??? !>".
    iIntros "Hσ". iApply "HΠ". iSplit!. iIntros (?) "HΠi".
    iApply (sim_gen_expr_intro _ tt _ None); simpl; [done..|].
    (* iApply sim_locle_spec2 => /=. iIntros (?????) "Hc _". iIntros (?). simplify_eq/=. *)
    iApply sim_locle_spec2 => /=. iIntros (?????) "Hc".
    iIntros "_". iApply "HΠi". iSplit!. iIntros (??) "HΠr". simplify_eq/=.
    iApply (sim_gen_expr_intro _ tt _ None); simpl; [done..|].
    iApply "Hc"; [done..|].
    iIntros (???). iIntros "_". iApply "HΠr". iSplit!. iIntros (?) "HΠf".
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HΠf". iSplit!. iIntros (?). simplify_eq. }
    iIntros (???) "!>". iApply "HΠf". iSplit!. iIntros (???). simplify_eq.
    iApply "Hσ". simplify_eq/=. iSplit!. iFrame. by iApply "HΦ".
    (* iApply "Hσ". iSplit!. iFrame. *)
    (* iApply "HC". iIntros (?) "HC". *)
    (* iIntros (??????). destruct!/=. *)
    (* (* iApply (sim_tgt_link_left_recv with "[-]"). *) *)
    (* iApply sim_tgt_rec_Waiting_raw. *)
    (* iSplit. { iIntros. iModIntro. iApply "HC". iIntros (? ?). simplify_eq. } *)
    (* iIntros (???) "!>". iApply "HC". iIntros (?). *)
    (* iApply "Hσ". simplify_eq/=. *)
(* iExists _. iFrame. iSplit!. by iApply "HΦ". *)
  Qed.

(*
possible specs:

only pre:
    rec_fn_spec Tgt Π "main" (λ es Φ,
      ⌜es = []⌝ ∗
      rec_fn_spec Tgt Π "print" (λ es Φ1, ⌜es = [Val 1]⌝ ∗ (∀ v',
        rec_fn_spec Tgt Π "print" (λ es Φ2, ⌜es = [Val 2]⌝ ∗ (∀ v', Φ 0 -∗ Φ2 v')) -∗
      Φ1 v'))).

    rec_fn_spec Tgt Π "main" (λ Φ, Φ []) (λ Φ,
      rec_fn_spec Tgt Π "print" (λ Φ, Φ [Val 1]) (λ Φ1, ∀ v',
        rec_fn_spec Tgt Π "print" (λ Φ, Φ [Val 2]) (λ Φ2, ∀ v', Φ 0 -∗ Φ2 v') -∗
      Φ1 v')).

Hoare triple spec:
    ∀ Φ,
      rec_fn_spec Tgt Π "main" (λ es, ⌜es = []⌝ ∗
       rec_fn_spec Tgt Π "print" (λ es, ⌜es = [Val 1]⌝) (λ _,
        rec_fn_spec Tgt Π "print" (λ es, ⌜es = [Val 2]⌝) (λ _, Φ 0))) Φ
*)


  Lemma sim_main Π `{!inMH _ Tgt nopMH Π}:
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    "main" ↪ Some main_rec -∗
    □ rec_fn_spec Tgt Π "locle" locle_fn_spec -∗
    rec_fn_spec Tgt Π "main" (λ es Φ, ⌜es = []⌝ ∗
      rec_fn_spec_hoare Tgt Π "print" (λ es C, ⌜es = [Val 1]⌝ ∗ C (λ _,
        rec_fn_spec_hoare Tgt Π "print" (λ es C, ⌜es = [Val 2]⌝ ∗ C (λ _, Φ 0))))).
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

    iApply "HΦ". iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.

    iApply "HΦ". iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_gen_expr_end => /=. iSplit!. iFrame.
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


  Lemma sim_main_full Π γσ_s (σ : m_state (spec_trans _ unit)) `{!inMH _ Tgt nopMH Π}:
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    "main" ↪ Some main_rec -∗
    "print" ↪ None -∗
    □ rec_fn_spec Tgt Π "locle" locle_fn_spec -∗
    γσ_s ⤳ σ -∗
    ⌜σ.1 ≡ main_spec_body⌝ -∗
    let* es, Φ := rec_fn_spec Tgt Π "main" in
    ⌜es = []⌝ ∗
      □ (let* κ,σ,C := switch_spec Π in
         ∃ vs h σ_s, ⌜κ = Some (Outgoing, ERCall "print" vs h)⌝ ∗ γσ_s ⤳ σ_s ∗
         let* Π_s := C Src (spec_trans _ unit) σ_s in
         let* κ', σ_s2, C := switch_spec Π_s in
         ⌜κ' = κ⌝ ∗
         let* Π' := C Src _ σ_s2 in
         ∃ e,
         let* κ'', σ_s3, C := switch_spec Π' in
         ⌜κ'' = Some (Incoming, e)⌝ ∗
         let* Π_s'' := C Src _ σ_s3 in
         let* κ'', σ'', C := switch_spec Π_s'' in
         ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ'' = None⌝ ∗
         (γσ_s ⤳ σ'' -∗
         let* Π' := C Tgt _ σ in
         let* κ, σ, C := switch_spec Π' in
         ∃ e', ⌜κ = Some (Incoming, e')⌝ ∗
         (⌜e = e'⌝ -∗
         let* Π' := C Tgt _ σ in
         ⌜Π = Π'⌝))) ∗
      (∀ σ_s, γσ_s ⤳ σ_s -∗
           (∀ Π, σ_s ≈{ spec_trans rec_event () }≈>ₛ Π) -∗ Φ 0).

    (* rec_fn_spec Tgt Π "main" (λ es Φ,  ⌜es = []⌝ ∗ *)
    (*   □ switch_spec Π (λ κ σ C, ∃ vs h σ_s, ⌜κ = Some (Outgoing, ERCall "print" vs h)⌝ ∗ γσ_s ⤳ σ_s ∗ *)
    (*      C Src (spec_trans _ unit) σ_s (λ Π_s, *)
    (*       switch_spec Π_s (λ κ' σ' C, ⌜κ' = κ⌝ ∗ C Src _ σ' (λ Π_s', switch_spec Π_s' (λ κ'' σ'' C,  *)
    (*       γσ_s ⤳ σ'' -∗ C Tgt _ σ (λ Π', ⌜Π = Π'⌝)))))) ∗ *)
    (*   Φ 0). *)
  Proof.
    set (X := letstar (switch_spec _) _).
    iIntros "#?#?#?#?#? Hσs". iIntros (??). iDestruct 1 as (?) "[#Hs Hend]".
    iApply sim_main; [done..|]. iSplit!.

    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns' Hh Ha !>". iIntros "Hσ".
    iApply "Hs". iSplit!. iFrame. iIntros (?) "HC".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    unfold main_spec_body.
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "_".
    iApply "HC". iSplit!. iIntros (?) "[% HC]".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "_".
    iApply "HC". iSplit!. iIntros (?) "HC".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq/=.
    iApply sim_gen_expr_None => /=. iIntros (? [] ??) "_".
    iApply "HC". iSplit!. iIntros "?" (?) "HC".
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HC". iSplit!. iIntros. simplify_eq. }
    iIntros (?? _) "!>". iApply "HC". iSplit!. iIntros (???). simplify_eq/=.
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ".

    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external); [done|].
    iIntros (???) "Hfns'' Hh Ha !>". iIntros "Hσ".
    iApply "Hs". iSplit!. iFrame. iIntros (?) "HC".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "_".
    iApply "HC". iSplit!. iIntros (?) "[% HC]".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply (sim_src_TExist _).
    iApply sim_gen_TVis. iIntros ([]) "_".
    iApply "HC". iSplit!. iIntros (?) "HC".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq/=.
    iApply sim_gen_expr_None => /=. iIntros (? [] ??) "_".
    iApply "HC". iSplit!. iIntros "?" (?) "HC".
    iApply sim_tgt_rec_Waiting_raw.
    iSplit. { iIntros. iModIntro. iApply "HC". iSplit!. iIntros. simplify_eq. }
    iIntros (?? _) "!>". iApply "HC". iSplit!. iIntros (???). simplify_eq/=.
    iApply "Hσ". iSplit!. iFrame. iApply "HΦ". iFrame.

    iApply ("Hend" with "[$]"). iIntros (?).
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply sim_src_TUb_end.
  Qed.



  (* Writing this spec for main_spec probably does not gain much / if
  anything compared to reasoning about the spec module directly *)
  Lemma sim_main_spec Π Φ :
    (∃ f vs h, ∀ σ, handle_cont _ Src Π (Some (Incoming, ERCall f vs h)) σ (λ σ', ⌜σ' = σ⌝ ∗ (
      ⌜f = "main"⌝ -∗ ⌜vs = []⌝ -∗
      ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗
      (∃ h', ∀ σ, handle_cont _ Src Π (Some (Outgoing, ERCall "print" [ValNum 1] h')) σ (λ σ', ⌜σ' = σ⌝ ∗
      (∃ e, ∀ σ, handle_cont _ Src Π (Some (Incoming, e)) σ (λ σ', ⌜σ' = σ⌝ ∗ (∀ v', ⌜e = ERReturn v' h'⌝ -∗
      ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗
      (∃ h', ∀ σ, handle_cont _ Src Π (Some (Outgoing, ERCall "print" [ValNum 2] h')) σ (λ σ', ⌜σ' = σ⌝ ∗
      (∃ e, ∀ σ, handle_cont _ Src Π (Some (Incoming, e)) σ (λ σ', ⌜σ' = σ⌝ ∗ (∀ v', ⌜e = ERReturn v' h'⌝ -∗
      ∀ σ, handle_cont _ Src Π None σ (λ σ', ⌜σ = σ'⌝ ∗ True)))))))))))))))) -∗
    SRC main_spec @ Π {{ Φ }}.
  Proof.
    iIntros "HΦ". iDestruct "HΦ" as (f vs h) "HΦ".
    iEval (unfold main_spec). rewrite /TReceive bind_bind.
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> HΦ]". iSplit; [done|].
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    iDestruct ("HΦ" with "[//] [//]") as "HΦ".
    iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> [% HΦ]]". iExists _. iSplit; [done|]. iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> [% HΦ]]". iSplit; [done|].
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> HΦ]". iSplit; [done|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq.
    iDestruct ("HΦ" with "[//]") as "HΦ".
    iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> [% HΦ]]". iExists _. iSplit; [done|]. iSplit!.
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> [% HΦ]]". iSplit; [done|].
    iApply sim_src_TExist. iApply sim_gen_TVis. iIntros ([]). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> HΦ]". iSplit; [done|].
    iApply sim_src_TAssume. iIntros (?). case_match => //; simplify_eq.
    iDestruct ("HΦ" with "[//]") as "HΦ".
    iApply sim_gen_expr_None => /=. iIntros (? [] ??). iApply (handle_cont_mono with "HΦ").
    iIntros (?) "[-> HΦ]". iExists _. iSplit; [done|]. iSplit!.
    iApply sim_src_TUb_end.
  Qed.
End memmove.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Local Canonical Structure spec_mod_lang_unit.

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
    iModIntro.
    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply (sim_gen_expr_wand _ _ _ _ _ (λ _, False%I) with "[-] []"); [|by iIntros].
    iApply sim_main_spec. iSplit!. iIntros (?) "HC".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "HC". iSplit!. iIntros (-> ->). simplify_eq.

    rewrite bool_decide_true; [|done].
    iIntros (?) "Hs".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply (sim_tgt_link_left with "[-]").
    (* iApply (sim_tgt_link_left_const with "Hγs [Hγσ_locle] [-]"); [done|]. *)
    (* iIntros "Hγs Hγσ_locle". *)
    iApply fupd_sim_gen.
    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }
    iModIntro.

    iApply (sim_gen_expr_intro _ [] _ None with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (Π := link_tgt_leftP _ _ _ _).
    (* set (Π := directMH Tgt _). *)

    have MHnop : inMH _ Tgt nopMH Π. {
      unfold inMH. iIntros "!>" (???) "HΠ Hσ".
      iDestruct "HΠ" as (->) "C" => /=.
      iIntros (?) "Hγσ_s ??". iApply sim_gen_stop.
      iIntros (??) "??".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγσ_t".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγκ".
      iSplit!.
      iApply (sim_tgt_constP_intro_weak with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
      iApply (sim_tgt_link_left with "[-]").
      iApply (sim_gen_wand with "[C Hσ]"); [by iApply "Hσ"|].
      iIntros (??) "HC". iApply ("HC").
    }

    have MHlocle : inMH _ Tgt (locleMH rec_trans) Π. {
      unfold inMH. iIntros "!>" (???) "HΠ Hσ" => /=. by iApply "HΠ".
    }

(*     eassert (inMH (locleMH2 rec_trans _) Π) as ?. { *)
(*       unfold inMH. iIntros "!>" (???) "HΠ Hσ" => /=. *)
(*       iDestruct ("HΠ" with "Hσ") as (?? ->) "HC" => /=. *)
(*       iIntros (??????). destruct!/=. *)
(*       rewrite bool_decide_false //. rewrite bool_decide_true //. *)
(*       iApply (sim_tgt_link_right_recv with "[-]"). *)
(*       iApply (sim_gen_wand with "HC"). iIntros (??) "HC". *)
(* by iApply "HΠ". *)
(*     } *)

    set Pκ : (option rec_event → m_state rec_trans → (m_state m_t → iProp Σ) → iProp Σ) := (λ κ σ C,
        (
        ∃ vs h, ⌜κ = Some (Outgoing, ERCall "print" vs h)⌝ ∗ C (MLFRun None, [Some SPLeft; None], σ, (locle_spec, ()))) ∨
        (∃ v h, ⌜κ = Some (Outgoing, ERReturn v h)⌝ ∗ C (MLFRun None, [], σ, (locle_spec, ()))))%I.

    eassert (inMH _ Tgt (sim_tgtMH γσ_t γσ_s γκ _ Pκ _ _) Π) as MHsrc. {
      unfold inMH. iIntros "!>" (???) "HΠ Hσ".
      iDestruct ("HΠ" with "Hσ") as "[(%&%&->&Hs)|(%&%&->&Hs)]" => /=.
      - iIntros (??????). destruct!/=. rewrite bool_decide_false//.
      - iIntros (??????). destruct!/=. done.
    }

    (* clearbody Π. *)

    (* iApply (sim_gen_expr_handler_wand _ ( *)
    (*   nopMH ∪ locleMH rec_trans ∪ sim_tgtMH γσ_t γσ_s γκ _ Pκ _ _) with "[-]"); last first. { *)
    (*   iIntros "!>" (???) "[[HΠ|HΠ]|HΠ] Hσ". *)
    (*   - iDestruct "HΠ" as (->) "C" => /=. *)
    (*     iIntros (?) "Hγσ_s ??". iApply sim_gen_stop. *)
    (*     iIntros (??) "??". *)
    (*     iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγσ_t". *)
    (*     iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγκ". *)
    (*     iSplit!. *)
    (*     iApply (sim_tgt_constP_intro_weak with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|]. *)
    (*     iApply (sim_tgt_link_left with "[-]"). by iApply "Hσ". *)
    (*   - by iApply "HΠ". *)
    (*   - iDestruct ("HΠ" with "Hσ") as "[[-> Hs]|[(%&%&->&Hs)|(%&%&->&Hs)]]" => /=. *)
    (*     + done. *)
    (*     + iIntros (??????). destruct!/=. rewrite bool_decide_false//. *)
    (*     + iIntros (??????). destruct!/=. done. *)
    (* } *)
    (* set (Π := nopMH ∪ _ ∪ _). *)

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply sim_main. 1-3: by iApply (rec_fn_intro with "[$]").
    (* { iIntros "!>". iApply sim_locle. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). } } *)
    { iIntros "!>". iApply sim_locle2. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). }
      iIntros (??). iDestruct 1 as (?? ->) "HC" => /=.
      iIntros (??????). destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_recv with "[-]"). iApply "HC". iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_right with "[-]"). iApply "HC"; [done|].
      iIntros (??). iDestruct 1 as (?? -> ->) "HC" => /=.
      iIntros (??????). destruct!/=.
      iApply (sim_tgt_link_left_recv with "[-]"). iApply "HC". iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left with "[-]"). by iApply "HC". }
    iSplit!.
    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }

    iIntros (???) "Hfns' Hh Ha !>". iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)).
    iIntros "HC". iLeft. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (?) "Hs".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (?) "Hs".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (? -> ?) "Hs". destruct!/=.
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply sim_tgt_rec_Waiting_raw.
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply "HC". iSplit!. iFrame. iApply "HΦ".

    iIntros (??). iDestruct 1 as (->) "HΦ".
    iApply (sim_tgt_rec_Call_external). { by iApply (rec_fn_intro with "[$]"). }

    iIntros (???) "Hfns'' Hh Ha !>". iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)).
    iIntros "HC". iLeft. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (?) "Hs".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (?) "Hs".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!. iIntros (? -> ?) "Hs". destruct!/=.
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply sim_tgt_rec_Waiting_raw.
    iSplit; [iIntros; iModIntro; by iIntros|].
    iIntros (???) "!>". iIntros (?). simplify_eq.
    iApply (sim_tgt_link_left with "[-]").
    iApply "HC". iSplit!. iFrame. iApply "HΦ".

    iApply sim_tgt_rec_ReturnExt. iIntros (???) "Hfns''' Hh Ha !>".
    iApply (inMH_apply (sim_tgtMH _ _ _ _ _ _ _)). iIntros "HC". iRight. iSplit!.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "Hs". iSplit!.
  Qed.

  Lemma memmove_sim2 :
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
    iApply sim_gen_TVis. iIntros ([]) "_".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt _ None with "[] [-]"); [simpl; done..|].
    iApply sim_src_TAssume. iIntros (?).
    iApply sim_src_TAssume. iIntros (?). simplify_eq.
    iApply sim_gen_expr_None => /=. iIntros (? [] ??) "_".

    rewrite bool_decide_true; [|done].
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_left_recv with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.
    iApply (sim_tgt_link_left with "[-]").
    (* iApply (sim_tgt_link_left_const with "Hγs [Hγσ_locle] [-]"); [done|]. *)
    (* iIntros "Hγs Hγσ_locle". *)
    iApply fupd_sim_gen.
    iMod (rec_mapsto_alloc_big (h_heap h) with "Hh") as "[Hh _]". { apply map_disjoint_empty_r. }
    iModIntro.

    iApply (sim_gen_expr_intro _ [] _ None with "[Hh Ha]"). { done. }
    { rewrite /= /rec_state_interp dom_empty_L right_id_L /=. iFrame "#∗". by iApply rec_alloc_fake. }

    set (Π := link_tgt_leftP _ _ _ _).
    (* set (Π := directMH Tgt _). *)

    have MHnop : inMH _ Tgt nopMH Π. {
      unfold inMH. iIntros "!>" (???) "HΠ Hσ".
      iDestruct "HΠ" as (->) "C" => /=.
      iIntros (?) "Hγσ_s ??". iApply sim_gen_stop.
      iIntros (??) "??".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγσ_t".
      iDestruct (mstate_var_merge with "[$] [$]") as (->) "Hγκ".
      iSplit!.
      iApply (sim_tgt_constP_intro_weak with "[Hγσ_t] [Hγσ_s] [Hγκ] [-]"); [done..|].
      iApply (sim_tgt_link_left with "[-]").
      iApply (sim_gen_wand with "[C Hσ]"); [by iApply "Hσ"|].
      iIntros (??) "HC". iApply ("HC").
    }

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply (sim_main_full with "[] [] [] [] [] Hγσ_s"). 1-4: by iApply (rec_fn_intro with "[$]").
    { iIntros "!>". iApply sim_locle2. 1: done. 1: { by iApply (rec_fn_intro with "[$]"). }
      iIntros (??). iDestruct 1 as (?? ->) "HC" => /=.
      iIntros (??????). destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_recv with "[-]"). iApply "HC". iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_right with "[-]"). iApply "HC"; [done|].
      iIntros (??). iDestruct 1 as (?? -> ->) "HC" => /=.
      iIntros (??????). destruct!/=.
      iApply (sim_tgt_link_left_recv with "[-]"). iApply "HC". iIntros (??). iDestruct 1 as (? ->) "HC" => /=.
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left with "[-]"). by iApply "HC". } { done. }
    iSplit!.
    - unfold letstar. iIntros "!>" (??). iDestruct 1 as (??? ->) "[Hγσ_s HC]" => /=.
      iIntros  (??????). destruct!/=. rewrite !bool_decide_false //.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".
      iApply "HC". iIntros (??). iDestruct 1 as (->) "HC".
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
      iApply "HC". iIntros (??). iDestruct 1 as (?? -> ->) "HC".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". destruct!/=.
      iApply (sim_tgt_link_left_recv with "[-]").
      iApply ("HC" with "[$]"). iIntros (??). iDestruct 1 as (? ->) "HC".
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left with "[-]").
      iApply "HC". iSplit!. done.
    - iIntros (?) "Hγσ_s Hs". iApply sim_tgt_rec_ReturnExt. iIntros (???) "Hfns''' Hh Ha !>".
      iIntros "?" => /=. iIntros (??????). destruct!/=.
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
