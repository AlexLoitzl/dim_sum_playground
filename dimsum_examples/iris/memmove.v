From dimsum.examples Require Import memmove.
From dimsum.examples.iris Require Export rec2.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(* TODO - Is this a more general notion we want to factor out somewhere? *)
Definition splittable {Σ A B} (P : A → iProp Σ) (PL : B → iProp Σ) : iProp Σ :=
  ∀ a,
  P a -∗
  ∃ b, PL b ∗ (PL b -∗ P a).

Section locle.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Definition locle_hoare (P: iProp Σ) ts Π : iProp Σ :=
    rec_hoare ts Π "locle"
      (λ es RET, ∃ l1 l2, ⌜es = [Val (ValLoc l1); Val $ ValLoc l2]⌝ ∗ P ∗ RET (l1, l2))%I
      (λ '(l1, l2) ret, ∃ b, P ∗ ⌜ret = ValBool b⌝ ∗
                         ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝)%I.

  Lemma sim_locle_spec `{!specGS} Π Φ :
    switch Π ({{ κ σ1 POST,
      ∃ f es h, ⌜κ = Some (Incoming, ERCall f es h)⌝ ∗
    POST Tgt _ _ Π ({{ σ',
      ∃ l1 l2, ⌜σ' = σ1⌝ ∗ ⌜f = "locle"⌝ ∗ ⌜es = [ValLoc l1; ValLoc l2]⌝ ∗
    switch Π ({{ κ σ POST,
      ∃ b, ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ ∗
      ⌜κ = (Some (Outgoing, ERReturn (ValBool b) h))⌝ ∗
    POST Tgt _ _ Π ({{σ',
      ⌜σ' = σ⌝ ∗ TGT locle_spec @ Π {{ Φ }}}})}})}})}}) -∗
    TGT locle_spec @ Π {{ Φ }}.
  Proof.
    iIntros "Hs".
    rewrite {2}/locle_spec unfold_forever /TReceive bind_bind -/locle_spec bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>".
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply (sim_gen_TVis with "[-]").
    iIntros (?) "Hγ !> %% [-> [-> HΠ]]".
    iApply "Hs". iSplit!. iIntros (?) "(% & % & -> & -> & -> & HC)".
    iApply "HΠ". iFrame. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_tgt_TAll with "[-]"). iModIntro. rewrite bind_bind.
    iApply (sim_tgt_TAll with "[-]"). iModIntro. rewrite bind_bind.
    iApply (sim_tgt_TAssume with "[-]"); [done|iModIntro]. rewrite bind_bind.
    iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>". rewrite bind_bind.
    iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>".
    iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>".
    iIntros (??) "[-> [-> HΠ]]".
    iApply "HC". iSplit!.
    iIntros (?) "[-> ?]".
    iApply "HΠ" => /=. by iFrame.
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

  Lemma sim_locle fns Π_l Π_r (PL : m_state (spec_trans rec_event ()) → iProp Σ) σi :
    rec_fn_auth fns -∗
    "locle" ↪ None -∗
    PL σi -∗
    ⌜σi.1 ≡ locle_spec⌝ -∗
    □ switch_link Tgt Π_l ({{σ_l POST,
      ∃ vs h σg, PL σg ∗
      POST (ERCall "locle" vs h) (spec_trans _ _) σg Π_r ({{_,
      switch_link Tgt Π_r ({{σ_r POST,
        ∃ v h',
      POST (ERReturn v h') _ σ_l Π_l ({{_,
        PL σ_r}})}})}})}}) -∗
    |==> ∃ P, P ∗ □ locle_hoare P Tgt Π_l ∗ □ splittable (λ _ : unit, P) PL.
  Proof.
    iIntros "#? #? HPL % #HC".
    iMod (mstate_var_alloc ()) as (γ) "Hγ".
    iMod (mstate_var_split γ () with "[$]") as "[Hγ Hγ']".
    pose (HS := SpecGS γ).

    set P := (∃ σ Φg, PL σ ∗ spec_state () ∗
                      ({{σ', ⌜σ' = σ⌝ ∗ TGT locle_spec @ Π_r {{Φg}}}}) ⇒ₜ Π_r)%I.

    iExists P.
    iModIntro. iSplit!.
    - iExists _, (λ e, sim_post Tgt () Π_r e).
      iFrame.
      iIntros ([? []]) "[<- H]".
      iApply (sim_gen_expr_intro with "[Hγ]") => //=.
    - iIntros "!> %% (% & % & -> & (% & % & ? & ? & Hg) & HΦ)".
      iApply (sim_tgt_rec_Call_external with "[$]").
      iIntros (???) "#??!> %% [-> [-> HΠl]]".
      iApply "HC". iFrame. iSplit!.
      iIntros (?) "[-> HC']".
      iApply "Hg". iSplit!.
      iApply sim_locle_spec.
      iIntros (??) "(% & % & % & -> & Hg)".
      iApply "HC'". iSplit!.
      iIntros (?) "[% [% HC']]". simplify_eq.
      iApply "Hg". iSplit!.
      iIntros (??) "[% [% [-> HΠr]]]".
      iApply "HC'". iSplit!.
      iIntros (?) "[-> HC']".
      iApply sim_tgt_rec_Waiting_all_raw.
      iIntros (?) "!>". iApply "HC'". iSplit!. iIntros (?) "[-> [-> HPL]]".
      iApply "HΠl". iSplit!. iFrame.
      iApply "HΦ". iFrame. iSplit!.
    - iIntros "!> % (% & % & ? & ?)".
      iFrame.
      iIntros "HPL".
      iFrame.
  Qed.
End locle.

Section memmove.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_memcpy Π :
    "memcpy" ↪ Some memcpy_rec -∗
    rec_hoare Tgt Π "memcpy"
      (λ es RET, ∃ d s n o d' s' hvss hvsd,
        ⌜es = [Val $ ValLoc d; Val $ ValLoc s; Val $ ValNum n; Val $ ValNum o]⌝ ∗
        ⌜n = Z.of_nat (length hvss)⌝ ∗
        ⌜length hvss = length hvsd⌝ ∗
        ⌜o = 1 ∨ o = -1⌝ ∗
        ⌜d' = (if bool_decide (o = 1) then d else d +ₗ (- n + 1))⌝ ∗
        ⌜s' = (if bool_decide (o = 1) then s else s +ₗ (- n + 1))⌝ ∗
        ⌜(if bool_decide (o = 1) then d.1 = s.1 → d.2 ≤ s.2 else d.1 = s.1 → s.2 ≤ d.2)⌝ ∗
        ([∗ map] l↦v∈array s' hvss ∪ array d' hvsd, l ↦ v) ∗ RET (s', d', hvss))
      (λ '(s, d, hvss) v, ⌜v = 0⌝ ∗ ([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v)).
  Proof.
    iIntros "#Hf". iApply rec_hoare_ctx. iIntros "#?".
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
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite length_insert. done. } { simpl. naive_solver lia. }
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
          iApply "IH". iFrame. iSplit!. { lia. } { lia. }
          { apply loc_eq; split!; lia. } { apply loc_eq; split!; lia. }
          iIntros (?) "[-> ?]". iSplit!. iApply ("HΦ" with "[-]"). iSplit!.
          rewrite -(insert_union_r _ ∅). 2: { apply array_lookup_None => /=. lia. }
          rewrite -insert_union_l right_id_L -insert_union_r. 2: { apply array_lookup_None => /=. lia. }
          rewrite insert_insert. by iApply (big_sepM_insert_2 with "[Hdv]"); [done|].
        * rewrite delete_insert_ne // delete_insert. 2: { apply array_lookup_None => /=. lia. }
          have ?: d.2 ≠ s.2. { destruct d, s; naive_solver. }
          rewrite (array_insert s (d +ₗ - length hvss)) //=; [|naive_solver lia].
          iApply "IH". iFrame. iSplit!. { lia. } { rewrite length_insert. lia. }
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

  Lemma sim_memmove Π P :
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    □ locle_hoare P Tgt Π -∗
    rec_hoare Tgt Π "memmove"
      (λ es RET, ∃ hvss hvsd d s n,
        ⌜es = [Val (ValLoc d); Val $ ValLoc s; Val $ ValNum n]⌝ ∗
        ⌜n = Z.of_nat (length hvss)⌝ ∗
        ⌜length hvss = length hvsd⌝ ∗
        ([∗ map] l↦v∈array s hvss ∪ array d hvsd, l ↦ v) ∗ P ∗ RET (d,s,hvss))%I
      (λ '(d,s,hvss) v, P ∗ ⌜v = 0⌝ ∗ ([∗ map] l↦v∈array d hvss ∪ array s hvss, l ↦ v))%I.
  Proof.
    iIntros "#Hmemmove #Hmemcpy #Hlocle". iIntros (es Φ) "HΦ".
    iDestruct "HΦ" as (hvss hvsd d s n -> -> ?) "[Hs [? HΦ]]".
    iApply (sim_gen_expr_bind _ []).
    iApply (sim_tgt_rec_Call_internal with "Hmemmove"); [done|]. iModIntro => /=.
    iApply sim_tgt_rec_AllocA; [econs|] => /=. iIntros (?) "?". destruct ls => //. iModIntro.
    iApply (sim_gen_expr_bind _ [IfCtx _ _] with "[-]") => /=.
    iApply "Hlocle". iFrame. iSplit!. iIntros (?) "[%b [? [-> %Hb]]]" => /=.
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

  (* NOTE - REVIEW: We now have fixed Π, but I think it's actually easier to write the lemma without switch_id *)
  (* This spec is tricky to use since one needs to pick one Π upfront *)
  (* Lemma sim_locle_spec' `{!specGS} Π Φ : *)
  (*   (∀ f vs h σ, switch_id Tgt _ Π (Some (Incoming, ERCall f vs h)) σ (λ σ', ∃ l1 l2, ⌜σ' = σ⌝ ∗ *)
  (*     ⌜f = "locle"⌝ ∗ ⌜vs = [ValLoc l1; ValLoc l2]⌝ ∗ (∀ b, *)
  (*       ⌜l1.1 = l2.1 → b = bool_decide (l1.2 ≤ l2.2)⌝ -∗ ∀ σ, *)
  (*         switch_id Tgt _ Π (Some (Outgoing, ERReturn (ValBool b) h)) σ (λ σ', ⌜σ' = σ⌝ ∗ *)
  (*           TGT locle_spec @ Π {{ Φ }})))) -∗ *)
  (*   TGT locle_spec @ Π {{ Φ }}. *)
  (* Proof. *)
  (*   iDestruct 1 as "HC". unfold locle_spec at 2. rewrite unfold_forever -/locle_spec. *)
  (*   rewrite /TReceive bind_bind bind_bind. *)
  (*   iApply (sim_tgt_TExist with "[-]"). iIntros ([[??]?]) "!>". *)
  (*   rewrite bind_bind. setoid_rewrite bind_ret_l. *)
  (*   iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>". *)
  (*   iApply (switch_id_mono with "HC"). iIntros (?). iDestruct 1 as (l1 l2 -> -> ->) "HC" => /=. iFrame. *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAll with "[-]"). iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAssume with "[-]"); [done|]. iIntros "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TExist with "[-]"). iIntros (b) "!>". *)
  (*   rewrite bind_bind. iApply (sim_tgt_TAssert with "[-]"). iIntros (?) "!>". *)
  (*   iApply (sim_gen_TVis with "[-]"). iIntros ([]) "? !>". *)
  (*   iApply (switch_id_mono with "[HC]"). { iApply ("HC" with "[//]"). } *)
  (*   simpl. iIntros (?). iDestruct 1 as (->) "HC". iFrame. *)
  (* Qed. *)

End memmove.

Section main.
  Context `{!dimsumGS Σ} `{!recGS Σ}.

  Lemma sim_main Π P :
    "memmove" ↪ Some memmove_rec -∗
    "memcpy" ↪ Some memcpy_rec -∗
    "main" ↪ Some main_rec -∗
    □ locle_hoare P Tgt Π -∗
    rec_hoare Tgt Π "main" (λ es RET, ⌜es = []⌝ ∗ P ∗
      rec_hoare Tgt Π "print"
        (λ es RET, P ∗ ⌜es = [Val 1]⌝ ∗ RET tt)
        (λ _ v, rec_hoare Tgt Π "print"
                  (λ es RET, ⌜es = [Val 2]⌝ ∗ RET tt)
                  (λ _ _, RET tt)))
        (λ _ v, ⌜v = 0⌝).
  Proof.
    iIntros "#? #? #? #?". iIntros (es Φ) "[-> [? HΦ]]".
    iApply sim_tgt_rec_Call_internal. 2: { done. } { done. }
    iModIntro.
    iApply sim_tgt_rec_AllocA; [by econs|]. iIntros (?) "Hl".
    destruct ls as [|l []] => //=. 2: by iDestruct!.
    have -> : (0%nat + 0) = 0 by [].
    have -> : (1%nat + 0) = 1 by []. have -> : (2%nat + 0) = 2 by [].
    iDestruct "Hl" as "[[Hl0 [Hl1 [Hl2 _]]] _]". iModIntro.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]").
    iApply (sim_gen_expr_bind _ [StoreLCtx _] with "[-]").
    iApply sim_tgt_rec_BinOp; [done|iModIntro].
    iApply (sim_tgt_rec_Store with "Hl0"). iIntros "Hl0 !>" => /=.
    iApply sim_tgt_rec_LetE. iIntros "!> /=".
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
    iFrame.
    iIntros (?) "[? [-> Hl]]" => /=.
    rewrite !array_cons !array_nil -!insert_union_l !left_id_L.
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

    iApply "HΦ". iFrame. iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply (sim_gen_expr_bind _ [LetECtx _ _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [CallCtx _ [] _] with "[-]") => /=.
    iApply (sim_gen_expr_bind _ [LoadCtx] with "[-]") => /=.
    iApply sim_tgt_rec_BinOp; [done|]. iModIntro => /=.
    iApply (sim_tgt_rec_Load with "Hl2"). iIntros "Hl2 !>" => /=.

    iApply "HΦ". iFrame. iSplit!. iIntros (?) "HΦ".

    iApply (sim_tgt_rec_LetE with "[-]"). iIntros "!>" => /=.
    iApply sim_gen_expr_stop => /=. iSplit!. iFrame. by iApply "HΦ".
  Qed.

  Definition call_print v : spec rec_event unit unit :=
    h ← TExist _;
    '(_,h') ← TCallRet "print" [ValNum v] h;
    TAssume (h = h').
  
  Definition main_spec_body : spec rec_event unit void :=
    call_print 1;;
    call_print 2;;
    TUb.

  Definition print_ext_hoare `{specGS}
      (PL : m_state (spec_trans rec_event ()) → iProp Σ) ts Π : iProp Σ :=
    rec_hoare ts Π "print"
      (λ es RET, ∃ σ v k, spec_state_name ⤳@{unit} - ∗
        PL σ ∗ ⌜σ.1 ≡ Spec.bind (call_print v) k⌝ ∗ ⌜es = [Val v]⌝ ∗ RET k)%I
      (λ k _, ∃ σ_s, PL σ_s ∗ spec_state_name ⤳@{unit} - ∗ ⌜σ_s.1 ≡ k tt⌝)%I.

  Lemma call_print_sim (S : specGS) fns PL Π_t Π_s :
    rec_fn_auth fns -∗
    "print" ↪ None -∗
    □ switch_external Π_t ({{κ0 σ_t POST0,
        ∃ vs h σs, PL σs ∗ ⌜κ0 = Some (Outgoing, ERCall "print" vs h)⌝ ∗
      POST0 (spec_trans _ ()) σs Π_s ({{σ_s1',
        ∃ e : rec_ev,
      switch Π_s ({{ κ3 σ_s2 POST2,
        ⌜κ3 = Some (Incoming, e)⌝ ∗
      POST2 Src _ (spec_trans _ ()) Π_s ({{ σ_s2',
        ⌜σ_s2 = σ_s2'⌝ ∗
      switch Π_s ({{ κ4 σ_s3 POST3,
        ∃ v h', ⌜e = ERReturn v h'⌝ ∗ ⌜κ4 = None⌝ ∗
      POST3 Tgt _ _ Π_t ({{ σ_t1,
        ⌜σ_t1 = σ_t⌝ ∗
      switch Π_t ({{ κ5 σ_t2 POST4,
        ∃ e' : rec_ev, ⌜κ5 = Some (Incoming, e')⌝ ∗
      POST4 Tgt rec_event rec_trans Π_t ({{ σ_t3,
        ⌜σ_t3 = σ_t2⌝ ∗ ⌜e = e'⌝ ∗ PL σ_s3
    }})}})}})}})}})}})}})}}) -∗
    □ print_ext_hoare PL Tgt Π_t.
  Proof.
    set γ := spec_state_name.
    set (X := (switch_external _) _).
    iIntros "#?#?#HC !> %% (%σ & % & % & ? & ? & % & -> & HΦ)".
    iMod (mstate_var_split γ σ.2 with "[$]") as "[Hγ Hγ']".
    iApply (sim_tgt_rec_Call_external with "[$]").
    iIntros (???) "#?? !>".
    iIntros (??) "[-> [-> HΠ_t]]".
    iApply "HC". iFrame. iSplit!.
    iIntros (?) "[-> HC']".
    (* TODO *)
    iApply (sim_gen_expr_intro _ tt with "[Hγ] [-]"); simpl; [done..|].
    rewrite bind_bind.
    iApply sim_src_TExist. rewrite bind_bind.
    iApply sim_src_TCallRet.
    iIntros (??) "(% & % & % & -> & -> & -> & -> & HΠ_s)".
    iApply "HC'". iSplit!.
    iIntros (?) "[-> [% HC']]".
    iApply "HΠ_s". iSplit!. iIntros (??) "[-> HΠ_s]".
    iApply "HC'". iSplit!. iIntros (?) "[-> HC']".
    iApply "HΠ_s". iSplit!. iIntros (?? ->).
    iApply sim_src_TAssume. iIntros "->".
    iApply sim_gen_expr_None => /=.
    iIntros (?) "_ % ? %% /= [-> [-> H]]".
    iApply "HC'". iSplit!.
    iIntros (?) "/= [-> HC']".
    iApply sim_tgt_rec_Waiting_all_raw. iIntros (?) "!>".
    iApply "HC'". iSplit!. iIntros (?) "[-> [<- ?]]" => /=.
    iApply "HΠ_t". iSplit!. iFrame.
    iApply "HΦ".
    iDestruct (mstate_var_merge with "Hγ' [$]") as "[_ ?]".
    by iFrame.
  Qed.

  Definition main_spec : spec rec_event unit void :=
    '(f, vs, h) ← TReceive (λ '(f, vs, h), (Incoming, ERCall f vs h));
    TAssume (f = "main");;
    TAssume (vs = []);;
    main_spec_body.

  Let m_t := rec_link_trans {["main"; "memmove"; "memcpy"]} {["locle"]}
               rec_trans (spec_trans rec_event ()).

  Lemma memmove_sim :
    rec_state_interp (rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog)) None -∗
    (MLFRun None, [], rec_init (main_prog ∪ memmove_prog ∪ memcpy_prog), (locle_spec, ())) ⪯{m_t,
      spec_trans rec_event unit} (main_spec, tt).
  Proof.
    iIntros "[#Hfns ?] /=".
    (* Ghost variable for source, target, and event *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event unit))) as (γσ_s) "Hγσ_s".
    iMod (mstate_var_alloc (m_state m_t)) as (γσ_t) "Hγσ_t".
    iMod (mstate_var_alloc (option rec_event)) as (γκ) "Hγκ".
    (* Source's state *)
    iMod (mstate_var_alloc unit) as (γs_s) "?".
    iMod (mstate_var_split γs_s tt with "[$]") as "[Hγs_s ?]".
    pose (Hspec := SpecGS γs_s).

    iApply (sim_tgt_constP_intro γσ_t γσ_s γκ with "Hγσ_t Hγσ_s Hγκ [-]"). iIntros "Hγσ_s".
    iApply (sim_tgt_link_None with "[-]").
    iIntros "!>" (??????). destruct!/=. case_match; destruct!/=.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply (sim_gen_expr_intro _ tt with "[Hγs_s] [-]"); [simpl; done..|].
    iEval (rewrite /main_spec /TReceive bind_bind).
    iApply (sim_src_TExist (_, _, _)).
    rewrite bind_bind. setoid_rewrite bind_ret_l.
    iApply sim_gen_TVis. iIntros ([]) "Hγs". iIntros (??) "[-> [-> HΠ_s]]".
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s". iApply sim_gen_stop.
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".
    iApply "HΠ_s". iFrame.
    iApply sim_src_TAssume. iIntros (->).
    iApply sim_src_TAssume. iIntros (->).
    iApply sim_gen_expr_None => /=. iIntros (? [] ?) "Hγs".
    (* TODO - Here for external call *)
    iIntros (??) "[-> [-> _]]".

    rewrite bool_decide_true; [|done].
    iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
    iIntros "Hγσ_s".
    iApply (sim_tgt_link_recv_left with "[-]").
    iApply (sim_tgt_rec_Waiting_raw _ []).
    iSplit; [|by iIntros].
    iIntros (???? Hin) "!>". iIntros (?). simplify_map_eq.

    iMod (heapUR_alloc_blocks _ (h_blocks h) with "[$]") as "[Hinv _]". { set_solver. }
    rewrite right_id_L heap_from_blocks_h_blocks.

    (* Target's spec module (Right linking case - locle) *)
    iMod (mstate_var_alloc (m_state (spec_trans rec_event unit))) as (γσr_t) "Hγσr_t".
    (* Target's rec module (Left linking case) *)
    iMod (mstate_var_alloc (m_state rec_trans)) as (γσl_t) "Hγσl_t".
    (* call stack of linking module  *)
    iMod (mstate_var_alloc (list seq_product_case)) as (γq_t) "Hγq_t".
    (* Linking event to pass around *)
    iMod (mstate_var_alloc (option rec_ev)) as (γκ_t) "Hγκ_t".

    iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t with "[$] [$] [$] [$] [-]").
    iIntros "Hγq_t Hγσr_t Hγκ_t".

    iApply (sim_gen_expr_intro _ [] with "[Hinv]"). { done. } { by iFrame. }

    set (Π := tgt_link_left_constP _ _ _ _ _ _).
    set PL := (λ (σ : m_state (spec_trans rec_event unit)),
                 γσr_t ⤳ σ ∗ γκ_t ⤳ @None rec_ev ∗ γq_t ⤳ [None : seq_product_case])%I.
    iDestruct (sim_locle _ Π _ PL (locle_spec, tt) with "[$] [] [$] [//]") as "H".
    1: by iApply (rec_fn_intro with "[$]").
    iMod ("H" with "[]") as "[%Pl [HPl [#Hlocle #Hsplitl]]]".
    {
      iIntros "!> %% (% & % & % & (Hγσr_t & ? & ?) & -> & HC)".
      (* REVIEW - How to do this better with done *)
      iApply (tgt_link_left_constP_run_elim with "[$] [Hγσr_t] [$]"); [done|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????).
      destruct!/=. rewrite bool_decide_false //. rewrite bool_decide_true //.
      iApply (sim_tgt_link_right_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_right_constP_recv_elim with "[Hγq_t] [Hγσl_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t" (?). simplify_eq.
      iApply (sim_tgt_link_right_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγκ_t".

      iApply "HC" => /=. iSplit!.
      iIntros (??) "[% [% [-> HC]]]".
      iApply (tgt_link_right_constP_run_elim with "[Hγq_t] [Hγσl_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????). destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!.
      iIntros (??) "[% [-> HC]]" => /=.
      iApply (tgt_link_left_constP_recv_elim with "[Hγq_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (?). simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply "HC". iSplit!. iFrame.
    }

    iDestruct (mstate_var_merge with "Hγs [$]") as "[_ Hγs]".
    set PL' := (λ (σ : m_state (spec_trans rec_event unit)), γσ_s ⤳ σ ∗ (∃ σ', PL σ'))%I.

    iDestruct (call_print_sim Hspec _ PL' Π with "[$] [] []") as "#Hprint".
    1: by iApply (rec_fn_intro with "[$]").

    {
      iIntros "!> %% (% & % & % & (Hγσ_s & % & Hγσr_t & ? & ?) & -> & HC)".
      iApply (tgt_link_left_constP_run_elim with "[$] [Hγσr_t] [$]"); [done|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
      iIntros (??????). destruct!/=. rewrite bool_decide_false //.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "[-> HC]".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s".
      iApply (sim_tgt_link_None with "[-]"). iIntros "!>" (??????). destruct!/=.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "[-> HC]".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". iApply sim_gen_stop.
      iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
      iIntros "Hγσ_s Hγσ_t Hγκ".

      iApply "HC". iSplit!. iIntros (??) "(% & % & -> & -> & HC)".
      iApply (sim_src_constP_next with "[Hγσ_t] [Hγκ] [Hγσ_s] [%] [-]"); [done..|].
      iIntros "Hγσ_s". destruct!/=.
      iApply (sim_tgt_link_left_constP_recv γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσr_t Hγκ_t".

      iApply ("HC" with "[-]"). iFrame. iSplit!.
      iIntros (??) "[% [-> HC]]".
      iApply (tgt_link_left_constP_recv_elim with "[Hγq_t] [Hγσr_t] [$] [-]"); [done..|].
      iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t %". simplify_eq.
      iApply (sim_tgt_link_left_constP_run γq_t γσl_t γσr_t γκ_t
               with "[$] [Hγσl_t] [Hγσr_t] [$] [-]"). 1-2: done.
      iIntros "???".

      iApply "HC". iSplit!. iFrame.
    }

    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]") => /=.
    iApply (sim_main with "[] [] [] [$]"). 1-3: by iApply (rec_fn_intro with "[$]").
    iFrame. iSplit!.
    iIntros (??) "[? [-> HΦ]]".

    iDestruct ("Hsplitl" $! tt with "[$]") as "[%σ' [HPL ?]]".

    iApply "Hprint". iFrame. iSplit!;[done|]. iIntros (?) "[% [? [? %]]]".
    iApply "HΦ".
    iIntros (??) "[? HΦ]".
    iApply "Hprint".
    iFrame. iSplit!;[done|].
    iIntros (?) "[%σ_s' [[Hγσ_s [% [Hγσr_t [Hγκ_t Hγq_t]]]] [? %]]]".
    iApply "HΦ".
    iIntros (?->).
    iApply (sim_gen_expr_bind _ [ReturnExtCtx _] with "[-]").

    iApply (sim_gen_expr_stop). iSplit!. iFrame.

    iApply sim_gen_expr_None. iIntros (??) "?? %% /= [-> [-> ?]]".
    iApply (tgt_link_left_constP_run_elim with "Hγq_t [Hγσr_t] [$]");[done|].
    iIntros "Hγq_t Hγσl_t Hγσr_t Hγκ_t".
    iApply (sim_tgt_constP_elim γσ_t γσ_s γκ with "[Hγσ_s] [-]"); [done..|].
    iIntros "Hγσ_s Hγσ_t Hγκ".

    iMod (mstate_var_split γs_s () with "[$]") as "[Hγs_s Hγs_s']".
    (* TODO *)
    iApply (sim_gen_expr_intro _ tt with "[Hγs_s]") => //=.
    { destruct σ_s'. simpl. destruct u. done. }
    iApply sim_src_TUb_end.
Qed.

End main.

Lemma memmove_refines_spec :
  trefines (rec_link {["main"; "memmove"; "memcpy"]} {["locle"]}
              (rec_mod (main_prog ∪ memmove_prog ∪ memcpy_prog))
              (spec_mod locle_spec tt))
    (spec_mod main_spec tt).
Proof.
  eapply (sim_adequacy #[dimsumΣ; recΣ]); [eapply _..|].
  iIntros (??) "!>". simpl.
  iMod recgs_alloc as (?) "[??]".
  iApply memmove_sim. iFrame.
Qed.

(* Idea: construct PI for source level proof from pre and
postconditions of all the external functions instead of constructing
it directly from the used combinators. Maybe one can do the texan
triple trick to force monotonicity of the Π. *)
