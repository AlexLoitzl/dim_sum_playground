Require Export refframe.module.
Require Import refframe.srefines.
Require Import refframe.trefines.
Require Import refframe.filter.


(*** [product] *)
Inductive product_step {EV1 EV2} (m1 : module EV1) (m2 : module EV2) :
  (m1.(m_state) * m2.(m_state)) → option (option EV1 * option EV2) → ((m1.(m_state) * m2.(m_state)) → Prop) → Prop :=
| ProductStepL σ1 σ2 e Pσ:
    m1.(m_step) σ1 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (Some e', None) else None)
                 (λ '(σ1', σ2'), Pσ σ1' ∧ σ2 = σ2')
| ProductStepR σ1 σ2 e Pσ:
    m2.(m_step) σ2 e Pσ →
    product_step m1 m2 (σ1, σ2)
                 (if e is Some e' then Some (None, Some e') else None)
                 (λ '(σ1', σ2'), σ1 = σ1' ∧ Pσ σ2')
| ProductStepBoth σ1 σ2 e1 e2 Pσ1 Pσ2:
    m1.(m_step) σ1 (Some e1) Pσ1 →
    m2.(m_step) σ2 (Some e2) Pσ2 →
    product_step m1 m2 (σ1, σ2)
                 (Some (Some e1, Some e2))
                 (λ '(σ1', σ2'), Pσ1 σ1' ∧ Pσ2 σ2')
.

Definition mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) : module (option EV1 * option EV2) :=
  Mod (product_step m1 m2).

Module test3.

(*

              1     3
        /- 1 --- 2 --- 3
M1: 0 -∀
        \- 4 --- 5 --- 6
              2     4

                    1     Y
       X      /- 2 --- 3 --- 4
MA: 0 --- 1 -∃
              \- 5 --- 6 --- 7
                    2     Y

              X     Y     3
        /- 1 --- 2 --- 3 --- 4
MB: 0 -∀
        \- 5 --- 6 --- 7 --- 8
              X     Y     4

                          3
        X     Y     /- 3 --- 4
MB': 0 --- 1 --- 2 -∀
                    \- 5 --- 6
                          4

We have [M1 ⊑ prod MA MB] and [MB ⊑ MB'], but ¬ [M1 ⊑ prod MA MB'].
Thus we cannot have [prod MA MB ⊑ prod MA MB'].

To see that this is a realistic case, consider [M1 ⊑ prod MA MB] in two steps:
First we have [M1 ⊑ M1'] which introduces the demonic choice:


                      1     3
                /- 2 --- 3 --- 4
          /- 1 -∃
         /      \- 5 --- 6 --- 7
        /             2     3
M1': 0 -∀
        \             1     4
         \      /- 9 --- A --- B
          \- 8 -∃
                \- C --- D --- E
                      2     4

Written as programs, we have :

M1 : x ← angelic_choice({3, 4}); y ← if x = 3 then 1 else 2; output(y); output(x)
M1': x ← angelic_choice({3, 4}); y ← demonic_choice({1, 2}); output(y); output(x)

Now we want to split the demonic choice in M1' into a separate function:

f   := y ← demonic_choice({1, 2}); output(y)
M1'': x ← angelic_choice({3, 4}); f(); output(x)

If one now one wants to verify M1'' and f separately, it might seem that one can
commute the angelic choice over the call to f (which would just be an external
event). But this is not sound!

(If the angelic choice and demonic choice seems to abstract, one can think of the
angelic choice as a integer to pointer cast and the demonic choice as an allocation.)


Question: Should one be able to do the following optimization if integer to pointer
casts are defined via angelic choice?

Either if f is an unknown function call or a call to malloc or a call to a function
where we know that it does not do a non-deterministic choice?

int x = ...;
int *a = (int * )x;
//f();
int *y = malloc();
return y + *a;

-optimize to>

int x = ...;
//f();
int *y = malloc();
return y + *(int * )x;


For malloc, the commutation is probably invalid and thus also for the case of unknown
function. But is there a model where one can commute the angelic choice over the
external function call if one knows that it does not do demonic choices?
Maybe, but such a model might be quite complicated and it is not clear how much it is worth
to be able to do this commutation in this quite specific case (or it is not clear how common
the case where the commutation is sound is).

 *)

Inductive prod_mod1_step : nat → option nat → (nat → Prop) → Prop :=
| PM1S0: prod_mod1_step 0 None (λ σ', σ' = 1 ∨ σ' = 4)
| PM1S1: prod_mod1_step 1 (Some 1) (λ σ', σ' = 2)
| PM1S2: prod_mod1_step 2 (Some 3) (λ σ', σ' = 3)
| PM1S4: prod_mod1_step 4 (Some 2) (λ σ', σ' = 5)
| PM1S5: prod_mod1_step 5 (Some 4) (λ σ', σ' = 6)
.

Definition prod_mod1 : module nat := Mod prod_mod1_step.

Inductive prod_modA_step : nat → option nat → (nat → Prop) → Prop :=
| PMAS0 : prod_modA_step 0 (Some 10) (λ σ', σ' = 1)
| PMAS11: prod_modA_step 1 None (λ σ', σ' = 2)
| PMAS12: prod_modA_step 1 None (λ σ', σ' = 5)
| PMAS2 : prod_modA_step 2 (Some 1) (λ σ', σ' = 3)
| PMAS3 : prod_modA_step 3 (Some 11) (λ σ', σ' = 4)
| PMAS5 : prod_modA_step 5 (Some 2) (λ σ', σ' = 6)
| PMAS6 : prod_modA_step 6 (Some 11) (λ σ', σ' = 7)
.

Definition prod_modA : module nat := Mod prod_modA_step.

Inductive prod_modB_step : nat → option nat → (nat → Prop) → Prop :=
| PMBS0: prod_modB_step 0 None (λ σ', σ' = 1 ∨ σ' = 5)
| PMBS1: prod_modB_step 1 (Some 10) (λ σ', σ' = 2)
| PMBS2: prod_modB_step 2 (Some 11) (λ σ', σ' = 3)
| PMBS3: prod_modB_step 3 (Some 3) (λ σ', σ' = 4)
| PMBS5: prod_modB_step 5 (Some 10) (λ σ', σ' = 6)
| PMBS6: prod_modB_step 6 (Some 11) (λ σ', σ' = 7)
| PMBS7: prod_modB_step 7 (Some 4) (λ σ', σ' = 8)
.

Definition prod_modB : module nat := Mod prod_modB_step.

Inductive prod_modB'_step : nat → option nat → (nat → Prop) → Prop :=
| PMB'S0: prod_modB'_step 0 (Some 10) (λ σ', σ' = 1)
| PMB'S1: prod_modB'_step 1 (Some 11) (λ σ', σ' = 2)
| PMB'S2: prod_modB'_step 2 None (λ σ', σ' = 3 ∨ σ' = 5)
| PMB'S3: prod_modB'_step 3 (Some 3) (λ σ', σ' = 4)
| PMB'S5: prod_modB'_step 5 (Some 4) (λ σ', σ' = 6)
.

Definition prod_modB' : module nat := Mod (prod_modB'_step).

Definition filterR (e1 : (option nat * option nat)) (e2 : option nat) : Prop :=
    (e1 = (Some 10, Some 10) ∧ e2 = None)
  ∨ (e1 = (Some 11, Some 11) ∧ e2 = None)
  ∨ (e1 = (Some 1, None) ∧ e2 = Some 1)
  ∨ (e1 = (Some 2, None) ∧ e2 = Some 2)
  ∨ (e1 = (None, Some 3) ∧ e2 = Some 3)
  ∨ (e1 = (None, Some 4) ∧ e2 = Some 4).
Arguments filterR _ _ /.
Definition prod_mod : module nat := mod_filter (mod_product prod_modA prod_modB) filterR.
Definition prod_mod' : module nat := mod_filter (mod_product prod_modA prod_modB') filterR.

Lemma prod_mod1_refines_prod_mod:
  srefines (MS prod_mod1 0) (MS prod_mod (0, 0)).
Proof.
  constructor => Pκs /= Himpl.
  inversion Himpl; simplify_eq. 1: by apply: STraceEnd.
  invert_all @m_step.

  apply: STraceStep. { econstructor. { apply ProductStepR. constructor. } done. } 2: done.
  move => [??] [?[?|?]]; simplify_eq.
  - have {}H := (H0 1 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.

    apply: STraceStep. { econstructor. { apply ProductStepBoth; constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepL. apply: PMAS11. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepL. constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepBoth; constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.

    have {}H := (H3 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.
    apply: STraceStep. { econstructor. { apply ProductStepR. constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.
    have {}H := (H5 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.
  - have {}H := (H0 4 ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.

    apply: STraceStep. { econstructor. { apply ProductStepBoth; constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepL. apply: PMAS12. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepL. constructor. } naive_solver. }
    2: done. move => [??] [??]; simplify_eq/=.
    apply: STraceStep. { econstructor. { apply ProductStepBoth; constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.

    have {}H := (H3 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.
    apply: STraceStep. { econstructor. { apply ProductStepR. constructor. } naive_solver. }
    2: naive_solver. move => [??] [??]; simplify_eq/=.
    have {}H := (H5 _ ltac:(naive_solver)).
    inversion H; simplify_eq. 1: by apply: STraceEnd.
    invert_all @m_step => //.
Qed.

Lemma prod_mod1_not_refines_prod_mod':
  ¬ srefines (MS prod_mod1 0) (MS prod_mod' (0, 0)).
Proof.
  move => [/=Hr].
  feed pose proof (Hr (λ κs, κs = [] ∨ κs = [Vis 1] ∨ κs = [Vis 1; Vis 3] ∨ κs = [Vis 1; Vis 3; Nb] ∨
                             κs = [Vis 2] ∨ κs = [Vis 2; Vis 4] ∨ κs = [Vis 2; Vis 4; Nb])) as Hr'.
  - apply: STraceStep. { constructor. } 2: naive_solver.
    move => /= ? [?|?]; simplify_eq.
    + apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceEnd; [done|]. naive_solver.
    + apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceStep. { constructor. } 2: naive_solver.
      move => /= ??; simplify_eq.
      apply: STraceEnd; [done|]. naive_solver.
  - inversion Hr'; simplify_eq. 1: naive_solver.
    invert_all @m_step. 1,2: naive_solver.
    have ? : κ = None by naive_solver. subst κ. clear H3 H1 Hr Hr'.
    have {}H := (H0 (_, _) ltac:(naive_solver)).
    inversion H; simplify_eq. 1: naive_solver.
    invert_all @m_step => //. 3: naive_solver.
    (* This should work by passing the opposite of the demonic choice
    to the angelic choice but has many case distinctions *)
Abort.
End test3.

Inductive mod_product_rel1 {EV1 EV2} (m2 : module EV2) : list (event EV1) → m2.(m_state) → list (event (option EV1 * option EV2)) → Prop :=
|MPR1_nil σ:
   mod_product_rel1 m2 [] σ []
|MPR1_nb σ:
   mod_product_rel1 m2 [Nb] σ [Nb]
.

Lemma mod_product_to_mod_1 {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ Pκs:
  σ ~{ mod_product m1 m2, Pκs }~>ₛ Pσ →
  σ.1 ~{ m1, λ κs, ∃ κs', mod_product_rel1 m2 κs σ.2 κs' ∧ Pκs κs' }~>ₛ (λ _, True).
Proof.
  elim.
  - move => ????[??]. apply: STraceEnd; [done|]. split; eexists _; (split; [constructor|done]).
  - move => [??]???? Hstep ? IH [He1 He2].
    inversion Hstep; simplify_eq.
    + apply: STraceStep; [done| |].
      * move => ??. apply: shas_trace_mono; [ by apply: (IH (_, _)) | |done].
        move => /=? [?[??]]. eexists _. split; [|done]. destruct e => //=.
        admit.
      * split; eexists _; split; [| apply: He1 | | apply: He2] => /=.
        -- constructor.
        -- admit.
    + apply: shas_trace_mono; [ apply: (IH (_, _)) | |done].
Abort.


Inductive mod_product_rel2 {EV1 EV2} : ((list (event (option EV1 * option EV2))) → Prop) → (list (event EV1) → Prop) → (list (event EV2) → Prop) → Prop :=.
(*
| MPR_nil κs :
    tnil ⊆ κs →
    mod_product_rel κs tnil tnil
| MPR_ex1 T f κs κs2 :
    (∀ x, mod_product_rel κs (f x) κs2) →
    mod_product_rel κs (tex T f) κs2
| MPR_ex2 T f κs κs2 :
    (∀ x, mod_product_rel κs κs2 (f x)) →
    mod_product_rel κs κs2 (tex T f)
| MPR_all1 {T} x f κs κs2 F :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T F f) κs2
| MPR_all2 {T} x f κs κs2 F :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T F f)
| MPR_all T f κs κs1 κs2 F:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T F f) ⊆ κs →
    mod_product_rel κs κs1 κs2
| MPR_cons_l κ κs κs' κs1' κs2 :
    mod_product_rel κs' κs1' κs2 →
    tcons (Some κ, None) κs' ⊆ κs →
    mod_product_rel κs (tcons κ κs1') κs2
| MPR_cons_r κ κs κs' κs1 κs2' :
    mod_product_rel κs' κs1 κs2' →
    tcons (None, Some κ) κs' ⊆ κs →
    mod_product_rel κs κs1 (tcons κ κs2')
| MPR_cons_both κ1 κ2 κs κs' κs1' κs2' :
    mod_product_rel κs' κs1' κs2' →
    tcons (Some κ1, Some κ2) κs' ⊆ κs →
    mod_product_rel κs (tcons κ1 κs1') (tcons κ2 κs2')
.
*)

Lemma mod_product_to_mods {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ κs:
  σ ~{ mod_product m1 m2, κs }~>ₛ Pσ → ∃ κs', mod_product_rel2 κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~>ₛ (λ _, True) ∧ σ.2 ~{ m2, κs'.2 }~>ₛ (λ _, True).
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (_, _) => /=.
    split_and!.
    + admit.
    + apply: STraceEnd; [done| ]. admit.
    + apply: STraceEnd; [done| ]. admit.
  - move => [σ1 σ2] ???? Hstep _ IH [??].
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have {IH}[f Hf]:= CHOICE IH.
      eexists (
          (λ κs, κs = [] ∨ κs = option_list (Vis <$> e) ∨ ∃ κs', κs = (option_list (Vis <$> e)) ++ κs' ∧ ∃ x, (f x).1 κs')
          , (λ κs, ∀ x, (f x).2 κs)) => /=.
      split_and!.
      * admit.
      * apply: STraceStep; [done| |naive_solver]. move => ??.
        apply: shas_trace_mono; [naive_solver| |done] => /=.
        move => ??. naive_solver.
      * have [[[??]?]|?]:= EM (∃ x, ∀ κs, (f x).2 κs → ∀ x', (f x').2 κs).
        -- apply: shas_trace_mono; [naive_solver| |done] => /=. done.
        -- apply: STraceEnd. done.
           split. admit.
           move => [??].
Admitted.

(*** trefines for [product] *)
Inductive mod_product_rel {EV1 EV2} : trace (option EV1 * option EV2) → trace EV1 → trace EV2 → Prop :=
| MPR_nil κs :
    tnil ⊆ κs →
    mod_product_rel κs tnil tnil
| MPR_ex1 T f κs κs2 :
    (∀ x, mod_product_rel κs (f x) κs2) →
    mod_product_rel κs (tex T f) κs2
| MPR_ex2 T f κs κs2 :
    (∀ x, mod_product_rel κs κs2 (f x)) →
    mod_product_rel κs κs2 (tex T f)
| MPR_all1 {T} x f κs κs2 :
    mod_product_rel κs (f x) κs2 →
    mod_product_rel κs (tall T f) κs2
| MPR_all2 {T} x f κs κs2 :
    mod_product_rel κs κs2 (f x) →
    mod_product_rel κs κs2 (tall T f)
| MPR_all T f κs κs1 κs2:
    (∀ x, mod_product_rel (f x) κs1 κs2) →
    (tall T f) ⊆ κs →
    mod_product_rel κs κs1 κs2
| MPR_cons_l κ κs κs' κs1' κs2 :
    mod_product_rel κs' κs1' κs2 →
    tcons (Some κ, None) κs' ⊆ κs →
    mod_product_rel κs (tcons κ κs1') κs2
| MPR_cons_r κ κs κs' κs1 κs2' :
    mod_product_rel κs' κs1 κs2' →
    tcons (None, Some κ) κs' ⊆ κs →
    mod_product_rel κs κs1 (tcons κ κs2')
| MPR_cons_both κ1 κ2 κs κs' κs1' κs2' :
    mod_product_rel κs' κs1' κs2' →
    tcons (Some κ1, Some κ2) κs' ⊆ κs →
    mod_product_rel κs (tcons κ1 κs1') (tcons κ2 κs2')
.


Lemma mod_product_rel_mono {EV1 EV2} κs κs' (κs1 : trace EV1) (κs2 : trace EV2) :
  mod_product_rel κs κs1 κs2 →
  κs ⊆ κs' →
  mod_product_rel κs' κs1 κs2.
Proof.
  move => Ht.
  elim: Ht κs'.
  - move => ????. constructor. by etrans.
  - move => *. constructor. naive_solver.
  - move => *. constructor. naive_solver.
  - move => *. econstructor. naive_solver.
  - move => *. econstructor; naive_solver.
  - move => *. eapply MPR_all. 2: by etrans. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_l; [| by etrans]. naive_solver.
  - move => ????? ?? IH ??.
    apply: MPR_cons_r; [| by etrans]. naive_solver.
  - move => *.
    apply: MPR_cons_both; [| by etrans]. naive_solver.
Qed.


Lemma tmod_product_to_mods {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ Pσ κs:
  σ ~{ mod_product m1 m2, κs }~>ₜ Pσ → ∃ κs', mod_product_rel κs κs'.1 κs'.2 ∧
    σ.1 ~{ m1, κs'.1 }~>ₜ (λ _, True) ∧ σ.2 ~{ m2, κs'.2 }~>ₜ (λ _, True).
Proof.
  elim.
  - move => [σ1 σ2] ????. eexists (tnil, tnil) => /=.
    split_and!.
    + apply: mod_product_rel_mono; [|done]. by constructor.
    + by constructor.
    + by constructor.
  - move => [σ1 σ2] ????? Hstep _ IH ?.
    inversion Hstep; simplify_eq.
    + have {}IH := IH (_, σ2) (conj _ ltac:(exact (eq_refl σ2))).
      have [f Hf]:= CHOICE IH.
      unshelve eexists (tapp (option_trace e) (tex _ (λ x, (f x).1)), (tall _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_l; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (σ1, _) (conj ltac:(exact (eq_refl σ1)) _).
      have [f Hf]:= CHOICE IH.
      unshelve eexists ((tall _ (λ x, (f x).1)), tapp (option_trace e) (tex _ (λ x, (f x).2))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done].
         destruct e => //=.
         ++ apply: MPR_cons_r; [|done].
            constructor => -[??]. econstructor.
            naive_solver.
         ++ constructor => -[??]. econstructor. naive_solver.
      -- apply: thas_trace_all => -[??].
         apply: thas_trace_mono. naive_solver. done. naive_solver.
      -- apply: TTraceStep; [ done | | done].
         move => σ' Hσ'. apply: (thas_trace_ex (exist _ σ' Hσ')).
         apply: thas_trace_mono. naive_solver. done. naive_solver.
    + have {}IH := IH (_, _) (conj _ _).
      have [f Hf]:= CHOICE2 IH.
      unshelve eexists (tcons e1 (tex _ (λ x1, (tall _ (λ x2, (f x1 x2).1)))),
                        tcons e2 (tex _ (λ x2, (tall _ (λ x1, (f x1 x2).2))))) => /=.
      split_and!.
      -- apply: mod_product_rel_mono; [|done]. simpl.
         econstructor; [|done..].
         constructor => -[??].
         constructor => -[??].
         econstructor.
         econstructor. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
      -- apply: TTraceStep; [ done | | simpl; done].
         move => ??.
         apply: thas_trace_ex. apply: thas_trace_all => -[??]. naive_solver.
  - move => T f ???? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall T (λ x, (fx x).1), tall T (λ x, (fx x).2)) => /=.
    split_and! => //.
    -- apply: mod_product_rel_mono; [|done].
       eapply MPR_all; [|done] => ?.
       econstructor. econstructor. naive_solver.
    -- apply: thas_trace_all. naive_solver.
    -- apply: thas_trace_all. naive_solver.
       Unshelve. done. done.
Qed.

Lemma mod_product_nil_l {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ1 ~{ m1, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.1 ∧ σ2 = σ'.2).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepL | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma mod_product_nil_r {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ1 σ2 Pσ κs:
  σ2 ~{ m2, κs }~>ₜ Pσ → κs ⊆ tnil →
  (σ1, σ2) ~{ mod_product m1 m2, tnil }~>ₜ (λ σ', Pσ σ'.2 ∧ σ1 = σ'.1).
Proof.
  elim.
  - move => ??????. constructor; [|done]. naive_solver.
  - move => ??? κ ????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as Hs.
    destruct κ; [inversion Hs|]; simplify_eq/=.
    apply: TTraceStep; [ by apply: ProductStepR | | simpl;done].
    move => [??] /=. naive_solver.
  - move => ??????? Hs1 Hs2.
    pose proof (transitivity Hs1 Hs2) as [??]%subtrace_all_nil_inv. naive_solver.
Qed.

Lemma tmods_to_mod_product {EV1 EV2} (m1 : module EV1) (m2 : module EV2) σ κs κs1 κs2:
  mod_product_rel κs κs1 κs2 →
  σ.1 ~{ m1, κs1 }~>ₜ (λ _, True) → σ.2 ~{ m2, κs2 }~>ₜ (λ _, True) →
  σ ~{ mod_product m1 m2, κs }~>ₜ (λ _, True).
Proof.
  move => Hrel.
  elim: Hrel σ.
  - move => ?????. by constructor.
  - move => ????? /= IH [??] /thas_trace_ex_inv ??.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ????? IH [??] ? /thas_trace_ex_inv ?.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => [??] /= [[??]?]. naive_solver.
  - move => ?????? IH ? /thas_trace_all_inv ??. apply: IH; [|done]. naive_solver.
  - move => ?????? IH ?? /thas_trace_all_inv ?. apply: IH; [done|]. naive_solver.
  - move => ?????? IH ????.
    apply: thas_trace_mono; [|done| done].
    apply: thas_trace_all => ?. naive_solver.
  - move => ?????? IH ? [??]/= /(thas_trace_cons_inv _ _) ??.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepL |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ?????? IH ? [??]/=? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepR |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
  - move => ??????? IH ? [??]/= /(thas_trace_cons_inv _ _)? /(thas_trace_cons_inv _ _)?.
    apply: thas_trace_mono; [|done| done].
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_l. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: (thas_trace_trans tnil). { by apply: mod_product_nil_r. }
    move => /= [??] /= [[?[??]]?]. subst.
    apply: TTraceStep; [ by apply: ProductStepBoth |  | simpl;done].
    move => [??] /= [??]. subst. naive_solver.
Qed.

Lemma mod_product_trefines {EV1 EV2} (m1 m1' : module EV1) (m2 m2' : module EV2) σ1 σ1' σ2 σ2':
  trefines (MS m1 σ1) (MS m1' σ1') →
  trefines (MS m2 σ2) (MS m2' σ2') →
  trefines (MS (mod_product m1 m2) (σ1, σ2)) (MS (mod_product m1' m2') (σ1', σ2')).
Proof.
  move => [/=Hr1] [/=Hr2]. constructor => κs /= /tmod_product_to_mods[κs1 [κs2 [/Hr1 ? /Hr2 ?]]].
  by apply: tmods_to_mod_product.
Qed.


(*** Proving refinement *)

(** ** [inv] *)
Lemma inv_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → Prop):
  inv m1.(ms_state) m2.(ms_state) →
  (∀ σi1 σs1 Pσi2 e,
      inv σi1 σs1 → m_step m1 σi1 e Pσi2 →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) Hinvinit => σi1 σs1 Hinv Hsteps.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ Hinv Hstep).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ??????????.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

Lemma inv'_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop):
  (∀ κs, ms_state m1 ~{ m1, κs }~>ₜ (λ _, True) → inv m1.(ms_state) m2.(ms_state) κs) →
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) →
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)) →
  trefines m1 m2.
Proof.
  move => Hinvinit Hinvstep Hinvall.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) (Hinvinit κs) => σi1 σs1 Hinv Hsteps.
  move: (Hinv Hsteps) => {}Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ _ _ Hinv Hstep Hcons).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ?????? IH ???.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.

Lemma trefines_implies_inv' {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 →
  ∃ (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop),
  (∀ κs, ms_state m1 ~{ m1, κs }~>ₜ (λ _, True) → inv m1.(ms_state) m2.(ms_state) κs) ∧
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) ∧
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)).
Proof.
  move => [Hr].
  eexists (λ σi σs κs, σs ~{ m2, κs }~>ₜ (λ _, True)).
  split_and!.
  - done.
  - move => {Hr} ?????????.  admit.
  - admit.
Abort.

Lemma inv''_implies_trefines {EV} (m1 m2 : mod_state EV) (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop):
  (∀ κs, inv m1.(ms_state) m2.(ms_state) κs) →
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) →
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)) →
  trefines m1 m2.
Proof. Abort.
(*
  move => Hinvinit Hinvstep Hinvall.
  constructor => // κs. move: m1.(ms_state) m2.(ms_state) (Hinvinit κs) => σi1 σs1 Hinv Hsteps.
  move: (Hinv Hsteps) => {}Hinv.
  elim: Hsteps σs1 Hinv => {σi1 κs}.
  - move => ???????. by constructor.
  - move => σi1 Pσi2 Pσi3 κ κs κs' Hstep Hsteps IH Hcons σs1 Hinv.
    have ?:= (Hinvstep _ _ _ _ _ _ Hinv Hstep Hcons).
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_trans; [done|] => ? /=[?[??]].
    by apply: IH.
  - move => ?????? IH ???.
    apply: thas_trace_mono; [|done|done].
    apply: thas_trace_all => ?. naive_solver.
Qed.
 *)
(*
Lemma trefines_implies_inv'' {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 →
  ∃ (inv : m1.(m_state) → m2.(m_state) → trace EV → Prop),
  (∀ κs, inv m1.(ms_state) m2.(ms_state) κs) ∧
  (∀ σi1 σs1 Pσi2 e κs κs',
      inv σi1 σs1 κs → m_step m1 σi1 e Pσi2 → tapp (option_trace e) κs' ⊆ κs →
      σs1 ~{ m2, option_trace e }~>ₜ (λ σs2, ∃ σi2, Pσi2 σi2 ∧ inv σi2 σs2 κs')) ∧
  (∀ σi1 σs1 κs T f,
      inv σi1 σs1 κs → tall T f ⊆ κs → ∀ x, inv σi1 σs1 (f x)).
Proof.
  move => [Hr].
  eexists (λ σi σs κs, σs ~{ m2, κs }~>ₜ (λ _, True)).
  split_and!.
  - done.
  - move => {Hr} ?????????.  admit.
  - admit.
Abort.
*)

Lemma forall_to_ex1 A B (P1 : A → Prop)  P2 (Q : B → Prop):
 (∃ n : A, P1 n ∧ (∀ y, P2 n y → Q y)) -> (∀ y, (∀ n : A, P1 n → P2 n y) → Q y).
Proof. naive_solver. Qed.

Lemma trefines_implies_trefines {EV} (m1 m2 : mod_state EV):
  trefines m1 m2 → trefines m1 m2.
Proof.
  move => [/=Hr]. constructor => κs Ht.
  move: Hr. move: (ms_state m1) (ms_state m2) Ht => σ1 σ2 Ht.
  move: σ2. apply: forall_to_ex1.
  elim: Ht.
  - move => ?????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ??. by apply: TTraceEnd.
  - move => ??? κ ?? Hstep ? IH ?.
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace κ) (tex _ f)). split.
    + apply: TTraceStep; [done| |done]. move => ??. apply: thas_trace_ex. naive_solver.
    + move => σ2. destruct κ; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _) Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [?[? {}Ht]].
        apply: thas_trace_mono; [|done|done].
        apply: TTraceStep; [done | |simpl; done]. move => ??.
        have /thas_trace_ex_inv{}Ht := Ht _ ltac:(done).
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done| ]. naive_solver. done.
      * move => /thas_trace_ex_inv Ht.
        apply: (thas_trace_trans tnil); [done|] => ? [[??]?].
        apply: thas_trace_mono; [|done|done]. naive_solver.
  - move => ?????? IH ?.
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. done.
Qed.

Lemma forall_to_ex2 A B1 B2 (P1 : A → Prop)  P2 (Q : B1 → B2 → Prop) R:
 (∃ n : A, P1 n ∧ (∀ y1 y2, R y1 y2 → P2 n y1 y2 → Q y1 y2)) -> (∀ y1 y2, R y1 y2 → (∀ n : A, P1 n → P2 n y1 y2) → Q y1 y2).
Proof. naive_solver. Qed.

Lemma trefines1_implies_trefines2 {EV1 EV2} (mi1 ms1 : mod_state EV1) (mi2 ms2 : mod_state EV2)
      (iinv : mi1.(m_state) → mi2.(m_state) → Prop)
      (sinv : ms1.(m_state) → ms2.(m_state) → Prop):
  trefines mi1 ms1 →
  iinv mi1.(ms_state) mi2.(ms_state) →
  sinv ms1.(ms_state) ms2.(ms_state) →
  (∀ σ1 σ2 κ Pσ2, iinv σ1 σ2 → m_step mi2 σ2 κ Pσ2 → ∃ κ',
    (if κ' is Some e then
       ∀ σs1 σs2 Pσs1, sinv σs1 σs2 → m_step ms1 σs1 κ' Pσs1 →
          σs2 ~{ ms2, option_trace κ }~>ₜ (λ σs2', ∃ σs1', Pσs1 σs1' ∧ sinv σs1' σs2')
     else κ = None) ∧
       σ1 ~{ mi1, option_trace κ' }~>ₜ (λ σ1', ∃ σ2', Pσ2 σ2' ∧ iinv σ1' σ2')) →
  (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → m_step ms1 σ1 None Pσ1 →
                σ2 ~{ ms2, tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')) →
  trefines mi2 ms2.
Proof.
  move => [/=Hr] Hiinvinit Hsinvinit Histep Hsnil.
  have {}Hsnil: (∀ σ1 σ2 Pσ1, sinv σ1 σ2 → σ1 ~{ ms1, tnil }~>ₜ Pσ1 →
                σ2 ~{ ms2, tnil }~>ₜ (λ σ2', ∃ σ1', Pσ1 σ1' ∧ sinv σ1' σ2')). {
    clear -Hsnil.
    move => σ1 σ2 Pσ1 Hsinv /thas_trace_nil_inv.
    have : @tnil EV1 ⊆ tnil by done. move: {1 3}(@tnil EV1) => κs Hκs Ht.
    elim: Ht σ2 Hsinv Hκs.
    - move => ????????. apply: TTraceEnd; naive_solver.
    - move => ??? κ ?? Hstep ? IH Hs1 ?? Hs2.
      pose proof (transitivity Hs1 Hs2) as Hs. destruct κ; simplify_eq/=; [easy| ].
      move: Hstep => /Hsnil {}Hstep.
      apply: (thas_trace_trans tnil); naive_solver.
  }
  constructor => κs Ht. move: Hiinvinit Hsinvinit Hr.
  move: (ms_state mi1) (ms_state mi2) (ms_state ms1) (ms_state ms2) Ht => σi1 σi2 σs1 σs2 Ht Hiinit Hsinit.
  move: σs1 σs2 Hsinit. apply: forall_to_ex2.
  elim: Ht σi1 Hiinit.
  - move => ???????. eexists tnil. split; [ by apply: TTraceEnd|]. move => ????. by apply: TTraceEnd.
  - move => ? Pσ2 ? κ ? κs' Hstep ? IH ? ? Hiinv.
    have [κ' [Hsend Hsteps]]:= Histep _ _ _ _ Hiinv Hstep.
    have {}IH : ∀ σi1, (∃ σ2', Pσ2 σ2' ∧ iinv σi1 σ2') → ∃ n, σi1 ~{ mi1, n }~>ₜ (λ _, True) ∧
       (∀ y1 y2, sinv y1 y2 → y1 ~{ ms1, n }~>ₜ (λ _, True) → y2 ~{ ms2, κs' }~>ₜ (λ _, True)).
    { move => ?. naive_solver. }
    have [f Hf]:= CHOICE IH.
    eexists (tapp (option_trace κ') (tex _ f)). split.
    + apply: thas_trace_trans; [done| ] => ?[?[??]].
      apply: thas_trace_ex. naive_solver.
    + move => σs1 σs2 ? /thas_trace_app_inv Happ.
      apply: (thas_trace_mono _ _ (λ _, True)); [|done|done].
      move: Happ. destruct κ'; simplify_eq/=.
      * move => /(thas_trace_cons_inv _ _)/Hsnil Ht.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => {Ht} ? [? [[?[? HP]]?]].
        apply: thas_trace_trans; [naive_solver|].
        move => ?[?[??]].
        have /Hsnil ?:= HP _ ltac:(done).
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[/thas_trace_ex_inv/Hsnil??]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ?[?[[[?[?[??]]]?]?]].
        naive_solver.
      * move => /Hsnil Hs.
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [? [/thas_trace_ex_inv/Hsnil? ?]].
        apply: (thas_trace_trans tnil); [naive_solver|].
        move => ? [?[[[?[?[??]]]?]?]]. naive_solver.
  - move => ?????? IH ???.
    have {}IH := (IH _ _ ltac:(done)).
    have [fx Hfx]:= AxCHOICE _ _ _ IH.
    eexists (tall _ (λ x, fx x)). split.
    + apply: thas_trace_all. naive_solver.
    + move => ??? /thas_trace_all_inv ?. apply: thas_trace_mono; [|done|done].
      apply: thas_trace_all. naive_solver.
      Unshelve. all: naive_solver.
Qed.

Lemma tmod_filter_refines' {EV1 EV2} (R : EV1 → option EV2 → Prop) mi ms σi σs:
  trefines (MS mi σi) (MS ms σs) →
  trefines (MS (mod_filter mi R) σi) (MS (mod_filter ms R) σs).
Proof.
  move => Hr. eapply (trefines1_implies_trefines2 (MS mi _) (MS ms _) (MS (mod_filter mi R) _) (MS (mod_filter ms R) _) (λ σ1 σ2, σ1 = σ2) (λ σ1 σ2, σ1 = σ2)); [done.. | |] => /=.
  - move => ???? -> Hstep. inversion Hstep; simplify_eq. eexists e.
    split.
    + case_match; simplify_eq => //.
      move => ??? -> ?. apply: TTraceStep; [| |by erewrite tapp_tnil_r].
      { econstructor; [done| simpl; done]. }
      move => ??. apply: TTraceEnd; naive_solver.
    + apply: TTraceStep; [done| |by erewrite tapp_tnil_r].
      move => ??. apply: TTraceEnd; [|done]. naive_solver.
  - move => ??? -> ?.
    apply: TTraceStep; [by econstructor| |simpl; done].
    move => ??. apply: TTraceEnd; [|done]. naive_solver.
Qed.
