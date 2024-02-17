From iris.bi Require Import fixpoint.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export fancy_updates.
From dimsum.core Require Export module trefines.
From dimsum.core.iris Require Export ord_later.
Set Default Proof Using "Type".

(** * dimsumGS *)
Class dimsumPreG (Σ : gFunctors) := DimsumPreG {
  dimsum_pre_invG :: invGpreS Σ;
  dimsum_pre_ord_laterG :: ord_laterPreG Σ;
}.

Class dimsumGS (Σ : gFunctors) := DimsumGS {
  dimsum_invGS :: invGS_gen HasNoLc Σ;
  dimsum_ord_laterGS :: ord_laterGS Σ;
}.
Global Opaque dimsum_invGS.

Definition dimsumΣ : gFunctors :=
  #[ ord_laterΣ; invΣ ].

Global Instance subG_dimsumΣ Σ :
  subG (dimsumΣ) Σ → dimsumPreG Σ.
Proof. solve_inG. Qed.

(** * [tgt_src] *)
Inductive tgt_src := | Tgt | Src.

Definition is_tgt (ts : tgt_src) : bool := if ts is Tgt then true else false.
Definition is_src (ts : tgt_src) : bool := if ts is Src then true else false.

Notation "▷ₒ? b P" := (if (b : bool) then ord_later P else P%I) (at level 20, b at level 9, P at level 20, format "▷ₒ? b  P") : bi_scope.

Global Instance elim_modal_ord_later_maybe `{!ord_laterGS Σ} b p P Q :
  ElimModal True p false (▷ₒ?b P) P (▷ₒ?b Q) Q.
Proof.
  rewrite /ElimModal bi.intuitionistically_if_elim.
  iIntros (?) "[? HQ]". destruct b; [iModIntro|]; by iApply "HQ".
Qed.

Definition ts_ex_all {Σ A} (ts : tgt_src) (P : A → iProp Σ) : iProp Σ :=
  match ts with | Tgt => ∃ x, P x | Src => ∀ x, P x end.
Definition ts_all_ex {Σ A} (ts : tgt_src) (P : A → iProp Σ) : iProp Σ :=
  match ts with | Tgt => ∀ x, P x | Src => ∃ x, P x end.
Definition ts_star_wand {Σ} (ts : tgt_src) (P1 P2 : iProp Σ) : iProp Σ :=
  match ts with | Tgt => P1 ∗ P2 | Src => P1 -∗ P2 end.
Definition ts_wand_star {Σ} (ts : tgt_src) (P1 P2 : iProp Σ) : iProp Σ :=
  match ts with | Tgt => P1 -∗ P2 | Src => P1 ∗ P2 end.

(* Notation "'ts_ex_allx'" := (ts_ex_all ltac:(assumption)) (only parsing). *)
(* Notation "'∃∀' x , P" := (ts_ex_all ltac:(assumption) (λ x, P)) *)
    (* (at level 100, x binder, P at level 100, right associativity, only parsing) : bi_scope. *)
Notation "'∃/∀{' ts '}' x .. y , P" := (ts_ex_all ts (λ x, .. (ts_ex_all ts (λ y, P)) ..))
    (at level 100, x binder, y binder, P at level 100, right associativity,
        format "'[' '∃/∀{' ts '}'  x  ..  y , ']'  '/' P") : bi_scope.
Notation "'∀/∃{' ts '}' x .. y , P" := (ts_all_ex ts (λ x, .. (ts_all_ex ts (λ y, P)) ..))
    (at level 100, x binder, y binder, P at level 100, right associativity,
        format "'[' '∀/∃{' ts '}'  x  ..  y , ']'  '/' P") : bi_scope.

Notation "P '∗/-∗{' ts '}' Q" := (ts_star_wand ts P Q)
   (at level 80, right associativity, format "P  '∗/-∗{' ts '}'  '/' Q").
Notation "P '-∗/∗{' ts '}' Q" := (ts_wand_star ts P Q)
   (at level 80, right associativity, format "P  '-∗/∗{' ts '}'  '/' Q").


Section tgt_src.
  Context {Σ : gFunctors} `{!dimsumGS Σ}.
  Context {EV : Type}.

  Definition ts_step (ts : tgt_src) (m : mod_trans EV) (σ : m.(m_state))
    (Φ : option EV → m.(m_state) → iProp Σ) : iProp Σ :=
    ∀/∃{ts} κ Pσ, ⌜m.(m_step) σ κ Pσ⌝ -∗/∗{ts} |={∅}=> ∃/∀{ts} σ', ⌜Pσ σ'⌝ ∗/-∗{ts} Φ κ σ'.

  Global Instance ts_step_ne ts m σ n:
    Proper ((pointwise_relation _ (pointwise_relation _ (dist n))) ==> dist n) (ts_step ts m σ).
  Proof. destruct ts; solve_proper. Qed.

  Lemma ts_step_wand_strong ts m σ Φ Ψ :
    ts_step ts m σ Φ -∗
    (* TODO: add ={∅}=∗ here? *)
    (∀ κ σ', Φ κ σ' -∗ Ψ κ σ') -∗
    ts_step ts m σ Ψ.
  Proof.
    iIntros "Hd HΦ". destruct ts => /=.
    - iIntros (??) "Ha". iMod ("Hd" with "Ha") as (?) "[??]".
      iDestruct ("HΦ" with "[$]") as "HΦ". iModIntro. iExists _. iFrame.
    - iDestruct "Hd" as (??) "[? Hb]". iExists _, _. iFrame.
      iMod "Hb". iModIntro. iIntros (b) "Ha". iDestruct ("Hb" with "Ha") as "Hb". by iApply "HΦ".
  Qed.

  Lemma ts_step_wand ts m σ Φ Ψ :
    ts_step ts m σ Φ -∗
    (∀ κ σ', Φ κ σ' -∗ Ψ κ σ') -∗
    ts_step ts m σ Ψ.
  Proof.
    iIntros "? Hwand". iApply (ts_step_wand_strong with "[$]").
    iIntros (??) "?". by iApply "Hwand".
  Qed.
End tgt_src.

(** * [sim_gen] *)
Section sim_gen.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (ts : tgt_src) (m : mod_trans EV).

  (* Technically, this definition is not strong enough for proving
  reflexivity of modules that have angelic and demonic choices in the
  same step (since the angelic choice of the target is before we get
  the angelic choice of the source), but if one has such a module, one
  can refactor it by splitting the step into two steps. (See
  https://gitlab.mpi-sws.org/iris/dimsum/-/blob/7e81d02e63e5fdd7908f805ec1255402d0455076/dimsum/iris/sim.v#L37
  for a definition of the simulation that supports this. Note the
  double continuation passing style.) *)
  Definition sim_gen_pre
    (Π : option EV → iProp Σ → iProp Σ)
    (Φ : m.(m_state) → iProp Σ)
    (sim_gen : leibnizO (m.(m_state)) -d>
               iPropO Σ) :
    leibnizO (m.(m_state)) -d>
    iPropO Σ := λ σ,
  (ord_later_ctx -∗ |={∅}=>
        Φ σ ∨
        Π None (sim_gen σ) ∨
        ts_step ts m σ (λ κ σ', ▷ₒ?(is_tgt ts) |={∅}=>
          if κ is Some _ then Π κ (sim_gen σ') else sim_gen σ'))%I.

  Global Instance sim_gen_pre_ne n Π Φ:
    Proper (dist n ==> dist n ==> dist n) (Π : leibnizO (option EV) -d> iPropO Σ -d> iPropO Σ) →
    Proper ((dist n ==> dist n) ==> dist n ==> dist n) (sim_gen_pre Π Φ).
  Proof.
    move => ? ?? Hsim ?? ->. rewrite /sim_gen_pre.
    repeat (f_equiv || eapply Hsim || reflexivity).
  Qed.
  (* Admitted. *)
    (* unfold dist, ofe_dist in *. simpl in *. unfold discrete_fun_dist, bi_dist in *. simpl. *)
    (* unfold dist, ofe_dist in *. simpl in *. unfold discrete_fun_dist, bi_dist in *. simpl. *)
    (* unfold dist, ofe_dist in *. simpl in *. unfold discrete_fun_dist, bi_dist in *.  *)
    (* eapply HΠ. *)
  (* Qed. *)

  Lemma sim_gen_pre_mono sim1 sim2 Π Φ:
    ⊢ □ (∀ σ, sim1 σ -∗ sim2 σ)
    → ∀ σ, sim_gen_pre Π Φ sim1 σ -∗ sim_gen_pre Π Φ sim2 σ.
  Proof.
    iIntros "#Hinner" (σ) "Hsim ?".
    iMod ("Hsim" with "[$]") as "[?|Hsim]"; [by iLeft; iFrame| iRight; iModIntro].
  Admitted.
    (* iApply (ts_step_wand with "Hsim"). iIntros (??) "Hsim" => /=. *)
    (* iMod "Hsim". case_match => //. by iApply "Hinner". *)
  (* Qed. *)

  Local Instance sim_gen_pre_monotone Π Φ:
    BiMonoPred (λ sim_gen : leibnizO (m.(m_state))-d> iPropO Σ, sim_gen_pre Π Φ sim_gen).
  Proof.
    constructor.
    - iIntros (Φ' Ψ ??) "#Hinner". iIntros (?) "Hsim" => /=. iApply sim_gen_pre_mono; [|done].
      iIntros "!>" (?) "HΠ". by iApply ("Hinner" $! _).
    - move => sim_gen Hsim n σ1 σ2 /= ?.
      apply sim_gen_pre_ne; eauto. admit.
      move => ??? /=. by apply: Hsim.
  Admitted.

  Definition sim_gen : (option EV → iProp Σ → iProp Σ) → (m.(m_state) → iProp Σ) → m.(m_state) → iProp Σ := λ Π Φ,
    bi_least_fixpoint (λ sim_gen : (leibnizO (m.(m_state))) -d> iPropO Σ, (sim_gen_pre Π Φ sim_gen)).

  (* Global Instance sim_gen_ne n: *)
    (* Proper ((=) ==> ((=) ==> (=) ==> dist n) ==> dist n) sim_gen. *)
  (* Proof. move => ?? -> ?? HΠ. unfold sim_gen. f_equiv. intros ??. by apply HΠ. Qed. *)
End sim_gen.

Notation "'SIM{' ts '}' σ @ m , Π {{ Φ } }" := (sim_gen ts m Π Φ%I σ)
  (at level 70, Π, Φ at level 200, only parsing) : bi_scope.

Notation "'SIM{' ts '}' σ @ m , Π {{ σ' , Φ } }" := (sim_gen ts m Π (λ σ', Φ%I) σ)
  (at level 70, Π, Φ at level 200,
    format "'[hv' 'SIM{' ts '}'  σ  '/' @  m ,  Π  {{  '[ ' σ' ,  '/' Φ  ']' } } ']'") : bi_scope.


(* Notation " σ '≈{' ts , m '}≈>' P " := (sim_gen ts m σ P) *)
(*   (at level 70, format "σ  '≈{'  ts ,  m  '}≈>'  P") : bi_scope. *)

(* Notation " σ '≈{' m '}≈>ₜ' P " := (sim_gen Tgt m σ P) *)
(*   (at level 70, format "σ  '≈{'  m  '}≈>ₜ'  P") : bi_scope. *)
(* Notation " σ '≈{' m '}≈>ₛ' P " := (sim_gen Src m σ P) *)
(*   (at level 70, format "σ  '≈{'  m  '}≈>ₛ'  P") : bi_scope. *)

(* Definition sim_gen_mapsto `{!dimsumGS Σ} {EV} (ts : tgt_src) (m : mod_trans EV) (σ : m_state m) *)
(*   (H_s : (option EV → m_state m → iProp Σ) → iProp Σ) : iProp Σ := *)
(*   ∀ Π, H_s Π -∗ σ ≈{ts, m}≈> Π. *)

(* Notation "σ '⤇{' ts , m } P " := (sim_gen_mapsto ts m σ P) *)
(*   (at level 20, only parsing) : bi_scope. *)
(* Notation "σ '⤇{' ts '}' P " := (sim_gen_mapsto ts _ σ P) *)
(*   (at level 20, format "σ  '⤇{' ts '}'  P") : bi_scope. *)

(* Notation "σ '⤇{' m '}ₜ' P " := (sim_gen_mapsto Tgt m σ P) *)
(*   (at level 20, only parsing) : bi_scope. *)
(* Notation "σ '⤇ₜ' P " := (sim_gen_mapsto Tgt _ σ P) *)
(*   (at level 20, format "σ  '⤇ₜ'  P") : bi_scope. *)

(* Notation "σ '⤇{' m '}ₛ' P " := (sim_gen_mapsto Src m σ P) *)
(*   (at level 20, only parsing) : bi_scope. *)
(* Notation "σ '⤇ₛ' P " := (sim_gen_mapsto Src _ σ P) *)
(*   (at level 20, format "σ  '⤇ₛ'  P") : bi_scope. *)

Section sim_gen.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (ts : tgt_src) (m : mod_trans EV).
  Context (Π : option EV → iProp Σ → iProp Σ).
  Context (Φ : m.(m_state) → iProp Σ).

  Local Existing Instance sim_gen_pre_monotone.
  Lemma sim_gen_unfold σ:
    SIM{ts} σ @ m, Π {{ Φ }} ⊣⊢ sim_gen_pre ts m Π Φ (sim_gen ts m Π Φ) σ.
  Proof. rewrite /sim_gen /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_gen_strong_ind (R: leibnizO (m.(m_state)) -d> iPropO Σ):
    NonExpansive R →
    ⊢ (□ ∀ σ, sim_gen_pre ts m Π Φ (λ σ, R σ ∧ SIM{ts} σ @ m, Π {{ Φ }}) σ -∗ R σ)
      -∗ ∀ σ, SIM{ts} σ @ m, Π {{ Φ }} -∗ R σ.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ) "Hsim".
    rewrite {2}/sim_gen.
    iApply (least_fixpoint_ind _ R with "[] Hsim").
    iIntros "!>" (?) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_gen_ind (R: leibnizO (m.(m_state)) -d> iPropO Σ) :
    NonExpansive R →
    ⊢ (□ ∀ σ, sim_gen_pre ts m Π Φ R σ -∗ R σ)
      -∗ ∀ σ, SIM{ts} σ @ m, Π {{ Φ }} -∗ R σ.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_gen_strong_ind. iIntros "!>" (σ) "Hsim".
    iApply "HPre". iApply (sim_gen_pre_mono with "[] Hsim").
    iIntros "!>" (?) "[? _]". by iFrame.
  Qed.

(*
  Lemma sim_gen_wand_strong σ Π Ψ:
    σ ≈{ ts, m }≈> Π -∗
    (∀ κ σ, Π κ σ ={∅}=∗ Ψ κ σ) -∗
    σ ≈{ ts, m }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ σ', Ψ κ σ' ={∅}=∗ Π κ σ') -∗ σ ≈{ ts, m }≈> Π)%I).
    iAssert (∀ Π, σ ≈{ ts, m }≈> Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_unfold. iIntros "?".
    iMod ("Hsim" with "[$]") as "[?|Hsim]"; [iLeft| iRight].
    - iMod ("Hc" with "[$]") as "$". done.
    - iModIntro. iApply (ts_step_wand with "Hsim").
      iIntros (??) "Hsim". iMod "Hsim" as "Hsim". iMod "Hsim" as "Hsim".
      case_match.
      + by iMod ("Hc" with "[$]").
      + iModIntro. by iApply "Hsim".
  Qed.

  Lemma sim_gen_wand σ Π Ψ:
    σ ≈{ ts, m }≈> Π -∗
    (∀ κ σ, Π κ σ -∗ Ψ κ σ) -∗
    σ ≈{ ts, m }≈> Ψ.
  Proof.
    iIntros "Hsim Hwand".
    iApply (sim_gen_wand_strong with "Hsim"). iIntros (??) "?". iModIntro. by iApply "Hwand".
  Qed.
*)
(*
  Lemma sim_gen_bind σ Π :
    σ ≈{ ts, m }≈> (λ κ σ', Π κ σ' ∨ ⌜κ = None⌝ ∗ σ' ≈{ ts, m }≈> Π) -∗
    σ ≈{ ts, m }≈> Π.
  Proof.
    iIntros "HΠ".
    pose (F := (λ σ Ψ, ∀ Π, (∀ κ (σ' : m_state m), Ψ κ σ' -∗ Π κ σ' ∨ ⌜κ = @None EV⌝ ∗ σ' ≈{ ts, m }≈> Π) -∗ σ ≈{ ts, m }≈> Π)%I).
    iAssert (∀ Π, σ ≈{ ts, m }≈> Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "HΠ"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?) "Hc".
    rewrite sim_gen_unfold. iIntros "#?".
    iMod ("Hsim" with "[$]") as "[?|Hsim]".
    - iSpecialize ("Hc" with "[$]"). iDestruct "Hc" as "[$|[_ Hc]]"; [done|].
      rewrite sim_gen_unfold. by iApply "Hc".
    - iModIntro. iRight. iApply (ts_step_wand with "Hsim"). iIntros (? ?) "Hsim /=".
      iMod "Hsim" as "Hsim". iMod "Hsim" as "Hsim".
      case_match.
      + by iDestruct ("Hc" with "[$]") as "[$|[% ?]]".
      + iModIntro. by iApply "Hsim".
  Qed.

  Lemma fupd_sim_gen σ Π :
    (|={∅}=> σ ≈{ ts, m }≈> Π) -∗
    σ ≈{ ts, m }≈> Π.
  Proof. iIntros "Hsim". rewrite sim_gen_unfold. iMod "Hsim". iApply "Hsim". Qed.

  Lemma sim_gen_ctx σ Π :
    (ord_later_ctx -∗ σ ≈{ ts, m }≈> Π) -∗
    σ ≈{ ts, m }≈> Π.
  Proof. iIntros "Hsim". rewrite sim_gen_unfold. iIntros "#?". by iApply "Hsim". Qed.

  Lemma sim_gen_stop σ Π :
    Π None σ -∗
    σ ≈{ ts, m }≈> Π.
  Proof. iIntros "?". rewrite sim_gen_unfold. iIntros "?". iLeft. by iFrame. Qed.

  Lemma sim_gen_step σ Π :
    (ts_step ts m σ (λ κ σ', ▷ₒ?ts |={∅}=> Π κ σ' ∨ ⌜κ = None⌝ ∗ σ' ≈{ ts, m }≈> Π)) -∗
    σ ≈{ ts, m }≈> Π.
  Proof.
    iIntros "HΠ". rewrite sim_gen_unfold.
    iIntros "?". iRight. iModIntro. iApply (ts_step_wand with "HΠ").
    iIntros (? ?) "Hsim". iMod "Hsim". iMod "Hsim". iModIntro.
    iDestruct "Hsim" as "[?|[% ?]]"; case_match => //. by iApply sim_gen_stop.
  Qed.

  Lemma sim_gen_step_end σ Π :
    (ts_step ts m σ (λ κ σ', ▷ₒ?ts |={∅}=> Π κ σ')) -∗
    σ ≈{ ts, m }≈> Π.
  Proof.
    iIntros "HΠ". iApply sim_gen_step.
    iApply (ts_step_wand with "HΠ"). iIntros (??) "HΠ".
    iMod "HΠ". iMod "HΠ". iModIntro. by iLeft.
  Qed.
*)
(*
  Lemma sim_gen_include {EV'} (m' : mod_trans EV') f σ Π Ψ :
    let F := (λ σ' Π', (∀ κ σ, Π' κ σ -∗ Π κ σ) -∗ f σ' ≈{ts, m'}≈> Ψ)%I in
    SIM{ts} σ @ m, Π {{ Φ }} -∗
    (□ ∀ σ Π, sim_gen_pre ts m F σ Π -∗ F σ Π) -∗
    SIM{ts} f σ @ m', Π' {{ Φ' }}.
  Proof.
    iIntros (F) "Hsim #Hrec".
    iAssert (∀ Π, σ ≈{ ts, m }≈> Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). iIntros (??) "?". done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    by iModIntro.
  Qed.
*)
End sim_gen.
(* Global Arguments sim_gen_include {_ _ _ _ _ _}. *)

From dimsum.core Require Import product seq_product state_transform prepost.
From dimsum.core.iris Require Import sat.
(* From dimsum.core.iris Require Export sim. *)
Set Default Proof Using "Type".

(** * map_mod *)

Section map.
  Context {Σ : gFunctors} {EV1 EV2 : Type} {S : Type} `{!dimsumGS Σ}.
  Implicit Types (f : map_mod_fn EV1 EV2 S).

  Axiom cur_f_state : gname → S → iProp Σ.

  Definition map_handler f (γ : gname) (Π : option EV2 → iProp Σ → iProp Σ) :
    option EV1 → iProp Σ → iProp Σ := λ κ C,
      (if κ is Some e then
       ∃ σf, cur_f_state γ σf ∗
         ∀ κ' σf' ok, ⌜f σf e κ' σf' ok⌝ -∗ cur_f_state γ σf' -∗
          Π κ' (⌜ok = true⌝ ∗ C)
      else
        Π None C)%I.

  Definition map_post (m : mod_trans EV1) f γ (Φ : (map_trans m f).(m_state) → iProp Σ) :
    m.(m_state) → iProp Σ := λ σ,
      (∃ σf, cur_f_state γ σf ∗ Φ (σ, (σf, true)))%I.

  Lemma sim_tgt_map m f σ σf Π Φ :
    (∀ γ, cur_f_state γ σf -∗ SIM{Tgt} σ @ m, (map_handler f γ Π) {{ map_post m f γ Φ }}) -∗
    SIM{Tgt} (σ, (σf, true)) @ map_trans m f, Π {{ Φ }}.
  Proof.
    iIntros "Hsim".
    iAssert (∃ γ, cur_f_state γ σf ∗ cur_f_state γ σf)%I as (γ) "[Hf1 Hf2]". { admit. }
    iDestruct "Hf1" as "-#Hf1". iDestruct "Hf2" as "-#Hf2".
    iDestruct ("Hsim" with "Hf1") as "Hsim".
Admitted.
(*
    set Π' := (X in (_ ≈{ m }≈>ₜ X)%I).
    iApply (sim_gen_include (map_trans _ _) (λ σ, (σ, (σf, true))) with "Hsim").
    iIntros "!>" (??) "Hsim". iIntros "HΠ".
    iApply (sim_gen_ctx with "[-]"). iIntros "?".
    iApply (fupd_sim_gen with "[-]").
    iMod ("Hsim" with "[$]") as "[HP| Hs]". {
      iModIntro. iApply (sim_gen_stop with "[-]"). by iApply ("HΠ" with "HP").
    }
    iModIntro. iApply (sim_gen_step with "[-]"). iIntros (?? Hstep). inv_all/= @m_step.
    all: iMod ("Hs" with "[//]") as (??) "Hs"; iModIntro; iExists (_, _); iSplit!; [done|].
    all: iModIntro; iMod "Hs"; iModIntro.
    - do 2 case_match; simplify_eq/=. iRight. iSplit!. by iApply "Hs".
    - iLeft. by iApply ("HΠ" with "Hs").
  Qed.
*)
End map.

Section seq_product.
  Context {Σ : gFunctors} {EV1 EV2 : Type} `{!dimsumGS Σ}.

  Definition seq_product_dispatch seq_product_dispatch' (p : option seq_product_side)
    (WPL : (option EV1 → iProp Σ → iProp Σ) → iProp Σ)
    (WPR : (option EV2 → iProp Σ → iProp Σ) → iProp Σ)
    (Π : option (seq_product_event EV1 EV2) → iProp Σ → iProp Σ) : iProp Σ :=
    match p with
    | None =>
        ∀ p', Π (Some (SPENone p')) (seq_product_dispatch' p' WPL WPR Π)
    | Some SPLeft =>
        (* TODO: put the handler in the lemma instead of here? *)
        WPL (λ κ C,
            ∀ s', ⌜if κ is None then s' = Some SPLeft else True⌝ -∗
            Π ((λ e, SPELeft e s') <$> κ) (seq_product_dispatch' s' (λ _, C) WPR Π))
    | Some SPRight =>
        WPR (λ κ C, True%I)
    end%I.

  (* TODO: all this mutual recursion breaks my head... Maybe we keep
  the other version for the combinators and only use the postcondition
  version / inductive version with expressions? *)
  Lemma sim_tgt_seq_product_left seq_product_dispatch'
    (m1 : mod_trans EV1) (m2 : mod_trans EV2) p σ1 σ2 Π Φ :
    seq_product_dispatch seq_product_dispatch'
      p (λ Πl, SIM{Tgt} σ1 @ m1, Πl {{ _, True }}) (λ Πr, SIM{Tgt} σ2 @ m2, Πr {{ _, True }})
      Π
     -∗
    SIM{Tgt} (p, σ1, σ2) @ seq_product_trans m1 m2, Π {{ Φ }}.
  Proof.


(** * [sim_tgt] *)
Section sim_tgt.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).

  Lemma sim_tgt_elim E σ Π κs n m_s σ_s :
    σ ~{m, κs, n}~>ₜ - →
    σ ≈{ m }≈>ₜ Π -∗
    ord_later_auth n -∗
    (∀ κ σ' n' κs', Π κ σ' -∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ -∗ ord_later_auth n' -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
    |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝.
  Proof.
    iIntros (?) "Hsim Ha Hc".
    iDestruct (ord_later_ctx_alloc with "[$]") as "#?".
    pose (F := (λ σ Π,
      ∀ n κs,
        ⌜σ ~{m, κs, n}~>ₜ -⌝ -∗
        ord_later_auth n -∗
        (∀ κ σ' n' κs', Π κ σ' -∗ ⌜σ' ~{m, κs', n'}~>ₜ -⌝ -∗ ord_later_auth n' -∗
           |={E}=> ⌜σ_s ~{m_s, tapp (option_trace κ) κs'}~>ₜ -⌝) -∗
        |={E}=> ⌜σ_s ~{m_s, κs}~>ₜ -⌝)%I).
    iAssert (∀ Π, σ ≈{ m }≈>ₜ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim [//] [$] Hc"). }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { unfold F. solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros (?? Htrace) "Ha Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[$]") as "[HΠ|Hsim]"; iMod "He" as "_".
    { iApply ("Hc" $! None with "[$] [//] [$]"). }
    move: Htrace => /tnhas_trace_inv Htrace.
    iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply: thas_trace_under_tall. }
    iIntros (κs' [[??]|(?&?&?&?&?&?&?&?)]). { iPureIntro. tend. }
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|]. simpl.
    iMod ("Hsim" with "[//]") as (b ?) "Hsim".
    iMod (ord_later_elim with "Hsim Ha [-]"); [|done]. iIntros "Ha".
    iMod (ord_later_update with "Ha"); [shelve|].
    iModIntro. iExists _. iFrame. iSplit; [done|]. iIntros "Ha Hsim". iModIntro => /=.
    iMod "Hsim". iMod "He" as "_". case_match.
    + iMod ("Hc" with "[$] [%] [$]") as %?. 2: { iPureIntro. by apply: thas_trace_mono. }
      apply: tnhas_trace_mono; [by eauto|done|by econs|done].
    + iApply ("Hsim" with "[%] [$] [$]"). simplify_eq/=.
      apply: tnhas_trace_mono; [by eauto|done|by econs|done].
    Unshelve.
    * etrans; [|done]. apply o_le_S.
    * done.
    * done.
  Qed.
End sim_tgt.

(** * [sim_src] *)
Section sim_src.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m : mod_trans EV).

  (* One should be able to get rid of the [HasNoLc] if one uses classical logic. *)
  (* TODO: Is it possible to get a stronger adequacy lemma? *)
  Lemma sim_src_elim E Pσ σ Π κs `{!VisNoAng m} :
    ord_later_ctx -∗
    σ ≈{ m }≈>ₛ Π -∗
    (∀ κ σ', Π κ σ' -∗ ∃ κs', ⌜κs = tapp (option_trace κ) κs'⌝ ∗ |={E}=> ⌜σ' ~{m, κs'}~>ₜ Pσ⌝ ) -∗
    |={E}=> ⌜σ ~{m, κs}~>ₜ Pσ⌝.
  Proof.
    iIntros "#? Hsim HΠ".
    pose (F := (λ σ Π,
      (∀ κ σ', Π κ σ' -∗ ∃ κs', ⌜κs = tapp (option_trace κ) κs'⌝ ∗ |={E}=> ⌜σ' ~{m, κs'}~>ₜ Pσ⌝ ) -∗
        |={E}=> ⌜σ ~{m, κs}~>ₜ Pσ⌝)%I  : _ → _ → iProp Σ).
    iAssert (∀ Π, σ ≈{ m }≈>ₛ Π -∗ F σ Π)%I as "Hgen"; last first.
    { iApply ("Hgen" with "Hsim"). done. }
    iIntros (?) "Hsim".
    iApply (sim_gen_ind with "[] Hsim"). { solve_proper. }
    iIntros "!>" (??) "Hsim". iIntros "Hc".
    iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
    iMod ("Hsim" with "[$]") as "[?|[%κ [% [% Hsim]]]]"; iMod "He" as "_".
    { iDestruct ("Hc" with "[$]") as (??) "?". subst. done. }
    destruct κ; last first; simplify_eq/=.
    - iApply (fupd_mono _ _ ⌜_⌝). { iPureIntro. by apply TTraceStepNone. }
      iIntros (??).
      iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
      iMod ("Hsim" with "[//]") as ">Hsim". iMod "He" as "_".
      by iApply "Hsim".
    - exploit vis_no_all; [done|] => -[??].
      iMod (fupd_mask_subseteq ∅) as "He"; [set_solver|].
      iMod ("Hsim" with "[%]") as ">Hsim"; [naive_solver|]. iMod "He" as "_".
      iDestruct ("Hc" with "[$]") as (?->) ">%". iPureIntro. tstep; [done| |done]. naive_solver.
  Qed.
End sim_src.

(** * [sim] *)
Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m_t m_s : mod_trans EV).

  Definition sim_pre
    (sim : leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ) :
    leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ := λ σ_t σ_s,
      (σ_t ≈{ m_t }≈>ₜ λ κ σ_t', σ_s ≈{ m_s }≈>ₛ λ κ' σ_s', ⌜κ = κ'⌝ ∗ sim σ_t' σ_s')%I.

  Global Instance sim_pre_ne n:
    Proper ((dist n ==> dist n ==> dist n) ==> dist n ==> dist n ==> dist n) sim_pre.
  Proof.
    move => ?? Hsim ?? -> ?? eq. cbv in eq. rewrite eq /sim_pre/bi_mono1.
    f_equiv. move => ?? -> ?? ->.
    f_equiv. move => ?? -> ?? ->.
    repeat (f_equiv || eapply Hsim || eapply HΠ || reflexivity).
  Qed.

  Lemma sim_pre_mono sim1 sim2:
    ⊢ □ (∀ σ_t σ_s, sim1 σ_t σ_s -∗ sim2 σ_t σ_s)
    → ∀ σ_t σ_s , sim_pre sim1 σ_t σ_s -∗ sim_pre sim2 σ_t σ_s.
  Proof.
    iIntros "#Hinner" (σ_t σ_s) "Hsim".
    iApply (sim_gen_wand with "Hsim"). iIntros (??) "Hsim".
    iApply (sim_gen_wand with "Hsim"). iIntros (??) "[% Hsim]".
    iSplit; [done|]. by iApply "Hinner".
  Qed.

  Local Instance sim_pre_monotone :
    BiMonoPred (λ sim : prodO (leibnizO (m_t.(m_state))) (leibnizO (m_s.(m_state))) -d> iPropO Σ, uncurry (sim_pre (curry sim))).
  Proof.
    constructor.
    - iIntros (Π Ψ ??) "#Hinner". iIntros ([??]) "Hsim" => /=. iApply sim_pre_mono; [|done].
      iIntros "!>" (??) "HΠ". by iApply ("Hinner" $! (_, _)).
    - move => sim_src Hsim n [σ_t1 σ_s1] [σ_t2 σ_s2] /= [/=??].
      apply sim_pre_ne; eauto. move => ?????? /=. by apply: Hsim.
  Qed.

  Definition sim : m_t.(m_state) → m_s.(m_state) → iProp Σ :=
    curry (bi_least_fixpoint (λ sim : prodO (leibnizO (m_t.(m_state))) (leibnizO (m_s.(m_state))) -d> iPropO Σ, uncurry (sim_pre (curry sim)))).

  Global Instance sim_ne n:
    Proper ((=) ==> (=) ==> dist n) sim.
  Proof. move => ?? -> ?? ->. unfold sim. f_equiv. Qed.
End sim.

Notation "σ_t ⪯{ m_t , m_s } σ_s" := (sim m_t m_s σ_t σ_s) (at level 70,
    format "σ_t  ⪯{ m_t ,  m_s }  σ_s") : bi_scope.

Section sim.
  Context {Σ : gFunctors} {EV : Type} `{!dimsumGS Σ}.
  Context (m_t m_s : mod_trans EV).

  Local Existing Instance sim_pre_monotone.
  Lemma sim_unfold σ_t σ_s :
    σ_t ⪯{m_t, m_s} σ_s ⊣⊢ sim_pre m_t m_s (sim m_t m_s) σ_t σ_s.
  Proof. rewrite /sim /curry. apply: least_fixpoint_unfold. Qed.

  Lemma sim_strong_ind (R: leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ):
    NonExpansive2 R →
    ⊢ (□ ∀ σ_t σ_s, sim_pre m_t m_s (λ σ_t σ_s, R σ_t σ_s ∧ σ_t ⪯{m_t, m_s} σ_s) σ_t σ_s -∗ R σ_t σ_s)
      -∗ ∀ σ_t σ_s, σ_t ⪯{m_t, m_s} σ_s -∗ R σ_t σ_s.
  Proof.
    iIntros (Hne) "#HPre". iIntros (σ_t σ_s) "Hsim".
    rewrite {2}/sim {1}/curry.
    iApply (least_fixpoint_ind _ (uncurry R) with "[] Hsim").
    iIntros "!>" ([??]) "Hsim" => /=. by iApply "HPre".
  Qed.

  Lemma sim_ind (R: leibnizO (m_t.(m_state)) -d> leibnizO (m_s.(m_state)) -d> iPropO Σ) :
    NonExpansive2 R →
    ⊢ (□ ∀ σ_t σ_s, sim_pre m_t m_s R σ_t σ_s -∗ R σ_t σ_s)
      -∗ ∀ σ_t σ_s, σ_t ⪯{m_t, m_s} σ_s -∗ R σ_t σ_s.
  Proof.
    iIntros (Hne) "#HPre". iApply sim_strong_ind. iIntros "!>" (σ_t σ_s) "Hsim".
    iApply "HPre". iApply (sim_pre_mono with "[] Hsim").
    iIntros "!>" (??) "[? _]". by iFrame.
  Qed.

  Lemma fupd_sim σ_t σ_s :
    (|={∅}=> σ_t ⪯{m_t, m_s} σ_s) -∗
    σ_t ⪯{m_t, m_s} σ_s.
  Proof. iIntros "Hsim". rewrite sim_unfold. by iApply fupd_sim_gen. Qed.

  Lemma sim_ctx σ_t σ_s :
    (ord_later_ctx -∗ σ_t ⪯{m_t, m_s} σ_s) -∗
    σ_t ⪯{m_t, m_s} σ_s.
  Proof. iIntros "Hsim". rewrite sim_unfold. by iApply sim_gen_ctx. Qed.

End sim.

Theorem sim_adequacy Σ EV (m_t m_s : module EV) `{!dimsumPreG Σ} `{!VisNoAng (m_trans m_s)} :
  (∀ `{Hinv : !invGS_gen HasNoLc Σ} `{Hord : !ord_laterGS Σ},
    ⊢ |={⊤}=>
       let _ : dimsumGS Σ := DimsumGS _ _ _
       in
       m_init m_t ⪯{m_trans m_t, m_trans m_s} m_init m_s ) →
  trefines m_t m_s.
Proof.
  intros Hsim. constructor => κs /thas_trace_n [n Htrace].
  eapply uPred.pure_soundness. apply (step_fupdN_soundness_no_lc _ 0 0) => ? /=. simpl in *. iIntros "_".
  iMod (ord_later_alloc n) as (?) "Ha". iDestruct (ord_later_ctx_alloc with "Ha") as "#?".
  iMod Hsim as "Hsim".
  clear Hsim. set (X := DimsumGS _ _ _ : dimsumGS Σ).
  pose (F := (λ σ_t σ_s,
               ∀ n κs,
               ⌜σ_t ~{ m_trans m_t, κs, n }~>ₜ -⌝ -∗
               ord_later_auth n -∗
               |={⊤,∅}=> ⌜σ_s ~{ m_trans m_s, κs }~>ₜ -⌝)%I
          : _ → _ → iProp Σ ).
  iAssert (∀ σ_t σ_s, σ_t ⪯{m_trans m_t, m_trans m_s} σ_s -∗ F σ_t σ_s)%I as "Hgen"; last first. {
    by iApply ("Hgen" with "Hsim").
  }
  clear n κs Htrace. iIntros (σ_t σ_s) "Hsim".
  iApply (sim_ind with "[] Hsim").
  iIntros "!>" (??) "Hsim". iIntros (n κs Htrace) "Ha".
  iApply (fupd_mask_weaken ∅); [set_solver|]. iIntros "He".
  iApply (sim_tgt_elim with "Hsim Ha"); [done|].
  iIntros (????) "Hsim %?".
  iApply (sim_src_elim with "[$] Hsim"). iIntros (??) "[% Hsim]". subst.
  iExists _. iSplit; [done|].
  iMod "He" as "_". iApply ("Hsim" with "[//] [$]").
Qed.
