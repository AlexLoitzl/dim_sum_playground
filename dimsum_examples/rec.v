From dimsum.core Require Export proof_techniques seq_product link prepost.
From dimsum.core Require Import axioms.

Local Open Scope Z_scope.

(** * Rec, a "C-like" language *)
(** ** Provenances and locations *)
Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition block_id := Z.

Inductive prov : Set :=
  ProvBlock (z : block_id) | ProvStatic (f : string) (i : Z).
Definition loc : Set := (prov * Z).

Global Instance prov_eq_dec : EqDecision prov.
Proof. solve_decision. Qed.

Global Instance prov_inhabited : Inhabited prov.
Proof. repeat constructor. Qed.

Global Program Instance prov_countable : Countable prov :=
  inj_countable
    (λ p : prov, match p with | ProvBlock z => inl z | ProvStatic f i => inr (f, i) end)
    (λ q, match q with | inl z => Some (ProvBlock z) | inr (f, i) => Some (ProvStatic f i) end) _.
Next Obligation. by move => []. Qed.

Definition is_ProvBlock (p : prov) := if p is ProvBlock b then True else False.

Global Instance is_ProvBlock_dec (p : prov) : Decision (is_ProvBlock p).
Proof.
  destruct p.
  + by left.
  + right. by intros [].
Defined.

Definition is_ProvStatic (p : prov) := if p is ProvStatic f i then True else False.

Global Instance is_ProvStatic_dec p : Decision (is_ProvStatic p).
Proof.
  destruct p.
  + right. by intros [].
  + by left.
Defined.

Definition prov_to_block (p : prov) : option block_id :=
  if p is ProvBlock b then Some b else None.

(** *** fresh provenances *)
Global Program Instance prov_infinite : Infinite prov :=
  inj_infinite ProvBlock prov_to_block (λ x, eq_refl (Some x)).

Lemma fresh_map_is_Block (s : gset prov) (X : gset prov) i p :
  fresh_map s X !! i = Some p → is_ProvBlock p.
Proof.
  rewrite list_to_map_lookup_Some => [[j [Hj _]]].
  apply lookup_zip_with_Some in Hj as [? [? [[=<-<-] [_ Hfresh]]]].
  induction (length (elements s)) in Hfresh, X, j |-* => //=.
  apply lookup_cons_Some in Hfresh as [[_ <-]|[? Hfresh]].
  - by eexists.
  - by eapply IHn.
Qed.

(** *** Static provenances *)
Definition static_provs {A} (f : string) (svars : list A) : list prov :=
  imap (λ i _, ProvStatic f i) svars.

Definition static_locs {A} f (svars : list A) : list loc := (λ p, (p, 0)) <$> static_provs f svars.

Lemma static_provs_length A f (l : list A) :
  length (static_provs f l) = length l.
Proof. by rewrite /static_provs length_imap. Qed.

Lemma static_provs_lookup A f (svars : list A) (i : nat) :
  static_provs f svars !! i = (λ _ : A, ProvStatic f i) <$> (svars !! i).
Proof. apply list_lookup_imap. Qed.

Lemma static_provs_lookup_Some A f (svars : list A) (i : nat) x :
  static_provs f svars !! i = Some x ↔ x = ProvStatic f i ∧ (i < length svars)%nat.
Proof.
  rewrite static_provs_lookup fmap_Some -lookup_lt_is_Some /is_Some. naive_solver.
Qed.

Definition static_provs_eq {A B} f (svars1 : list A) (svars2 : list B) :
  length svars1 = length svars2 →
  static_provs f svars1 = static_provs f svars2.
Proof.
  move => ?. apply list_eq => i.  apply option_eq => ?.
  rewrite !static_provs_lookup_Some. naive_solver lia.
Qed.

Lemma elem_of_static_provs A p f (svars : list A) :
  p ∈ static_provs f svars ↔ ∃ (i : nat), p = ProvStatic f i ∧ (i < length svars)%nat.
Proof. rewrite elem_of_list_lookup. by setoid_rewrite static_provs_lookup_Some. Qed.

Lemma NoDup_static_provs {A} f (svars : list A) :
  NoDup (static_provs f svars).
Proof.
  apply NoDup_alt => ??? /static_provs_lookup_Some? /static_provs_lookup_Some?.
  naive_solver.
Qed.

Lemma static_provs_snoc {A} f svars (s : A):
  static_provs f (svars ++ [s]) = static_provs f svars ++ [ProvStatic f (length svars)].
Proof. rewrite /static_provs imap_app /=. do 3 f_equal. lia. Qed.

(** *** Locations *)
Definition offset_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (offset_loc l%L z%Z) (at level 50, left associativity) : loc_scope.
Global Typeclasses Opaque offset_loc.

Lemma loc_eq (l1 l2 : loc) :
  l1 = l2 ↔ l1.1 = l2.1 ∧ l1.2 = l2.2.
Proof. destruct l1, l2; naive_solver. Qed.

Lemma offset_loc_0 l :
  l +ₗ 0 = l.
Proof. apply loc_eq. split!. lia. Qed.

Lemma offset_loc_assoc l n1 n2 :
  l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2).
Proof. apply loc_eq. split!. lia. Qed.

Global Instance offset_loc_inj_r l : Inj eq eq (λ i, l +ₗ i).
Proof. move => ??. rewrite /offset_loc /= => ?. simplify_eq. lia. Qed.

Global Instance offset_loc_inj_r2 l i : Inj eq eq (λ j, l +ₗ i +ₗ j).
Proof. move => ??. rewrite /offset_loc /= => ?. simplify_eq. lia. Qed.

Lemma offset_loc_S l i :
  l +ₗ S i = l +ₗ 1 +ₗ i.
Proof. apply loc_eq. split!. lia. Qed.

Lemma offset_loc_add_sub l i j:
  i = - j →
  l +ₗ i +ₗ j = l.
Proof. move => ?. apply loc_eq. split!. lia. Qed.

(** ** Syntax *)
Inductive binop : Set :=
| AddOp | OffsetOp | EqOp | LeOp | LtOp.

Inductive val := | ValNum (z : Z) | ValBool (b : bool) | ValFn (f : string) | ValLoc (l : loc).
Global Instance val_inhabited : Inhabited val := populate (ValNum 0).
Coercion ValNum : Z >-> val.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Qed.

Definition val_to_Z (v : val) : option Z :=
  match v with
  | ValNum z => Some z
  | _ => None
  end.
Definition val_to_bool (v : val) : option bool :=
  match v with
  | ValBool b => Some b
  | _ => None
  end.
Definition val_to_fn (v : val) : option string :=
  match v with
  | ValFn f => Some f
  | _ => None
  end.
Definition val_to_loc (v : val) : option loc :=
  match v with
  | ValLoc l => Some l
  | _ => None
  end.

Section expr.
Local Unset Elimination Schemes.
Inductive expr : Set :=
| Var (v : string)
| Val (v : val)
| BinOp (e1 : expr) (o : binop) (e2 : expr)
| Load (e : expr)
| Store (e1 e2 : expr)
| If (e e1 e2 : expr)
| LetE (v : string) (e1 e2 : expr)
| Call (e : expr) (args : list expr)
(* expressions only appearing at runtime: *)
| AllocA (ls : list (string * Z)) (e : expr)
| FreeA (ls : list (loc * Z)) (e : expr)
(* Returning to the context, insert automatically during execution. *)
| ReturnExt (can_return_further : bool) (e : expr)
| Waiting (can_return : bool)
.
End expr.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : string), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (e1 : expr) (op : binop) (e2 : expr), P e1 → P e2 → P (BinOp e1 op e2)) →
  (∀ (e : expr), P e → P (Load e)) →
  (∀ (e1 e2 : expr), P e1 → P e2 → P (Store e1 e2)) →
  (∀ (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (If e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : expr), P e1 → P e2 → P (LetE v e1 e2)) →
  (∀ (e : expr) (args : list expr), P e → Forall P args → P (Call e args)) →
  (∀ ls (e : expr), P e → P (AllocA ls e)) →
  (∀ ls (e : expr), P e → P (FreeA ls e)) →
  (∀ (can_return_further : bool) (e : expr), P e → P (ReturnExt can_return_further e)) →
  (∀ (can_return : bool), P (Waiting can_return)) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall ????.
  8: { apply Hcall; [by apply: FIX|]. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. move => ?? []. done. Qed.

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Fixpoint assigned_vars (e : expr) : list string :=
  match e with
  | Var v => []
  | Val v => []
  | BinOp e1 o e2 => assigned_vars e1 ++ assigned_vars e2
  | Load e => assigned_vars e
  | Store e1 e2 => assigned_vars e1 ++ assigned_vars e2
  | If e e1 e2 => assigned_vars e ++ assigned_vars e1 ++ assigned_vars e2
  | LetE v e1 e2 => [v] ++ assigned_vars e1 ++ assigned_vars e2
  | Call e args => assigned_vars e ++ mjoin (assigned_vars <$> args)
  | AllocA _ e => assigned_vars e
  | FreeA _ e => assigned_vars e
  | ReturnExt can_return_further e => assigned_vars e
  | Waiting can_return => []
  end.

(** ** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr) : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst x v e1) o (subst x v e2)
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | If e e1 e2 => If (subst x v e) (subst x v e1) (subst x v e2)
  | LetE y e1 e2 => LetE y (subst x v e1) (if bool_decide (x ≠ y) then subst x v e2 else e2)
  | Call e args => Call (subst x v e) (subst x v <$> args)
  | AllocA ls e => AllocA ls (subst x v e)
  | FreeA ls e => FreeA ls (subst x v e)
  | ReturnExt b e => ReturnExt b (subst x v e)
  | Waiting b => Waiting b
  end.
Fixpoint subst_l (xs : list string) (vs : list val) (e : expr) : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst_l xs' vs' (subst x v e)
  | _,_ => e
  end.

Fixpoint subst_map (x : gmap string val) (e : expr) : expr :=
  match e with
  | Var y => if x !! y is Some v then Val v else Var y
  | Val v => Val v
  | BinOp e1 o e2 => BinOp (subst_map x e1) o (subst_map x e2)
  | Load e => Load (subst_map x e)
  | Store e1 e2 => Store (subst_map x e1) (subst_map x e2)
  | If e e1 e2 => If (subst_map x e) (subst_map x e1) (subst_map x e2)
  | LetE y e1 e2 => LetE y (subst_map x e1) (subst_map (delete y x) e2)
  | Call e args => Call (subst_map x e) (subst_map x <$> args)
  | AllocA ls e => AllocA ls (subst_map x e)
  | FreeA ls e => FreeA ls (subst_map x e)
  | ReturnExt b e => ReturnExt b (subst_map x e)
  | Waiting b => Waiting b
  end.

Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  elim: e => /=; try by move => *; simplify_map_eq; congruence.
  - move => *. rewrite delete_empty. congruence.
  - move => ?? -> /Forall_lookup IH. f_equal.
    apply list_eq => ?. apply option_eq => ?.
    rewrite !list_lookup_fmap !fmap_Some.
    naive_solver congruence.
Qed.

Lemma subst_map_subst x v e xs :
  subst_map (<[x:=v]> xs) e = subst_map xs (subst x v e).
Proof.
  elim: e xs => //=; try by move => *; congruence.
  - move => ??. case_bool_decide; simplify_map_eq => //.
  - move => ??? H1 H2 xs. rewrite H1. case_bool_decide; subst. 2: by rewrite delete_insert_delete.
    by rewrite delete_insert_ne // H2.
  - move => ?? IHe /Forall_lookup IH ?. f_equal; [by rewrite IHe|].
    apply list_eq => ?. apply option_eq => ?.
    rewrite !list_lookup_fmap !fmap_Some. setoid_rewrite fmap_Some.
    naive_solver congruence.
Qed.

Lemma subst_map_subst_map e xs ys:
  subst_map (xs ∪ ys) e = subst_map ys (subst_map xs e).
Proof.
  revert e. induction xs using map_ind => e.
  { by rewrite left_id_L subst_map_empty. }
  rewrite -insert_union_l !subst_map_subst. naive_solver.
Qed.

Lemma subst_subst_map x v e xs :
  subst_map (xs ∪ <[x:=v]> ∅) e = subst x v (subst_map xs e).
Proof. by rewrite subst_map_subst_map subst_map_subst subst_map_empty. Qed.

Lemma subst_subst_map_delete x v e xs :
  subst_map (<[x:=v]> xs) e = subst x v (subst_map (delete x xs) e).
Proof.
  rewrite -subst_subst_map -insert_union_r; [|by simplify_map_eq].
  by rewrite right_id_L insert_delete_insert.
Qed.

Lemma subst_l_subst_map xs vs e :
  length xs = length vs →
  subst_l xs vs e = subst_map (list_to_map (zip xs vs)) e.
Proof.
  elim: xs vs e. { case => //=. move => ??. by rewrite subst_map_empty. }
  move => ?? IH [|??] //= e [?]. by rewrite subst_map_subst IH.
Qed.

(** ** Evaluation contexts *)
Inductive expr_ectx :=
| BinOpLCtx (op : binop) (e2 : expr)
| BinOpRCtx (v1 : val) (op : binop)
| LoadCtx
| StoreLCtx (e2 : expr)
| StoreRCtx (v1 : val)
| IfCtx (e2 e3 : expr)
| LetECtx (v : string) (e2 : expr)
| CallLCtx (el : list expr)
| CallCtx (v : val) (vl : list val) (el : list expr)
| FreeACtx (ls : list (loc * Z))
| ReturnExtCtx (can_return_further : bool)
.

Definition expr_fill_item (Ki : expr_ectx) (e : expr) : expr :=
  match Ki with
  | BinOpLCtx op e2 => BinOp e op e2
  | BinOpRCtx v1 op => BinOp (Val v1) op e
  | LoadCtx => Load e
  | StoreLCtx e2 => Store e e2
  | StoreRCtx v1 => Store (Val v1) e
  | IfCtx e2 e3 => If e e2 e3
  | LetECtx v e2 => LetE v e e2
  | CallLCtx el => Call e el
  | CallCtx v vl el => Call (Val v) ((Val <$> vl) ++ e :: el)
  | FreeACtx ls => FreeA ls e
  | ReturnExtCtx b => ReturnExt b e
  end.

Global Instance expr_fill_item_inj Ki : Inj (=) (=) (expr_fill_item Ki).
Proof. destruct Ki => ??? //=; by simplify_eq/=. Qed.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Val <$> vl1) ++ e1 :: el1 = (Val <$> vl2) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_inv vl1 vl2 e2 el2 :
  (Val <$> vl1) = (Val <$> vl2) ++ e2 :: el2 →
  is_Some (to_val e2).
Proof. revert vl2; induction vl1; destruct vl2 => //?; simplify_eq/=; naive_solver. Qed.

Lemma fill_item_val Ki e : is_Some (to_val (expr_fill_item Ki e)) → is_Some (to_val e).
Proof. destruct Ki => //=; move => [??] //. Qed.

Lemma expr_fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  expr_fill_item Ki1 e1 = expr_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  destruct Ki1, Ki2 => //= *; simplify_eq => //.
  exploit list_expr_val_eq_inv; [| |done|]; naive_solver.
Qed.

Definition expr_fill (K : list expr_ectx) (e : expr) : expr :=
  foldl (flip expr_fill_item) e K.

Lemma expr_fill_app K1 K2 e:
  expr_fill (K2 ++ K1) e = expr_fill K1 (expr_fill K2 e).
Proof. apply foldl_app. Qed.

Lemma fill_val K e : is_Some (to_val (expr_fill K e)) → is_Some (to_val e).
Proof.
  elim/rev_ind: K e => //?? IH e. rewrite expr_fill_app /= => ?.
  apply IH. by apply: fill_item_val.
Qed.

Lemma expr_fill_Waiting_inj K1 K2 b1 b2 :
  expr_fill K1 (Waiting b1) = expr_fill K2 (Waiting b2) → K1 = K2 ∧ b1 = b2.
Proof.
  elim/rev_ind: K1 K2.
  - move => K2. destruct K2 as [|Ki] using rev_ind; [naive_solver|] => /=.
    rewrite expr_fill_app => /=. destruct Ki; naive_solver.
  - move => Ki1 K1 IH K2. destruct K2 as [|Ki2 K2 IHK] using rev_ind => /=.
    { rewrite expr_fill_app => /=. destruct Ki1; naive_solver. }
    rewrite !expr_fill_app /= => Heq.
    have ? : Ki1 = Ki2. {
      apply: expr_fill_item_no_val_inj; [..|done].
      all: apply eq_None_not_Some => /fill_val /=[??]//.
    } subst.
    naive_solver.
Qed.

(** ** Static expressions *)
(** Static expressions correspond to the surface syntax of the language. *)
Fixpoint is_static_expr (allow_loc : bool) (e : expr) : bool :=
  match e with
  | Var v => true
  | Val v => allow_loc || (if v is ValLoc _ then false else true)
  | BinOp e1 o e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | Load e1 => is_static_expr allow_loc e1
  | Store e1 e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | If e e1 e2 => is_static_expr allow_loc e && is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | LetE v e1 e2 => is_static_expr allow_loc e1 && is_static_expr allow_loc e2
  | Call e args => is_static_expr allow_loc e && forallb (is_static_expr allow_loc) args
  | AllocA _ e => allow_loc && is_static_expr allow_loc e
  | FreeA _ e => allow_loc && is_static_expr allow_loc e
  | ReturnExt can_return_further e => false
  | Waiting can_return => false
  end.

Lemma is_static_expr_forallb vs:
  forallb (is_static_expr true) (Val <$> vs).
Proof. by apply forallb_True, Forall_fmap, Forall_true. Qed.

Lemma is_static_expr_subst x v e:
  is_static_expr true e →
  is_static_expr true (subst x v e).
Proof.
  elim: e => //= *; try naive_solver.
  - by case_bool_decide.
  - case_bool_decide; naive_solver.
  - destruct_and!. split_and?; [naive_solver|].
    apply forallb_True, Forall_forall => ? /elem_of_list_fmap[?[??]]. subst.
    revert select (Forall _ _) => /Forall_forall.
    revert select (Is_true (forallb _ _)) => /forallb_True/Forall_forall. naive_solver.
Qed.

Lemma is_static_expr_subst_l xs vs e:
  is_static_expr true e →
  is_static_expr true (subst_l xs vs e).
Proof.
  elim: xs vs e. { by case. }
  move => ?? IH [//|??] /=??. apply IH.
  by apply is_static_expr_subst.
Qed.

Lemma is_static_expr_expr_fill bl K e:
  is_static_expr bl (expr_fill K e) ↔ is_static_expr bl (expr_fill K (Var "")) ∧ is_static_expr bl e.
Proof.
  elim/rev_ind: K e => /=. { naive_solver. }
  move => Ki K IH e. rewrite !expr_fill_app/=.
  destruct Ki => //=; rewrite ?forallb_app/=; naive_solver.
Qed.

Lemma is_static_expr_mono e:
  is_static_expr false e →
  is_static_expr true e.
Proof.
  elim: e => //=; try naive_solver.
  move => ?? IHe IH /andb_True[?] /forallb_True Hargs.
  split_and?; [naive_solver|].
  elim: IH Hargs => // *. decompose_Forall_hyps; naive_solver.
Qed.

(** ** rec_expr_depth *)
Fixpoint rec_expr_depth (e : expr) : nat :=
  match e with
  | Var _ | Val _ | Waiting _ => 0
  | Load e | AllocA _ e | FreeA _ e | ReturnExt _ e => S (rec_expr_depth e)
  | BinOp e1 _ e2 | Store e1 e2 | LetE _ e1 e2 =>
     S ((rec_expr_depth e1) `max` (rec_expr_depth e2))
  | If e1 e2 e3 => S ((rec_expr_depth e1) `max` (rec_expr_depth e2) `max` (rec_expr_depth e3))
  | Call e args => S (rec_expr_depth e `max` max_list (rec_expr_depth <$> args))
  end.

Lemma rec_expr_depth_ind (P : expr → Prop) :
  (∀ e, (∀ e', (rec_expr_depth e' < rec_expr_depth e)%nat → P e') → P e) → ∀ e, P e.
Proof.
  move => IH e. move Heq: (rec_expr_depth e) => n.
  elim/lt_wf_ind: n e Heq. naive_solver.
Qed.

Lemma rec_expr_depth_subst x v e :
  rec_expr_depth (subst x v e) = rec_expr_depth e.
Proof.
  elim: e => //= *; try lia.
  - by case_bool_decide.
  - case_bool_decide; lia.
  - do 2 f_equal; [done|]. f_equal. rewrite -list_fmap_compose. by apply Forall_fmap_ext_1.
Qed.

(** ** fndef *)
Record fndef : Type := {
  fd_args : list string;
  fd_static_vars : list (string * Z); (* (name, size) *)
  fd_vars : list (string * Z);
  fd_body : expr;
  fd_static : is_static_expr false fd_body;
}.

Lemma fndef_eq fn1 fn2 :
  fn1 = fn2 ↔ fd_args fn1 = fd_args fn2
            ∧ fd_static_vars fn1 = fd_static_vars fn2
            ∧ fd_vars fn1 = fd_vars fn2
            ∧ fd_body fn1 = fd_body fn2.
Proof. split; [naive_solver|]. destruct fn1, fn2 => /= -[?[?[??]]]. subst. f_equal. apply proof_irrel. Qed.

(** ** heap *)
Record heap_state : Set := Heap {
  h_heap : gmap loc val;
  h_provs : gset prov;
  heap_wf l : is_Some (h_heap !! l) → l.1 ∈ h_provs;
}.
Add Printing Constructor heap_state.

Lemma heap_state_eq h1 h2:
  h1 = h2 ↔ h1.(h_heap) = h2.(h_heap) ∧ h1.(h_provs) = h2.(h_provs).
Proof. split; [naive_solver|]. destruct h1, h2 => /= -[??]; subst. f_equal. apply AxProofIrrelevance. Qed.

(** *** heap provs *)
Definition h_used_blocks (h : heap_state) : gset block_id :=
  set_omap (λ x, prov_to_block x) (h_provs h).

Definition h_static_provs (h : heap_state) : gset prov :=
  filter (λ x, is_ProvStatic x) (h_provs h).

Lemma elem_of_h_static_provs h p :
  p ∈ h_static_provs h ↔ is_ProvStatic p ∧ p ∈ h_provs h.
Proof. set_solver. Qed.

Lemma elem_of_h_provs p h :
  p ∈ h_provs h ↔ p ∈ h_static_provs h ∨ ∃ b, p = ProvBlock b ∧ b ∈ h_used_blocks h.
Proof.
  rewrite elem_of_filter /h_used_blocks.
  setoid_rewrite elem_of_set_omap.
  destruct p; split => ?; destruct!; try naive_solver.
  destruct x; naive_solver.
Qed.

Lemma h_provs_blocks b h :
  ProvBlock b ∈ h_provs h ↔ b ∈ h_used_blocks h.
Proof.
  rewrite /h_used_blocks elem_of_set_omap.
  split => ?; destruct!; try naive_solver.
  destruct x; naive_solver.
Qed.

Lemma h_provs_static p h :
  is_ProvStatic p →
  p ∈ h_provs h ↔ p ∈ h_static_provs h.
Proof. set_solver. Qed.

Lemma subseteq_h_provs s h :
  s ⊆ h_provs h ↔
  (∀ b, ProvBlock b ∈ s → b ∈ h_used_blocks h) ∧
  (∀ f i, ProvStatic f i ∈ s → ProvStatic f i ∈ h_static_provs h).
Proof.
  setoid_rewrite <-h_provs_blocks. setoid_rewrite <-h_provs_static => //.
  split.
  - naive_solver.
  - move => [H1 H2] []; naive_solver.
Qed.

(* TODO: Rename? *)
Lemma lookup_heap_is_Some_elem_of_h_provs l h :
  is_Some (h_heap h !! l) →
  l.1 ∈ h_provs h.
Proof. apply heap_wf. Qed.

Lemma lookup_heap_Some_elem_of_h_provs l h v :
  h_heap h !! l = Some v →
  l.1 ∈ h_provs h.
Proof. move => ?. by apply lookup_heap_is_Some_elem_of_h_provs. Qed.

Lemma not_elem_of_h_provs_lookup_heap l h :
  l.1 ∉ h_provs h →
  h_heap h !! l = None.
Proof. move => ?. apply eq_None_not_Some. by move => /lookup_heap_is_Some_elem_of_h_provs. Qed.

Global Typeclasses Opaque h_provs.

(** *** various functions on heaps *)
Definition h_block (h : heap_state) (p : prov) : gmap Z val :=
  gmap_curry (h_heap h) !!! p.

Lemma h_block_lookup h p z:
  h_block h p !! z = h_heap h !! (p, z).
Proof.
  rewrite /h_block -lookup_gmap_curry /=.
  apply option_eq => ?.
  rewrite bind_Some lookup_total_alt. simpl.
  destruct (gmap_curry (h_heap h) !! p); naive_solver.
Qed.

Lemma h_block_lookup2 h l:
  h_heap h !! l = h_block h l.1 !! l.2.
Proof. destruct l. by rewrite h_block_lookup. Qed.

Lemma h_heap_difference_block h p :
  (h_heap h ∖ kmap (pair p) (h_block h p)) = filter (λ l, l.1.1 ≠ p) (h_heap h).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite lookup_difference_Some lookup_kmap_None map_lookup_filter_Some/=.
  split.
  - move => [Hh Hlookup]. split!. move => ?. subst.
    move: Hh. by rewrite h_block_lookup2 Hlookup // -surjective_pairing.
  - move => [??]. naive_solver.
Qed.


Definition h_blocks (h : heap_state) : gmap prov (gmap Z val) :=
  set_to_map (λ p, (p, h_block h p)) (h_provs h).

Lemma h_blocks_lookup_Some h p b :
  h_blocks h !! p = Some b ↔ p ∈ h_provs h ∧ b = h_block h p.
Proof. rewrite /h_blocks lookup_set_to_map //. naive_solver. Qed.

Lemma h_blocks_lookup_is_Some h p :
  is_Some (h_blocks h !! p) ↔ p ∈ h_provs h.
Proof. rewrite /is_Some. setoid_rewrite h_blocks_lookup_Some. naive_solver. Qed.

Lemma h_blocks_lookup_None h p :
  h_blocks h !! p = None ↔ p ∉ h_provs h.
Proof. rewrite eq_None_not_Some /is_Some. setoid_rewrite h_blocks_lookup_Some. naive_solver. Qed.

Lemma h_blocks_dom h :
  dom (h_blocks h) = h_provs h.
Proof. apply set_eq => ?. by rewrite elem_of_dom h_blocks_lookup_is_Some. Qed.

Lemma heap_state_blocks_eq h1 h2:
  h1 = h2 ↔ h_blocks h1 = h_blocks h2.
Proof.
  split; [naive_solver|].
  move => /map_eq_iff. setoid_rewrite option_eq.
  setoid_rewrite h_blocks_lookup_Some.
  move => Heq. apply heap_state_eq. split; [|set_solver].
  apply map_eq => i. apply option_eq => x.
  (split => ?; exploit Heq) => [[Hi _] | [_ Hi]]; exploit Hi; split!.
  1, 3: by apply: lookup_heap_Some_elem_of_h_provs.
  all: rewrite !h_block_lookup2; move => [_ <-]; by rewrite -h_block_lookup2.
Qed.


Definition zero_block (n : Z) : gmap Z val :=
  map_seqZ 0 (replicate (Z.to_nat n) (ValNum 0)).

Lemma zero_block_lookup_None k i:
  zero_block k !! i = None ↔ ¬ (0 ≤ i < k)%Z.
Proof.
  rewrite /zero_block lookup_map_seqZ_None length_replicate. naive_solver lia.
Qed.

Lemma zero_block_lookup_Some k i x:
  zero_block k !! i = Some x ↔ x = ValNum 0 ∧ (0 ≤ i < k)%Z.
Proof.
  rewrite /zero_block lookup_map_seqZ_Some lookup_replicate. naive_solver lia.
Qed.

Lemma zero_block_insert_zero (k : Z) i:
  (0 ≤ i < k)%Z →
  <[i:=ValNum 0%Z]> (zero_block k) = zero_block k.
Proof.
  move => ?. apply map_eq => j.
  destruct (decide (i = j)); simplify_map_eq => //.
  symmetry. by apply zero_block_lookup_Some.
Qed.

Lemma zero_block_lookup_is_Some i k :
  is_Some (zero_block k !! i) ↔ (0 ≤ i < k)%Z.
Proof.
  rewrite /is_Some. setoid_rewrite zero_block_lookup_Some.
  naive_solver.
Qed.

Lemma elem_of_dom_zero_block i k :
  i ∈ dom (zero_block k) ↔ (0 ≤ i < k)%Z.
Proof. by rewrite elem_of_dom zero_block_lookup_is_Some. Qed.

Lemma zero_block_list sz :
  zero_block sz = list_to_map ((λ x, pair x (ValNum 0)) <$> seqZ 0 sz).
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite zero_block_lookup_Some -elem_of_list_to_map ?elem_of_list_fmap.
  2: { apply NoDup_alt => ???. do 2 setoid_rewrite list_lookup_fmap_Some.
       setoid_rewrite lookup_seqZ => ??. naive_solver lia. }
  setoid_rewrite elem_of_seqZ. naive_solver lia.
Qed.

Lemma big_sepM_zero_block {PROP : bi} n (Φ : Z → val → PROP) :
  ([∗ map] k↦y ∈ zero_block n, Φ k y) ⊣⊢ ([∗ list] k ∈ seqZ 0 n, Φ k (ValNum 0)).
Proof.
  rewrite zero_block_list big_sepM_list_to_map.
  2: { apply NoDup_alt => ???. do 2 setoid_rewrite list_lookup_fmap_Some.
       setoid_rewrite lookup_seqZ => ??. naive_solver lia. }
  by rewrite big_sepL_fmap.
Qed.


Definition heap_alive (h : heap_state) (l : loc) : Prop :=
  is_Some (h.(h_heap) !! l).

Definition heap_range (h : heap_state) (l : loc) (a : Z) : Prop :=
  ∀ l', l'.1 = l.1 → is_Some (h.(h_heap) !! l') ↔ l.2 ≤ l'.2 < l.2 + a.

Definition heap_is_fresh (h : heap_state) (l : loc) : Prop :=
  l.1 ∉ h_provs h ∧ l.2 = 0 ∧ is_ProvBlock l.1.

Definition heap_fresh (bs : gset block_id) (h : heap_state) : loc :=
  (ProvBlock (fresh (bs ∪ (h_used_blocks h))), 0).

Lemma heap_fresh_is_fresh bs h:
  heap_is_fresh h (heap_fresh bs h).
Proof.
  unfold heap_fresh. split!.
  match goal with | |- context [fresh ?X] => pose proof (is_fresh X) as H; revert H; move: {1 3}(X) => l Hl end.
  split_and! => //=.
  move => /h_provs_blocks.
  set_solver.
Qed.

Lemma heap_fresh_not_in bs h b:
  (heap_fresh bs h).1 = ProvBlock b →
  b ∉ bs.
Proof.
  unfold heap_fresh => /=.
  match goal with | |- context [fresh ?X] => pose proof (is_fresh X) as H; revert H; move: {1 3}(X) => l Hl end.
  set_solver.
Qed.
Global Opaque heap_fresh.

(** *** heap constructors *)
Global Program Instance heap_empty : Empty heap_state :=
  Heap ∅ ∅ _.
Next Obligation. move => ?. rewrite lookup_empty => -[??]. done. Qed.

Program Definition heap_update (h : heap_state) (l : loc) (v : val) : heap_state :=
  Heap (alter (λ _, v) l h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite lookup_alter_is_Some. apply heap_wf. Qed.

Lemma h_static_provs_heap_update h l v :
  h_static_provs (heap_update h l v) = h_static_provs h.
Proof. done. Qed.

Lemma h_provs_heap_update h l v :
  h_provs (heap_update h l v) = h_provs h.
Proof. done. Qed.

Lemma heap_alive_update h l l' v :
  heap_alive h l →
  heap_alive (heap_update h l' v) l.
Proof. move => ?. rewrite /heap_alive/=. by apply lookup_alter_is_Some. Qed.

Lemma h_block_heap_update h l v p :
  h_block (heap_update h l v) p =
    if decide (p = l.1) then alter (λ _, v) l.2 (h_block h p) else h_block h p.
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite h_block_lookup /= !lookup_alter_Some.
  case_decide; rewrite ?lookup_alter_Some h_block_lookup; destruct l; naive_solver.
Qed.

Lemma h_blocks_heap_update h l v :
  h_blocks (heap_update h l v) = alter (λ b, alter (λ _, v) l.2 b) l.1 (h_blocks h).
Proof.
  apply map_eq => p. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_alter_Some.
  setoid_rewrite h_blocks_lookup_Some.
  rewrite h_block_heap_update.
  split => ?; destruct!/=.
  - destruct (decide (p = l.1)); naive_solver.
  - rewrite decide_True //.
  - rewrite decide_False //.
Qed.

Program Definition heap_update_big (h : heap_state) (m : gmap loc val) : heap_state :=
  Heap (map_union_weak m h.(h_heap)) (h.(h_provs)) _.
Next Obligation. move => ???. rewrite map_lookup_imap. move => [? /bind_Some[?[??]]]. by apply heap_wf. Qed.

Lemma heap_update_big_empty h :
  heap_update_big h ∅ = h.
Proof.
  apply heap_state_eq => /=. split!. etrans; [|apply map_imap_Some].
  apply map_imap_ext => ? /=. by rewrite lookup_empty.
Qed.

Lemma heap_update_big_update h l v m:
  heap_update_big (heap_update h l v) m = heap_update_big h (m ∪ (<[l := v]> $ ∅)).
Proof.
  apply heap_state_eq => /=. split!. apply map_eq => i. apply option_eq => v'. rewrite !map_lookup_imap.
  rewrite !bind_Some. setoid_rewrite lookup_alter_Some.
  split => ?; destruct!.
  - split!. destruct (m !! i) eqn:?.
    + by erewrite lookup_union_Some_l.
    + rewrite lookup_union_r //=. by simplify_map_eq.
  - split!. rewrite lookup_union_l //. by simplify_map_eq.
  - destruct (decide (l = i)); subst; split!.
    + destruct (m !! i) eqn:?.
      * by erewrite lookup_union_Some_l.
      * rewrite lookup_union_r //=. by simplify_map_eq.
    + rewrite lookup_union_l //. by simplify_map_eq.
Qed.

Program Definition heap_update_block (h : heap_state) (p : prov) (b : gmap Z val) : heap_state :=
  Heap (kmap (pair p) b ∪ (filter (λ l, l.1.1 ≠ p) h.(h_heap)))
    ({[p]} ∪ h.(h_provs)) _.
Next Obligation.
  move => ???? /lookup_union_is_Some[/lookup_kmap_is_Some|[? /map_lookup_filter_Some[??]]].
  - set_solver.
  - apply elem_of_union. right. by apply heap_wf.
Qed.

Lemma h_static_provs_update_block h p b :
  p ∈ h_provs h →
  h_static_provs (heap_update_block h p b) = h_static_provs h.
Proof. rewrite /h_static_provs/=. set_solver. Qed.

Lemma h_block_heap_update_block h p b p' :
  h_block (heap_update_block h p b) p' =
    if decide (p = p') then b else h_block h p'.
Proof.
  apply map_eq => ?. apply option_eq => ?.
  rewrite h_block_lookup /= lookup_union_Some.
  2: { apply map_disjoint_spec => ??? /lookup_kmap_Some[?[??]] /map_lookup_filter_Some.  naive_solver. }
  rewrite lookup_kmap_Some map_lookup_filter_Some.
  case_decide; rewrite ?h_block_lookup; naive_solver.
Qed.

Lemma h_blocks_heap_update_block h p b :
  h_blocks (heap_update_block h p b) = <[p := b]> (h_blocks h).
Proof.
  apply map_eq => p'. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_insert_Some.
  setoid_rewrite h_blocks_lookup_Some.
  rewrite h_block_heap_update_block.
  case_decide; split => ?; set_solver.
Qed.


(* TODO: take loc instead of prov as argument to allow allocating at
other places than 0 and make some sideconditions a bit easier to solve
by turning 0 ≤ l'.2 < n into l.1 ≤ l'.2 < l.1 + n ? *)
Definition heap_alloc_h (h : gmap loc val) (p : prov) (n : Z) : gmap loc val :=
  (kmap (pair p) (zero_block n) ∪ h).

Lemma heap_alloc_h_lookup h n p (l' : loc):
  p = l'.1 →
  0 ≤ l'.2 < n →
  heap_alloc_h h p n !! l' = Some (ValNum 0).
Proof.
  destruct l' as [p' o'] => /=??; subst. apply lookup_union_Some_l.
  rewrite lookup_kmap. apply zero_block_lookup_Some. naive_solver lia.
Qed.

Lemma heap_alloc_h_is_Some h p n l' :
  is_Some (heap_alloc_h h p n !! l') ↔ is_Some (h !! l') ∨ l'.1 = p ∧ 0 ≤ l'.2 < n.
Proof.
  rewrite /heap_alloc_h -!elem_of_dom dom_union dom_kmap_L elem_of_union elem_of_map.
  setoid_rewrite elem_of_dom_zero_block.
  destruct l'. naive_solver lia.
Qed.

(* must be Opaque, otherwise simpl takes ages to figure out that it cannot reduce heap_alloc_h. *)
Global Opaque heap_alloc_h.

Program Definition heap_alloc (h : heap_state) (l : loc) (n : Z) : heap_state :=
  Heap (heap_alloc_h h.(h_heap) l.1 n) ({[l.1]} ∪ h_provs h) _.
Next Obligation.
  move => ? l ? l' /=. rewrite heap_alloc_h_is_Some.
  move => [?|[-> ?]].
  - exploit heap_wf; [done..|]. set_solver.
  - set_solver.
Qed.

Lemma h_static_provs_heap_alloc h l n :
  is_ProvBlock l.1 →
  h_static_provs (heap_alloc h l n) = h_static_provs h.
Proof.
  rewrite set_eq => Hb p. rewrite !elem_of_h_static_provs /=.
  destruct l.1 => //; set_solver.
Qed.

Lemma h_provs_heap_alloc h l n :
  h_provs (heap_alloc h l n) = {[l.1]} ∪ h_provs h.
Proof. done. Qed.

Lemma heap_alive_alloc h l l' n :
  l.1 = l'.1 →
  0 ≤ l.2 < n →
  heap_alive (heap_alloc h l' n) l.
Proof.
  move => ??. rewrite /heap_alive heap_alloc_h_is_Some. naive_solver.
Qed.

Lemma h_block_heap_alloc h l n :
  heap_is_fresh h l →
  h_block (heap_alloc h l n) l.1 = zero_block n.
Proof.
  intros [Hfresh ?].
  rewrite /h_block /heap_alloc /=.
  apply map_eq; intros i.
  rewrite !lookup_total_gmap_curry.
  rewrite lookup_union_l ?lookup_kmap //. apply eq_None_not_Some.
  contradict Hfresh. move: Hfresh => /lookup_heap_is_Some_elem_of_h_provs//.
Qed.

Lemma h_block_heap_alloc_ne h l n p:
  l.1 ≠ p →
  h_block (heap_alloc h l n) p = h_block h p.
Proof.
  move => ?. rewrite /h_block /heap_alloc /=.
  apply map_eq => i. rewrite !lookup_total_gmap_curry.
  rewrite lookup_union_r // lookup_kmap_None. naive_solver.
Qed.

Lemma h_blocks_heap_alloc h l n:
  heap_is_fresh h l →
  h_blocks (heap_alloc h l n) = <[l.1 := zero_block n]> (h_blocks h).
Proof.
  move => ?. apply map_eq => p. apply option_eq => ?.
  rewrite lookup_insert_Some h_blocks_lookup_Some/= elem_of_union elem_of_singleton.
  destruct (decide (p = l.1)); subst.
  - rewrite h_block_heap_alloc //. set_solver.
  - rewrite h_block_heap_alloc_ne // h_blocks_lookup_Some. set_solver.
Qed.


Program Definition heap_alloc_loc (h : heap_state) (l : loc) (v : val) (H : l.1 ∈ h_provs h) : heap_state :=
  Heap (<[l:=v]> (h_heap h)) (h_provs h) _.
Next Obligation. move => ????? /lookup_insert_is_Some'[<-//|]. apply heap_wf. Qed.

Lemma h_block_heap_alloc_loc h p l v H:
  h_block (heap_alloc_loc h l v H) p = if decide (p = l.1) then <[l.2 := v]> (h_block h p) else h_block h p.
Proof.
  apply map_eq => i. apply option_eq => ?. rewrite !lookup_total_gmap_curry /=.
  rewrite lookup_insert_Some -h_block_lookup.
  case_decide. 2: naive_solver.
  rewrite lookup_insert_Some. destruct l. naive_solver.
Qed.

Lemma h_blocks_heap_alloc_loc h l v b H :
  h_blocks h !! l.1 = Some b →
  h_blocks (heap_alloc_loc h l v H) = <[l.1:=<[l.2 := v]>b]> (h_blocks h).
Proof.
  move => /h_blocks_lookup_Some [??]. subst. apply map_eq => p'. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_insert_Some h_blocks_lookup_Some.
  rewrite h_block_heap_alloc_loc.
  case_decide; naive_solver.
Qed.


Program Definition heap_add_blocks (h : heap_state) (blocks : gset block_id) : heap_state :=
  Heap (h_heap h) (set_map ProvBlock blocks ∪ h_provs h) _.
Next Obligation. move => ????. apply: union_subseteq_r. by eapply heap_wf. Qed.

Lemma h_static_provs_heap_add_blocks h ps:
  h_static_provs (heap_add_blocks h ps) = h_static_provs h.
Proof. rewrite /h_static_provs/=. rewrite filter_union_L. set_solver. Qed.

Program Definition heap_free (h : heap_state) (l : loc) : heap_state :=
  Heap (filter (λ '(l', v), l'.1 ≠ l.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ???. rewrite map_lookup_filter => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

Lemma h_static_provs_heap_free h l :
  h_static_provs (heap_free h l) = h_static_provs h.
Proof. done. Qed.

Lemma h_provs_heap_free h l :
  h_provs (heap_free h l) = h_provs h.
Proof. done. Qed.

(*
Lemma heap_free_alloc h l n b :
  l.1 = ProvBlock b →
  (* b ∉ h_used_blocks h → *)
  heap_free (heap_alloc h l n) l = heap_add_blocks h {[b]}.
Proof.
  move => Hl. apply heap_state_eq => /=. rewrite Hl. split.
  - rewrite map_filter_union.
  2: { apply map_disjoint_list_to_map_l. rewrite Forall_fmap. apply Forall_forall.
       move => ?? /=. apply eq_None_not_Some. move => /heap_wf/=. naive_solver. }
  (* rewrite (map_filter_id _ (h_heap h)). *)
  (* 2: { move => [??] ? /(mk_is_Some _ _) /heap_wf/=Hwf ?. subst. naive_solver. } *)
  (* rewrite map_filter_empty_iff_2 ?left_id_L //. *)
  (* move => ?? /(elem_of_list_to_map_2 _ _ _)/elem_of_list_fmap[?[??]]. simplify_eq/=. by apply. *)
(* Qed. *)
*)

Lemma heap_free_update h l l' v :
  l'.1 = l.1 →
  heap_free (heap_update h l' v) l = heap_free h l.
Proof.
  move => ?. apply heap_state_eq => /=. split; [|done].
  apply map_filter_strong_ext_1 => l'' ?. destruct l'', l', l; simplify_eq/=.
  split => -[?]; rewrite lookup_alter_ne //; congruence.
Qed.

Lemma h_block_free h l p:
  h_block (heap_free h l) p = if decide (p = l.1) then ∅ else h_block h p.
Proof.
  apply map_eq => ?.
  rewrite !lookup_total_gmap_curry /=.
  case_decide.
  - rewrite map_lookup_filter_None_2; naive_solver.
  - by rewrite map_lookup_filter_true // h_block_lookup.
Qed.

Lemma h_blocks_free h l :
  h_blocks (heap_free h l) = alter (λ _, ∅) l.1 (h_blocks h).
Proof.
  apply map_eq => p. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_alter_Some.
  setoid_rewrite h_blocks_lookup_Some.
  rewrite h_block_free.
  case_decide; naive_solver.
Qed.

Program Definition heap_remove_loc (h : heap_state) (l : loc) : heap_state :=
  Heap (delete l (h_heap h)) (h_provs h) _.
Next Obligation. move => ??? /lookup_delete_is_Some[??]. by apply heap_wf. Qed.

Lemma h_block_heap_remove_loc h p l:
  h_block (heap_remove_loc h l) p = if decide (p = l.1) then delete l.2 (h_block h p) else h_block h p.
Proof.
  apply map_eq => i. apply option_eq => ?. rewrite !lookup_total_gmap_curry /=.
  rewrite lookup_delete_Some -h_block_lookup.
  case_decide. 2: naive_solver.
  rewrite lookup_delete_Some. destruct l. naive_solver.
Qed.

Lemma h_blocks_heap_remove_loc h l b :
  h_blocks h !! l.1 = Some b →
  h_blocks (heap_remove_loc h l) = <[l.1:=delete l.2 b]> (h_blocks h).
Proof.
  move => /h_blocks_lookup_Some [??]. subst. apply map_eq => p'. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_insert_Some h_blocks_lookup_Some.
  rewrite h_block_heap_remove_loc.
  case_decide; naive_solver.
Qed.

Program Definition heap_remove_prov (h : heap_state) (p : prov) : heap_state :=
  Heap (filter (λ l, l.1.1 ≠ p) h.(h_heap)) (h.(h_provs) ∖ {[p]}) _.
Next Obligation.
  move => ???. rewrite map_lookup_filter => -[?/bind_Some[?[?/bind_Some[?[??]]]]].
  apply elem_of_difference. split; [|set_solver].
  by apply heap_wf.
Qed.

Lemma h_block_remove_prov h p p':
  h_block (heap_remove_prov h p') p = if decide (p = p') then ∅ else h_block h p.
Proof.
  apply map_eq => ?. rewrite !lookup_total_gmap_curry /=.
  case_decide.
  - rewrite map_lookup_filter_None_2 //. naive_solver.
  - rewrite map_lookup_filter_true //. by rewrite h_block_lookup.
Qed.

Lemma h_blocks_heap_remove_prov h p :
  h_blocks (heap_remove_prov h p) = delete p (h_blocks h).
Proof.
  apply map_eq => p'. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= lookup_delete_Some h_blocks_lookup_Some.
  rewrite elem_of_difference not_elem_of_singleton h_block_remove_prov.
  case_decide; naive_solver.
Qed.


Program Definition heap_merge (h1 h2 : heap_state) : heap_state :=
  Heap (h_heap h1 ∪ h_heap h2) (h_provs h1 ∪ h_provs h2) _.
Next Obligation. move => ???. move => /lookup_union_is_Some[/heap_wf?|/heap_wf?]; set_solver. Qed.

Lemma h_static_provs_heap_merge h1 h2 :
  h_static_provs (heap_merge h1 h2) = h_static_provs h1 ∪ h_static_provs h2.
Proof. by rewrite /h_static_provs/= filter_union_L. Qed.

Lemma h_provs_heap_merge h1 h2 :
  h_provs (heap_merge h1 h2) = h_provs h1 ∪ h_provs h2.
Proof. done. Qed.

Global Instance heap_merge_left_id : LeftId (=) ∅ heap_merge.
Proof. move => ?. apply heap_state_eq => /=. by rewrite !left_id_L. Qed.
Global Instance heap_merge_right_id : RightId (=) ∅ heap_merge.
Proof. move => ?. apply heap_state_eq => /=. by rewrite !right_id_L. Qed.
Global Instance heap_merge_assoc : Assoc (=) heap_merge.
Proof. move => ???. apply heap_state_eq => /=. split; [|set_solver]. by rewrite assoc_L. Qed.

Lemma h_block_heap_merge h1 h2 p :
  h_provs h1 ## h_provs h2 →
  h_block (heap_merge h1 h2) p = if decide (p ∈ h_provs h1) then h_block h1 p else h_block h2 p.
Proof.
  move => Hdisj.
  apply map_eq => ?. apply option_eq => ?.
  rewrite h_block_lookup/=. rewrite lookup_union_Some.
  2: { apply map_disjoint_spec => ??? /lookup_heap_Some_elem_of_h_provs? /lookup_heap_Some_elem_of_h_provs?. set_solver. }
  rewrite -!h_block_lookup. case_decide; split => Hl; destruct!; try naive_solver.
  all: move: Hl; rewrite h_block_lookup => /lookup_heap_Some_elem_of_h_provs; set_solver.
Qed.

Lemma h_blocks_heap_merge h1 h2 :
  h_provs h1 ## h_provs h2 →
  h_blocks (heap_merge h1 h2) = h_blocks h1 ∪ h_blocks h2.
Proof.
  move => Hdisj.
  apply map_eq => ?. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= h_block_heap_merge // elem_of_union.
  rewrite lookup_union_Some.
  2: { apply map_disjoint_dom_2. by rewrite !h_blocks_dom. }
  rewrite !h_blocks_lookup_Some. case_decide; set_solver.
Qed.

Program Definition heap_restrict (h : heap_state) (P : prov → Prop) `{!∀ x, Decision (P x)} : heap_state :=
  Heap (filter (λ x, P x.1.1) h.(h_heap)) h.(h_provs) _.
Next Obligation. move => ????. rewrite map_lookup_filter => -[?/bind_Some[?[??]]]. by apply heap_wf. Qed.

Lemma h_static_provs_heap_restrict h (P : prov → Prop) `{!∀ x, Decision (P x)} :
  h_static_provs (heap_restrict h P) = h_static_provs h.
Proof. done. Qed.

Lemma h_provs_heap_restrict h (P : prov → Prop) `{!∀ x, Decision (P x)} :
  h_provs (heap_restrict h P) = h_provs h.
Proof. done. Qed.

Program Definition heap_from_blocks (bs : gmap prov (gmap Z val)) : heap_state :=
  Heap (gmap_uncurry bs) (dom bs) _.
Next Obligation.
  move => ?[??]. rewrite lookup_gmap_uncurry => -[? /bind_Some[?[??]]]/=.
  by apply elem_of_dom.
Qed.

Lemma h_static_provs_heap_from_blocks bs :
  h_static_provs (heap_from_blocks bs) = filter is_ProvStatic (dom bs).
Proof. done. Qed.

Lemma h_provs_heap_from_blocks bs :
  h_provs (heap_from_blocks bs) = dom bs.
Proof. done. Qed.

Lemma heap_from_blocks_empty :
  heap_from_blocks ∅ = ∅.
Proof. by apply heap_state_eq. Qed.

Lemma heap_from_blocks_insert b s bs :
  bs !! b = None →
  heap_from_blocks (<[b:=s]>bs) = heap_merge (heap_from_blocks ({[ b := s]})) (heap_from_blocks (bs)).
Proof.
  move => ?.
  apply heap_state_eq => /=. split; [|set_solver].
  apply map_eq => -[??]. rewrite lookup_union !lookup_gmap_uncurry.
  apply option_eq => ?. rewrite union_Some !bind_Some !bind_None.
  setoid_rewrite lookup_singleton_Some. setoid_rewrite lookup_singleton_None.
  setoid_rewrite lookup_insert_Some. naive_solver.
Qed.

Lemma h_block_heap_from_blocks bs p :
  h_block (heap_from_blocks bs) p = bs !!! p.
Proof.
  apply map_eq => o. rewrite h_block_lookup => /=.
  rewrite lookup_gmap_uncurry lookup_total_alt.
  by destruct (bs !! p).
Qed.

Lemma h_blocks_heap_from_blocks bs :
  h_blocks (heap_from_blocks bs) = bs.
Proof.
  apply map_eq => p. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/=. split.
  - move => [/elem_of_dom[??] ->]. rewrite h_block_heap_from_blocks. by erewrite lookup_total_correct.
  - move => ?. rewrite elem_of_dom h_block_heap_from_blocks. split; [done|].
    by erewrite lookup_total_correct.
Qed.

Lemma heap_from_blocks_h_blocks h :
  heap_from_blocks (h_blocks h) = h.
Proof. apply heap_state_blocks_eq. by rewrite h_blocks_heap_from_blocks. Qed.

Lemma h_block_heap_merge_block p p' b h:
  p ∉ h_provs h →
  h_block (heap_merge (heap_from_blocks {[p := b]}) h) p' = if decide (p = p') then b else h_block h p'.
Proof.
  move => ?.
  rewrite h_block_heap_merge /=. 2: set_solver.
  rewrite dom_singleton_L. repeat case_decide => //; subst. 2, 3: set_solver.
  rewrite h_block_heap_from_blocks. rewrite lookup_total_singleton //.
Qed.

Lemma h_blocks_heap_merge_block p  b h:
  p ∉ h_provs h →
  h_blocks (heap_merge (heap_from_blocks {[p := b]}) h) = <[p:=b]> (h_blocks h).
Proof.
  move => ?. apply map_eq => p'. apply option_eq => ?.
  rewrite h_blocks_lookup_Some/= h_block_heap_merge_block //.
  rewrite dom_singleton_L lookup_insert_Some h_blocks_lookup_Some.
  case_decide; set_solver.
Qed.

Fixpoint heap_fresh_list (xs : list Z) (bs : gset block_id) (h : heap_state) : list loc :=
  match xs with
  | [] => []
  | x::xs' =>
      let l := heap_fresh bs h in
      l::heap_fresh_list xs' bs (heap_alloc h l x)
  end.

Fixpoint heap_alloc_list (xs : list Z) (ls : list loc) (h h' : heap_state) : Prop :=
  match xs with
  | [] => ls = [] ∧ h' = h
  | x::xs' => ∃ l ls', ls = l::ls' ∧ heap_is_fresh h l ∧ heap_alloc_list xs' ls' (heap_alloc h l x) h'
  end.

Fixpoint heap_free_list (xs : list (loc * Z)) (h h' : heap_state) : Prop :=
  match xs with
  | [] => h' = h
  | x::xs' => is_ProvBlock x.1.1 ∧ heap_range h x.1 x.2 ∧ heap_free_list xs' (heap_free h x.1) h'
  end.

Lemma heap_alloc_list_length xs ls h h' :
  heap_alloc_list xs ls h h' →
  length xs = length ls.
Proof. elim: xs ls h h'. { case; naive_solver. } move => /= ??? [|??] ??; naive_solver. Qed.

Lemma heap_alloc_list_is_block vs ls h1 h2 i l:
  heap_alloc_list vs ls h1 h2 →
  ls !! i = Some l →
  is_ProvBlock l.1.
Proof.
  induction vs as [|v vs IHvs] in i, ls, h1, h2 |-*; destruct ls; simpl; try naive_solver.
  intros (? & ? & ? & [? [??]] & ?) Hlook. simplify_eq.
  destruct i; last by eauto.
  by injection Hlook as ->.
Qed.

Lemma heap_alloc_list_offset_zero vs ls h1 h2 i l:
  heap_alloc_list vs ls h1 h2 →
  ls !! i = Some l →
  l.2 = 0%Z.
Proof.
  induction vs as [|v vs IHvs] in i, ls, h1, h2 |-*; destruct ls; simpl; try naive_solver.
  intros (? & ? & ? & [? [??]] & ?) Hlook. simplify_eq.
  destruct i; last by eauto.
  by injection Hlook as ->.
Qed.

Lemma heap_alloc_list_fresh xs bs h:
  ∃ h', heap_alloc_list xs (heap_fresh_list xs bs h) h h'.
Proof.
  elim: xs bs h. { case; naive_solver. }
  move => a ? IH //= bs h. exploit IH => -[??].
  split!; [|done]. by apply heap_fresh_is_fresh.
Qed.

(** *** heap_range lemmata *)
Lemma heap_range_alloc h l z :
  heap_is_fresh h l →
  heap_range (heap_alloc h l z) l z.
Proof.
  move => [Hfresh [??]] l' ? //=.
  rewrite lookup_union_is_Some lookup_kmap_is_Some.
  setoid_rewrite zero_block_lookup_is_Some.
  split; [|destruct l, l'; naive_solver lia].
  move => [[?[??]]|/lookup_heap_is_Some_elem_of_h_provs ?].
  - destruct l, l'; naive_solver lia.
  - congruence.
Qed.

Lemma heap_range_alloc_other h l z l' z' :
  l.1 ≠ l'.1 →
  heap_range h l' z' →
  heap_range (heap_alloc h l z) l' z'.
Proof.
  move => ? Hrange l'' ?.
  rewrite lookup_union_is_Some lookup_kmap_is_Some.
  setoid_rewrite zero_block_lookup_is_Some.
  etrans; [|by apply Hrange].
  naive_solver.
Qed.

(*
Lemma heap_range_alloc_other' h l z l' z' :
  0 < z' →
  heap_is_fresh h l →
  heap_range h l' z' →
  heap_range (heap_alloc h l z) l' z'.
Proof.
  move => ? [Hfresh [??]] Hrange l'' ? //=.
  rewrite lookup_union_is_Some.
  rewrite list_to_map_lookup_is_Some.
  setoid_rewrite elem_of_list_fmap.
  setoid_rewrite elem_of_seqZ.
  split.
  - move => [|].
    + move => [v [o [[= ??] ?]]].
      unfold offset_loc in *. simplify_eq/=.
      specialize (Hrange (l.1, l'.2) ltac:(done)).
      contradict Hfresh. eapply (lookup_heap_is_Some_elem_of_h_provs (_, _)).
      apply Hrange => /=. lia.
    + by apply Hrange.
  - destruct l, l'. move => /Hrange. naive_solver.
Qed.
*)

Lemma heap_range_update h l z l' v :
  heap_range h l z ↔
  heap_range (heap_update h l' v) l z.
Proof.
  rewrite /heap_range //=.
  by setoid_rewrite lookup_alter_is_Some.
Qed.

Lemma heap_range_free_other h l z l' :
  l.1 ≠ l'.1 →
  heap_range h l z →
  heap_range (heap_free h l') l z.
Proof.
  move => Hneq Hrange l'' Heq //=.
  rewrite -(Hrange l'' ltac:(done)).
  unfold is_Some.
  setoid_rewrite map_lookup_filter_Some.
  rewrite -Heq in Hneq.
  naive_solver.
Qed.

Lemma heap_range_dom_h_block hs ls n:
  ls.2 = 0%Z →
  heap_range hs ls n ↔ dom (h_block hs ls.1) = dom (zero_block n).
Proof.
  move => ?. rewrite set_eq. setoid_rewrite elem_of_dom_zero_block.
  setoid_rewrite elem_of_dom. setoid_rewrite h_block_lookup.
  unfold heap_range. split.
  - move => + ?. move => ->; naive_solver lia.
  - move => Heq [??] /= ->. rewrite Heq. lia.
Qed.

Lemma heap_range_dom_h_block1 hs ls n:
  ls.2 = 0%Z →
  heap_range hs ls n →
  dom (h_block hs ls.1) = dom (zero_block n).
Proof. move => *. by apply heap_range_dom_h_block. Qed.


(** *** heap_preserved *)
Definition heap_preserved (m : gmap prov (gmap Z val)) (h : heap_state) :=
  ∀ l h', m !! l.1 = Some h' → h.(h_heap) !! l = h' !! l.2.

Lemma heap_preserved_mono m1 m2 h:
  heap_preserved m1 h →
  m2 ⊆ m1 →
  heap_preserved m2 h.
Proof. unfold heap_preserved => Hp Hsub ???. apply: Hp. by eapply map_subseteq_spec. Qed.

Lemma heap_preserved_union m1 m2 h:
  heap_preserved m1 h →
  heap_preserved m2 h →
  heap_preserved (m1 ∪ m2) h.
Proof. unfold heap_preserved => Hp Hsub ?? /lookup_union_Some_raw ?. naive_solver. Qed.

Lemma heap_preserved_lookup_r m h h' l v:
  h_heap h !! l = v →
  heap_preserved m h →
  m !! l.1 = Some h' →
  h' !! l.2 = v.
Proof. move => Hl Hp ?. by rewrite -Hp. Qed.

Lemma heap_preserved_update l v h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_update h l v).
Proof.
  move => Hp ???? /=. rewrite lookup_alter_ne; [by eapply Hp|naive_solver].
Qed.

Lemma heap_preserved_alloc l n h m :
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_alloc h l n).
Proof.
  move => Hp ? l' f /= ?. rewrite lookup_union_r; [by apply Hp|].
  rewrite lookup_kmap_None => ??. naive_solver.
Qed.

Lemma heap_preserved_free l h m:
  heap_preserved m h →
  m !! l.1 = None →
  heap_preserved m (heap_free h l).
Proof.
  move => Hp ? l' f ? /=. rewrite map_lookup_filter. etrans; [|by eapply Hp].
  destruct (h_heap h !! l') => //=. case_guard => //. destruct l, l'; naive_solver.
Qed.

Lemma heap_preserved_insert_const p m h:
  heap_preserved (delete p m) h →
  heap_preserved (<[p := h_block h p]> m) h.
Proof.
  move => Hp l f /= /lookup_insert_Some[[??]|[??]]; simplify_eq.
  - rewrite h_block_lookup. by destruct l.
  - apply: Hp => /=. rewrite lookup_delete_Some. done.
Qed.

(** ** initial heap *)
Definition fd_init_heap (f : string) (statics : list (string * Z)) : gmap prov (gmap Z val) :=
  list_to_map (zip_with (λ p sv, (p, zero_block sv.2))
                 (static_provs f statics) statics).

Lemma fd_init_heap_lookup_Some f statics p h :
  fd_init_heap f statics !! p = Some h ↔ ∃ i s, statics !! i = Some s ∧ static_provs f statics !! i = Some p ∧ h = zero_block s.2.
Proof.
  rewrite /fd_init_heap list_to_map_lookup_Some_NoDup.
  - f_equiv => ?. rewrite lookup_zip_with_Some. naive_solver.
  - apply NoDup_alt => ???. rewrite !list_lookup_fmap_Some.
    setoid_rewrite lookup_zip_with_Some.
    setoid_rewrite static_provs_lookup_Some.
    naive_solver.
Qed.

Definition fds_init_heap (fns : gmap string (list (string * Z))) : gmap prov (gmap Z val) :=
  map_fold (λ f fn h, fd_init_heap f fn ∪ h) ∅ fns.

Lemma fds_init_heap_empty :
  fds_init_heap ∅ = ∅.
Proof. done. Qed.

Lemma fds_init_heap_insert f fn fns :
  fns !! f = None →
  fds_init_heap (<[f := fn]> fns) = fd_init_heap f fn ∪ fds_init_heap fns.
Proof.
  move => ?.
  rewrite /fds_init_heap map_fold_insert_L //.
  move => ?????? ??.
  rewrite !assoc_L. f_equal. apply map_union_comm.
  apply map_disjoint_spec.
  move => ??? /fd_init_heap_lookup_Some[? [? [? [/static_provs_lookup_Some ? ?]]]].
  move => /fd_init_heap_lookup_Some[? [? [? [/static_provs_lookup_Some ? ?]]]].
  naive_solver.
Qed.

Lemma fd_init_heap_map_disjoint f1 f2 s1 s2 :
  f1 ≠ f2 →
  fd_init_heap f1 s1 ##ₘ fd_init_heap f2 s2.
Proof.
  move => ?. apply map_disjoint_spec => ???.
  rewrite !fd_init_heap_lookup_Some.
  setoid_rewrite static_provs_lookup_Some.
  naive_solver.
Qed.

Lemma fds_init_heap_map_disjoint f s fns :
  fns !! f = None →
  fd_init_heap f s ##ₘ fds_init_heap fns.
Proof.
  rewrite /fds_init_heap.
  apply (map_fold_weak_ind (λ x m, m !! f = None → fd_init_heap f s ##ₘ x)).
  { move => ?. apply map_disjoint_empty_r. }
  move => ?????? /lookup_insert_None [??].
  apply map_disjoint_union_r_2; [|naive_solver].
  by apply fd_init_heap_map_disjoint.
Qed.

Lemma fds_init_heap_lookup_Some fns p h :
  fds_init_heap fns !! p = Some h ↔ ∃ f statics, fns !! f = Some statics ∧ fd_init_heap f statics !! p = Some h.
Proof.
  rewrite /fds_init_heap.
  apply (map_fold_weak_ind (λ x m, x !! p = Some h ↔ ∃ f statics, m !! f = Some statics ∧
     fd_init_heap f statics !! p = Some h)).
  { setoid_rewrite lookup_empty. naive_solver. }
  move => ????? IH.
  rewrite lookup_union_Some_raw IH. split.
  - move => [? |[?[?[?[??]]]]].
    + eexists _, _. split; [|done]. apply lookup_insert.
    + eexists _, _. split; [|done]. rewrite lookup_insert_ne //. naive_solver.
  - move => [?[? [/lookup_insert_Some[[??]|[??]] ?]]]; simplify_eq; [naive_solver|].
    right. split; [|naive_solver]. apply: map_disjoint_Some_r; [|done]. by apply fd_init_heap_map_disjoint.
Qed.

Lemma fd_init_heap_snoc f statics s :
  fd_init_heap f (statics ++ [s]) =
    <[ProvStatic f (length statics) := zero_block s.2]>
      (fd_init_heap f statics).
Proof.
  apply map_eq => i. apply option_eq => h.
  rewrite lookup_insert_Some !fd_init_heap_lookup_Some.
  setoid_rewrite static_provs_snoc.
  setoid_rewrite lookup_snoc_Some.
  setoid_rewrite static_provs_length.
  setoid_rewrite static_provs_lookup_Some.
  naive_solver lia.
Qed.

Lemma fd_init_heap_ext f s1 s2 :
  s1.*2 = s2.*2 →
  fd_init_heap f s1 = fd_init_heap f s2.
Proof.
  move => Heq.
  apply map_eq => ?. apply option_eq => ?.
  rewrite !fd_init_heap_lookup_Some.
  setoid_rewrite static_provs_lookup_Some.
  have -> : length s1 = length s2 by rewrite -(length_fmap snd) Heq length_fmap.
  split; move => [i [[? b] [?[[??]?]]]]; simplify_eq.
  - have : s2.*2 !! i = Some b by rewrite -Heq list_lookup_fmap_Some; naive_solver.
    move => /list_lookup_fmap_Some[?[??]]. naive_solver.
  - have : s1.*2 !! i = Some b by rewrite Heq list_lookup_fmap_Some; naive_solver.
    move => /list_lookup_fmap_Some[?[??]]. naive_solver.
Qed.

Lemma fds_init_heap_union fns1 fns2 :
  fns1 ##ₘ fns2 →
  fds_init_heap (fns1 ∪ fns2) = fds_init_heap fns1 ∪ fds_init_heap fns2.
Proof.
  induction fns1 as [|x l fns1 ? IH ] using map_ind. { by rewrite fds_init_heap_empty ?left_id_L. }
  move => Hdisj. rewrite -insert_union_l !fds_init_heap_insert // ?IH ?assoc_L //.
  - apply: map_disjoint_weaken_l; [done|]. by apply insert_subseteq_r.
  - apply lookup_union_None. split; [done|]. apply: map_disjoint_Some_l; [done|]. apply lookup_insert.
Qed.

Lemma fds_init_heap_disj fns1 fns2 :
  fns1 ##ₘ fns2 →
  fds_init_heap fns1 ##ₘ fds_init_heap fns2.
Proof.
  induction fns1 as [|x l fns1 ? IH ] using map_ind.
  { move => ?. rewrite fds_init_heap_empty. apply map_disjoint_empty_l. }
  move => Hdisj. rewrite !fds_init_heap_insert //. apply map_disjoint_union_l_2.
  - apply fds_init_heap_map_disjoint. apply: map_disjoint_Some_l; [done|]. apply lookup_insert.
  - apply IH. apply: map_disjoint_weaken_l; [done|]. by apply insert_subseteq_r.
Qed.

(** ** state *)
Record rec_state := Rec {
  st_expr : expr;
  st_heap : heap_state;
  st_fns : gmap string fndef;
}.
Add Printing Constructor rec_state.

Definition rec_init (fns : gmap string fndef) : rec_state :=
  Rec (Waiting false) ∅ fns.

(** ** rec_event *)
Inductive rec_ev : Type :=
| ERCall (fn : string) (args: list val) (h : heap_state)
| ERReturn (ret: val) (h : heap_state).

Global Instance rec_ev_inhabited : Inhabited rec_ev := populate (ERReturn inhabitant ∅).

Definition rec_event := io_event rec_ev.

Definition vals_of_event (e : rec_ev) : list val :=
  match e with
  | ERCall f vs h => vs
  | ERReturn v h => [v]
  end.

Definition heap_of_event (e : rec_ev) : heap_state :=
  match e with
  | ERCall f vs h => h
  | ERReturn v h => h
  end.

Definition event_set_vals_heap (e : rec_ev) (vs : list val) (h : heap_state) : rec_ev :=
  match e with
  | ERCall f vs' h' => ERCall f vs h
  | ERReturn v' h' => ERReturn (vs !!! 0%nat) h
  end.

Lemma heap_of_event_event_set_vals_heap e vs h :
  heap_of_event (event_set_vals_heap e vs h) = h.
Proof. by destruct e. Qed.

Lemma vals_of_event_event_set_vals_heap e vs h :
  length vs = length (vals_of_event e) →
  vals_of_event (event_set_vals_heap e vs h) = vs.
Proof. destruct e => //=. destruct vs as [|? [|]] => //. Qed.

Lemma event_set_vals_heap_idemp e vs1 h1 vs2 h2:
  event_set_vals_heap (event_set_vals_heap e vs1 h1) vs2 h2 = event_set_vals_heap e vs2 h2.
Proof. by destruct e. Qed.

Global Instance event_set_vals_heap_split_assume_inj e : SplitAssumeInj2 (=) (=) (=) (event_set_vals_heap e).
Proof. done. Qed.

(** ** Operational semantics *)
Definition eval_binop (op : binop) (v1 v2 : val) : option val :=
  match op with
  | AddOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValNum (z1 + z2))
  | OffsetOp => l ← val_to_loc v1; z ← val_to_Z v2; Some (ValLoc (l +ₗ z))
  | EqOp =>
      match v1 with
      | ValNum z1 => z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 = z2)))
      | ValBool b1 => b2 ← val_to_bool v2; Some (ValBool (bool_decide (b1 = b2)))
      | _ => None
      end
  | LeOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 ≤ z2)))
  | LtOp => z1 ← val_to_Z v1; z2 ← val_to_Z v2; Some (ValBool (bool_decide (z1 < z2)))
  end.

(* substitution on function call *)
Definition subst_static (f : string) (static_vars : list (string * Z)) :=
  subst_l (static_vars.*1) (ValLoc <$> static_locs f static_vars).

Inductive head_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
| BinOpS v1 op v2 h fns:
  head_step (Rec (BinOp (Val v1) op (Val v2)) h fns) None (λ σ',
    ∃ v, eval_binop op v1 v2 = Some v ∧ σ' = Rec (Val v) h fns)
| LoadS v1 h fns:
  head_step (Rec (Load (Val v1)) h fns) None (λ σ',
    ∃ l v, v1 = ValLoc l ∧ h.(h_heap) !! l = Some v ∧ σ' = Rec (Val v) h fns)
| StoreS v1 v h fns:
  head_step (Rec (Store (Val v1) (Val v)) h fns) None (λ σ',
    ∃ l, v1 = ValLoc l ∧ heap_alive h l ∧ σ' = Rec (Val v) (heap_update h l v) fns)
| IfS v fns e1 e2 h:
  head_step (Rec (If (Val v) e1 e2) h fns) None (λ σ,
       ∃ b, val_to_bool v = Some b ∧ σ = Rec (if b then e1 else e2) h fns)
| LetS x v e fns h:
  head_step (Rec (LetE x (Val v) e) h fns) None (λ σ, σ = Rec (subst x v e) h fns)
| VarES fns h v: (* unbound variable *)
  head_step (Rec (Var v) h fns) None (λ σ, False)
| AllocAS h h' fns ls xs e:
  heap_alloc_list xs.*2 ls h h' →
  head_step (Rec (AllocA xs e) h fns) None (λ σ',
    Forall (λ x, 0 < x) xs.*2 ∧ σ' = Rec (FreeA (zip ls xs.*2) (subst_l xs.*1 (ValLoc <$> ls) e)) h' fns)
| FreeAS h fns ls v:
  head_step (Rec (FreeA ls (Val v)) h fns) None (λ σ',
    ∃ h', heap_free_list ls h h' ∧ σ' = Rec (Val v) h' fns)
| CallUbS v fns vs h:
  val_to_fn v = None →
  head_step (Rec (Call (Val v) (Val <$> vs)) h fns) None (λ σ, False)
| CallInternalS f fn fns vs h:
  fns !! f = Some fn →
  head_step (Rec (Call (Val (ValFn f)) (Val <$> vs)) h fns) None (λ σ,
   length vs = length fn.(fd_args) ∧
   σ = Rec (AllocA fn.(fd_vars) (subst_static f fn.(fd_static_vars) (subst_l fn.(fd_args) vs fn.(fd_body)))) h fns)
| CallExternalS f fns vs h:
  fns !! f = None →
  head_step (Rec (Call (Val (ValFn f)) (Val <$> vs)) h fns) (Some (Outgoing, ERCall f vs h)) (λ σ, σ = Rec (Waiting true) h fns)
| ReturnS fns v b h:
  head_step (Rec (ReturnExt b (Val v)) h fns) (Some (Outgoing, ERReturn v h)) (λ σ, σ = (Rec (Waiting b) h fns))
| RecvCallS fns f fn vs b h h':
  fns !! f = Some fn →
  head_step (Rec (Waiting b) h fns) (Some (Incoming, ERCall f vs h')) (λ σ,
    σ = (Rec (ReturnExt b (Call (Val (ValFn f)) (Val <$> vs))) h' fns))
| RecvReturnS fns v h h':
  head_step (Rec (Waiting true) h fns) (Some (Incoming, ERReturn v h')) (λ σ, σ = (Rec (Val v) h' fns))
.

Definition sub_redexes_are_values (e : expr) :=
  ∀ K e', e = expr_fill K e' → to_val e' = None → K = [].

Lemma sub_redexes_are_values_item e :
  (∀ Ki e', e = expr_fill_item Ki e' → is_Some (to_val e')) →
  sub_redexes_are_values e.
Proof.
  move => Hitem. elim/rev_ind => //= ?? IH?.
  rewrite expr_fill_app /= => /Hitem/fill_val[??].
  naive_solver.
Qed.

Ltac solve_sub_redexes_are_values := apply sub_redexes_are_values_item; case; naive_solver.

Global Instance expr_fill_inj K : Inj (=) (=) (expr_fill K).
Proof. induction K as [|Ki K IH]; rewrite /Inj; naive_solver. Qed.

Lemma val_head_stuck e1 h σ1 κ Pσ : head_step (Rec e1 h σ1) κ Pσ → to_val e1 = None.
Proof. by inversion 1. Qed.

Lemma head_ctx_step_val Ki e h σ1 κ Pσ :
  head_step (Rec (expr_fill_item Ki e) h σ1) κ Pσ → is_Some (to_val e).
Proof. destruct Ki; inversion 1; simplify_eq => //; by apply: list_expr_val_inv. Qed.

Lemma head_fill_step_val K e h σ1 κ Pσ :
  to_val e = None →
  head_step (Rec (expr_fill K e) h σ1) κ Pσ →
  K = [].
Proof.
  elim/rev_ind: K => //=????. rewrite expr_fill_app /= => /head_ctx_step_val /fill_val[??].
  naive_solver.
Qed.

Lemma step_by_val K K' e1' e1_redex h σ1 κ Pσ :
  expr_fill K e1' = expr_fill K' e1_redex →
  to_val e1' = None →
  head_step (Rec e1_redex h σ1) κ Pσ →
  ∃ K'', K' = K'' ++ K.
Proof.
  assert (fill_val : ∀ K e, is_Some (to_val (expr_fill K e)) → is_Some (to_val e)).
  { intros K''. induction K'' as [|Ki K'' IH]=> e //=. by intros ?%IH%fill_item_val. }
  assert (fill_not_val : ∀ K e, to_val e = None → to_val (expr_fill K e) = None).
  { intros ? e. rewrite !eq_None_not_Some. eauto. }

  intros Hfill Hred Hstep; revert K' Hfill.
  induction K as [|Ki K IH] using rev_ind=> /= K' Hfill; eauto using app_nil_r.
  destruct K' as [|Ki' K' _] using @rev_ind; simplify_eq/=.
  { rewrite expr_fill_app in Hstep. apply head_ctx_step_val in Hstep.
    apply fill_val in Hstep. by apply not_eq_None_Some in Hstep. }
  rewrite !expr_fill_app /= in Hfill.
  assert (Ki = Ki') as ->.
  { eapply expr_fill_item_no_val_inj, Hfill; eauto using val_head_stuck. }
  simplify_eq. destruct (IH K') as [K'' ->]; auto.
  exists K''. by rewrite assoc.
Qed.

Inductive prim_step : rec_state → option rec_event → (rec_state → Prop) → Prop :=
  Ectx_step K e e' fns κ Pσ h:
    e = expr_fill K e' →
    head_step (Rec e' h fns) κ Pσ →
    prim_step (Rec e h fns) κ (λ σ, ∃ e2 h2 fns2, Pσ (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill K e2) h2 fns2).

Lemma prim_step_inv K e fns κ h Pσ:
  prim_step (Rec (expr_fill K e) h fns) κ Pσ →
  to_val e = None →
  ∃ K' e' Pσ', e = expr_fill K' e' ∧ head_step (Rec e' h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill (K' ++ K) e2) h2 fns2).
Proof.
  inversion 1; simplify_eq => ?.
  revert select (expr_fill _ _ = expr_fill _ _) => Heq. move: (Heq) => /step_by_val Hg.
  have [//|? ?]:= Hg _ _ _ _ _ ltac:(done). subst.
  rewrite expr_fill_app in Heq. naive_solver.
Qed.

Lemma prim_step_inv_head K e fns h κ Pσ:
  prim_step (Rec (expr_fill K e) h fns) κ Pσ →
  sub_redexes_are_values e →
  to_val e = None →
  ∃ Pσ', head_step (Rec e h fns) κ Pσ' ∧
      Pσ = (λ σ, ∃ e2 h2 fns2, Pσ' (Rec e2 h2 fns2) ∧ σ = Rec (expr_fill K e2) h2 fns2).
Proof.
  move => Hprim Hsub ?.
  move: Hprim => /prim_step_inv[|?[?[?[?[Hstep ?]]]]]. { done. } subst.
  have ->:= Hsub _ _ ltac:(done). 2: { by apply: val_head_stuck. }
  naive_solver.
Qed.

Definition rec_trans := ModTrans prim_step.
Definition rec_mod (fns : gmap string fndef) := Mod rec_trans (rec_init fns).

Global Instance rec_vis_no_all: VisNoAng rec_trans.
Proof. move => *. inv_all @m_step; inv_all head_step; naive_solver. Qed.

(** * Deeply embedded static expressions  *)
Inductive static_val := | StaticValNum (z : Z) | StaticValBool (b : bool) | StaticValFn (f : string).
Global Instance static_val_eqdec : EqDecision static_val.
Proof. solve_decision. Qed.

Definition static_val_to_val (v : static_val) : val :=
  match v with
  | StaticValNum z => ValNum z
  | StaticValBool b => ValBool b
  | StaticValFn f => ValFn f
  end.

Definition val_to_static_val (v : val) : static_val :=
  match v with
  | ValNum z => StaticValNum z
  | ValBool b => StaticValBool b
  | ValFn f => StaticValFn f
  | ValLoc _ => StaticValNum 0
  end.

Section static_expr.
Local Unset Elimination Schemes.
Inductive static_expr : Set :=
| SVar (v : string)
| SVal (v : static_val)
| SBinOp (e1 : static_expr) (o : binop) (e2 : static_expr)
| SLoad (e : static_expr)
| SStore (e1 e2 : static_expr)
| SIf (e e1 e2 : static_expr)
| SLetE (v : string) (e1 e2 : static_expr)
| SCall (e : static_expr) (args : list static_expr)
.
End static_expr.
Lemma static_expr_ind (P : static_expr → Prop) :
  (∀ (x : string), P (SVar x)) →
  (∀ (v : static_val), P (SVal v)) →
  (∀ (e1 : static_expr) (op : binop) (e2 : static_expr), P e1 → P e2 → P (SBinOp e1 op e2)) →
  (∀ (e : static_expr), P e → P (SLoad e)) →
  (∀ (e1 e2 : static_expr), P e1 → P e2 → P (SStore e1 e2)) →
  (∀ (e1 e2 e3 : static_expr), P e1 → P e2 → P e3 → P (SIf e1 e2 e3)) →
  (∀ (v : string) (e1 e2 : static_expr), P e1 → P e2 → P (SLetE v e1 e2)) →
  (∀ (e : static_expr) (args : list static_expr), P e → Forall P args → P (SCall e args)) →
  ∀ (e : static_expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : static_expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall.
  8: { apply Hcall; [by apply: FIX|]. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Fixpoint static_expr_to_expr (e : static_expr) : expr :=
  match e with
  | SVar v => Var v
  | SVal v => Val (static_val_to_val v)
  | SBinOp e1 o e2 => BinOp (static_expr_to_expr e1) o (static_expr_to_expr e2)
  | SLoad e => Load (static_expr_to_expr e)
  | SStore e1 e2 => Store (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SIf e e1 e2 => If (static_expr_to_expr e) (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SLetE v e1 e2 => LetE v (static_expr_to_expr e1) (static_expr_to_expr e2)
  | SCall e args => Call (static_expr_to_expr e) (static_expr_to_expr <$> args)
  end.

Lemma static_expr_is_static e :
  is_static_expr false (static_expr_to_expr e).
Proof.
  elim: e => //=; try naive_solver.
  - by case.
  - move => ??? Hargs. split_and?; [done|]. elim: Hargs => //=. naive_solver.
Qed.

Fixpoint expr_to_static_expr (e : expr) : static_expr :=
  match e with
  | Var v => SVar v
  | Val v => SVal (val_to_static_val v)
  | BinOp e1 o e2 => SBinOp (expr_to_static_expr e1) o (expr_to_static_expr e2)
  | Load e => SLoad (expr_to_static_expr e)
  | Store e1 e2 => SStore (expr_to_static_expr e1) (expr_to_static_expr e2)
  | If e e1 e2 => SIf (expr_to_static_expr e) (expr_to_static_expr e1) (expr_to_static_expr e2)
  | LetE v e1 e2 => SLetE v (expr_to_static_expr e1) (expr_to_static_expr e2)
  | Call e args => SCall (expr_to_static_expr e) (expr_to_static_expr <$> args)
  | _ => SVar ""
  end.

Lemma static_expr_to_expr_to_static_expr e :
  is_static_expr false e →
  static_expr_to_expr (expr_to_static_expr e) = e.
Proof.
  elim: e => //=; try (move => *; f_equal; naive_solver).
  - by case.
  - move => e args He Hall /andb_True[? Hargs]. f_equal. { rewrite He; naive_solver. }
    elim: Hall Hargs => // ??; csimpl => *. f_equal; naive_solver.
Qed.

Record static_fndef : Type := {
  sfd_args : list string;
  sfd_static_vars : list (string * Z);
  sfd_vars : list (string * Z);
  sfd_body : static_expr;
}.

Program Definition static_fndef_to_fndef (fn : static_fndef) : fndef := {|
   fd_args := fn.(sfd_args);
   fd_static_vars := fn.(sfd_static_vars);
   fd_vars := fn.(sfd_vars);
   fd_body := static_expr_to_expr fn.(sfd_body);
|}.
Next Obligation. move => ?. apply static_expr_is_static. Qed.

Definition fndef_to_static_fndef (fn : fndef) : static_fndef := {|
   sfd_args := fn.(fd_args);
   sfd_static_vars := fn.(fd_static_vars);
   sfd_vars := fn.(fd_vars);
   sfd_body := expr_to_static_expr fn.(fd_body);
|}.

Definition rec_static_init (fns : gmap string static_fndef) : rec_state :=
  rec_init (static_fndef_to_fndef <$> fns).

Definition rec_static_mod (fns : gmap string static_fndef) := Mod rec_trans (rec_static_init fns).

Lemma static_fndef_to_fndef_to_static_fndef fn :
  static_fndef_to_fndef (fndef_to_static_fndef fn) = fn.
Proof. apply fndef_eq. split_and!; [done..|] => /=. apply static_expr_to_expr_to_static_expr. apply fd_static. Qed.

(** * tstep *)
(** ** AsVals *)
Class AsVals (es : list expr) (vs : list val) (es' : option (expr * list expr)) := {
  as_vals : es = (Val <$> vs) ++ from_option (λ '(e, es), e :: es) [] es'
}.
Global Hint Mode AsVals ! - ! : typeclass_instances.

Lemma as_vals_nil :
  AsVals [] [] None.
Proof. done. Qed.
Global Hint Resolve as_vals_nil : typeclass_instances.

Lemma as_vals_cons v es vs es' :
  AsVals es vs es' → AsVals (Val v :: es) (v :: vs) es'.
Proof. move => [->]. done. Qed.
Global Hint Resolve as_vals_cons : typeclass_instances.

Lemma as_vals_expr_cons e es:
  AsVals (e :: es) [] (Some (e, es)).
Proof. done. Qed.
Global Hint Resolve as_vals_expr_cons | 50 : typeclass_instances.

Lemma as_vals_fmap vs :
  AsVals (Val <$> vs) vs None.
Proof. constructor. rewrite right_id_L. done. Qed.
Global Hint Resolve as_vals_fmap : typeclass_instances.


(** ** RecExprFill *)
Class RecExprFill (e : expr) (K : list expr_ectx) (e' : expr) := {
    rec_expr_fill_proof : e = expr_fill K e'
}.
Global Hint Mode RecExprFill ! - - : typeclass_instances.

Lemma rec_expr_fill_end e :
  RecExprFill e [] e.
Proof. done. Qed.
Global Hint Resolve rec_expr_fill_end | 100 : typeclass_instances.

Lemma rec_expr_fill_expr_fill e K K' e' `{!RecExprFill e K' e'} :
  RecExprFill (expr_fill K e) (K' ++ K) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_expr_fill : typeclass_instances.

Lemma rec_expr_fill_BinOpL e1 e2 op K e' `{!RecExprFill e1 K e'} :
  RecExprFill (BinOp e1 op e2) (K ++ [BinOpLCtx op e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_BinOpL : typeclass_instances.

Lemma rec_expr_fill_BinOpR (v1 : val) e2 op K e' `{!RecExprFill e2 K e'} :
  RecExprFill (BinOp (Val v1) op e2) (K ++ [BinOpRCtx v1 op]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_BinOpR : typeclass_instances.

Lemma rec_expr_fill_Load e1 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (Load e1) (K ++ [LoadCtx]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_Load : typeclass_instances.

Lemma rec_expr_fill_StoreL e1 e2 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (Store e1 e2) (K ++ [StoreLCtx e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_StoreL : typeclass_instances.

Lemma rec_expr_fill_StoreR (v1 : val) e2 K e' `{!RecExprFill e2 K e'} :
  RecExprFill (Store (Val v1) e2) (K ++ [StoreRCtx v1]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_StoreR : typeclass_instances.

Lemma rec_expr_fill_FreeA e1 K e' ls `{!RecExprFill e1 K e'} :
  RecExprFill (FreeA ls e1) (K ++ [FreeACtx ls]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_FreeA : typeclass_instances.

Lemma rec_expr_fill_If e e2 e3 K e' `{!RecExprFill e K e'} :
  RecExprFill (If e e2 e3) (K ++ [IfCtx e2 e3]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_If : typeclass_instances.

Lemma rec_expr_fill_LetE v e1 e2 K e' `{!RecExprFill e1 K e'} :
  RecExprFill (LetE v e1 e2) (K ++ [LetECtx v e2]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_LetE : typeclass_instances.

Lemma rec_expr_fill_CallL e K e' es `{!RecExprFill e K e'} :
  RecExprFill (Call e es) (K ++ [CallLCtx es]) e'.
Proof.
  destruct RecExprFill0. subst.
  constructor => /=. rewrite expr_fill_app /=. done.
Qed.
Global Hint Resolve rec_expr_fill_CallL : typeclass_instances.

Lemma rec_expr_fill_Call e K e' v es vs es' `{!AsVals es vs (Some (e, es')) } `{!RecExprFill e K e'} :
  RecExprFill (Call (Val v) es) (K ++ [CallCtx v vs es']) e'.
Proof.
  destruct AsVals0, RecExprFill0. subst.
  constructor => /=. rewrite expr_fill_app /=. done.
Qed.
Global Hint Resolve rec_expr_fill_Call : typeclass_instances.

Lemma rec_expr_fill_ReturnExt b e K e' `{!RecExprFill e K e'} :
  RecExprFill (ReturnExt b e) (K ++ [ReturnExtCtx b]) e'.
Proof. constructor => /=. rewrite expr_fill_app /=. f_equal. apply rec_expr_fill_proof. Qed.
Global Hint Resolve rec_expr_fill_ReturnExt : typeclass_instances.

(** ** instances *)
(* This pattern of using RecExprFill at each rule is quite expensive
but we don't care at the moment. *)
Lemma rec_step_Var_s fns h e K v `{!RecExprFill e K (Var v)}:
  TStepS rec_trans (Rec e h fns) (λ G, G None (λ G', True)).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. eexists _, _. split; [done|] => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. naive_solver.
Qed.
Global Hint Resolve rec_step_Var_s : typeclass_instances.

Lemma rec_step_Val_i fns h v :
  TStepI rec_trans (Rec (Val v) h fns) (λ G, G false None (λ G', True)).
Proof.
  constructor => ? HG. apply steps_impl_step_end => /= ?? Hv.
  inv Hv. revert select (Val v = expr_fill _ _).
  destruct K as [|[] ] using rev_ind; simplify_eq/=; rewrite ?expr_fill_app//.
  move => ?. simplify_eq. inv_all head_step.
Qed.
Global Hint Resolve rec_step_Val_i : typeclass_instances.

Lemma rec_step_Waiting_i fns h K e b `{!RecExprFill e K (Waiting b)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (∀ f fn vs h', fns !! f = Some fn →
      G true (Some (Incoming, ERCall f vs h')) (λ G',  G'
          (Rec (expr_fill K (ReturnExt b (Call (Val (ValFn f)) (Val <$> vs)))) h' fns))) ∧
    ∀ v h', b → G true (Some (Incoming, ERReturn v h')) (λ G', G' (Rec (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve rec_step_Waiting_i : typeclass_instances.

Lemma rec_step_Waiting_s fns h e K b `{!RecExprFill e K (Waiting b)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (∃ f fn vs h', fns !! f = Some fn ∧
      G (Some (Incoming, ERCall f vs h')) (λ G', G'
          (Rec (expr_fill K (ReturnExt b (Call (Val (ValFn f)) (Val <$> vs)))) h' fns))) ∨
    ∃ v h', b ∧ G (Some (Incoming, ERReturn v h')) (λ G', G' (Rec (expr_fill K (Val v)) h' fns))
   ).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. destruct!; (split!; [done|]) => /= ??. 2: destruct b => //.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?; destruct!; done.
Qed.
Global Hint Resolve rec_step_Waiting_s : typeclass_instances.

Lemma rec_step_ReturnExt_i fns h e K b (v : val) `{!RecExprFill e K (ReturnExt b (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true (Some (Outgoing, ERReturn v h)) (λ G', G' (Rec (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_ReturnExt_i : typeclass_instances.

Lemma rec_step_ReturnExt_s fns h e K b (v : val) `{!RecExprFill e K (ReturnExt b (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G (Some (Outgoing, ERReturn v h)) (λ G', G' (Rec (expr_fill K (Waiting b)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. done.
Qed.
Global Hint Resolve rec_step_ReturnExt_s : typeclass_instances.

Lemma rec_step_Call_i fns h e K f vs es `{!RecExprFill e K (Call (Val (ValFn f)) es)} `{!AsVals es vs None}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (∀ fn, fns !! f = Some fn → G true None (λ G', length vs = length fn.(fd_args) ∧
         G' (Rec (expr_fill K (AllocA fn.(fd_vars) (subst_static f fn.(fd_static_vars) (subst_l fn.(fd_args) vs fn.(fd_body))))) h fns))) ∧
    (fns !! f = None → G true (Some (Outgoing, ERCall f vs h)) (λ G',
           G' (Rec (expr_fill K (Waiting true)) h fns)))).
Proof.
  destruct AsVals0, RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[Hstep ?]]. {
    apply sub_redexes_are_values_item; case; try naive_solver.
    move => /= ??? e' [_ Heq]. rewrite right_id_L in Heq. by apply: list_expr_val_inv.
  } { done. } subst.
  rewrite right_id_L in Hstep. inv Hstep.
  - naive_solver.
  - naive_solver.
Qed.
Global Hint Resolve rec_step_Call_i : typeclass_instances.

Lemma rec_step_Call_s fns h e K f vs `{!RecExprFill e K (Call (Val (ValFn f)) es)} `{!AsVals es vs None}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (∃ fn, fns !! f = Some fn ∧ G None (λ G', length vs = length fn.(fd_args) → G'
             (Rec (expr_fill K (AllocA fn.(fd_vars) (subst_static f fn.(fd_static_vars) (subst_l fn.(fd_args) vs fn.(fd_body))))) h fns))) ∨
    (fns !! f = None ∧ G (Some (Outgoing, ERCall f vs h)) (λ G',
           G' (Rec (expr_fill K (Waiting true)) h fns)))
).
Proof.
  destruct AsVals0, RecExprFill0; subst. rewrite right_id_L.
  constructor => ? HG.
  destruct!; (split!; [done|]); move => /= ??.
  all: apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  all: destruct!; naive_solver.
Qed.
Global Hint Resolve rec_step_Call_s | 5 : typeclass_instances.

Lemma rec_step_Call_Ub_s fns h e K v vs `{!RecExprFill e K (Call (Val v) es)} `{!AsVals es vs None}:
  TStepS rec_trans (Rec e h fns) (λ G,
    G None (λ G', ∀ f, v = ValFn f → G' (Rec (expr_fill K (Call (Val (ValFn f)) es)) h fns))).
Proof.
  destruct AsVals0, RecExprFill0; subst. rewrite right_id_L.
  constructor => ? HG.
  split!; [done|] => ??.
  destruct (val_to_fn v) eqn:Hv.
  - destruct v => //. apply: steps_spec_end. naive_solver.
  - apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?. destruct!.
Qed.
Global Hint Resolve rec_step_Call_Ub_s | 10 : typeclass_instances.

Lemma rec_step_Binop_i fns h e K (v1 v2 : val) op `{!RecExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ v', eval_binop op v1 v2 = Some v' ∧ G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Binop_i | 10 : typeclass_instances.

Lemma rec_step_Binop_s fns h e K (v1 v2 : val) op `{!RecExprFill e K (BinOp (Val v1) op (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ v', eval_binop op v1 v2 = Some v' → G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Binop_s | 10 : typeclass_instances.

Lemma rec_step_BinopAdd_i fns h e K n1 n2 `{!RecExprFill e K (BinOp (Val (ValNum n1)) AddOp (Val (ValNum n2)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopAdd_i | 5 : typeclass_instances.

Lemma rec_step_BinopAdd_s fns h e K (v1 v2 : val) `{!RecExprFill e K (BinOp (Val v1) AddOp (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ n1 n2, v1 = ValNum n1 → v2 = ValNum n2 → G' (Rec (expr_fill K (Val (ValNum (n1 + n2)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopAdd_s | 5 : typeclass_instances.

Lemma rec_step_BinopOffset_i fns h e K l z `{!RecExprFill e K (BinOp (Val (ValLoc l)) OffsetOp (Val (ValNum z)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. tstep_i => ???. split! => ?. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopOffset_i | 5 : typeclass_instances.

Lemma rec_step_BinopOffset_s fns h e K (v1 v2 : val) `{!RecExprFill e K (BinOp (Val v1) OffsetOp (Val v2))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l z, v1 = ValLoc l → v2 = ValNum z → G' (Rec (expr_fill K (Val (ValLoc (l +ₗ z)))) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??. tstep_s. split! => ? /bind_Some[?[? /bind_Some[?[??]]]].
  destruct v1, v2 => //. simplify_eq/=. naive_solver.
Qed.
Global Hint Resolve rec_step_BinopOffset_s | 5 : typeclass_instances.

Lemma rec_step_Load_i fns h e K l `{!RecExprFill e K (Load (Val (ValLoc l)))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ v', h.(h_heap) !! l = Some v' ∧ G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Load_i : typeclass_instances.

Lemma rec_step_Load_s fns h e K v `{!RecExprFill e K (Load (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l v', v = ValLoc l → h.(h_heap) !! l = Some v' → G' (Rec (expr_fill K (Val v')) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Load_s : typeclass_instances.

Lemma rec_step_Store_i fns h e K l v `{!RecExprFill e K (Store (Val (ValLoc l)) (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', heap_alive h l ∧ G' (Rec (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_Store_i : typeclass_instances.

Lemma rec_step_Store_s fns h e K v1 v `{!RecExprFill e K (Store (Val v1) (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ l, v1 = ValLoc l → heap_alive h l → G'
      (Rec (expr_fill K (Val v)) (heap_update h l v) fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Store_s : typeclass_instances.

Lemma rec_step_AllocA_i fns h e K e' vs `{!RecExprFill e K (AllocA vs e')}:
  TStepI rec_trans (Rec e h fns) (λ G, ∀ ls h', heap_alloc_list vs.*2 ls h h' →
    (G true None (λ G', Forall (λ z, 0 < z) vs.*2 ∧
           G' (Rec (expr_fill K (FreeA (zip ls vs.*2) (subst_l vs.*1 (ValLoc <$> ls) e'))) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_AllocA_i : typeclass_instances.

Lemma rec_step_Alloc_s fns h e e' K vs `{!RecExprFill e K (AllocA vs e')}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∃ ls h', heap_alloc_list vs.*2 ls h h' ∧
      (Forall (λ z, 0 < z) vs.*2 → G' (Rec (expr_fill K (FreeA (zip ls vs.*2) (subst_l vs.*1 (ValLoc <$> ls) e'))) h' fns))))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ?[?[?[??]]].
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_Alloc_s : typeclass_instances.

Lemma rec_step_FreeA_i fns h e K v ls `{!RecExprFill e K (FreeA ls (Val v))}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', ∃ h', heap_free_list ls h h' ∧ G' (Rec (expr_fill K (Val v)) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_FreeA_i : typeclass_instances.

Lemma rec_step_FreeA_s fns h e K ls v `{!RecExprFill e K (FreeA ls (Val v))}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ h', heap_free_list ls h h' → G' (Rec (expr_fill K (Val v)) h' fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_FreeA_s : typeclass_instances.

Lemma rec_step_LetE_i fns h e K x v e1 `{!RecExprFill e K (LetE x (Val v) e1)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_LetE_i : typeclass_instances.

Lemma rec_step_LetE_s fns h e K x v e1 `{!RecExprFill e K (LetE x (Val v) e1)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', G' (Rec (expr_fill K (subst x v e1)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. naive_solver.
Qed.
Global Hint Resolve rec_step_LetE_s : typeclass_instances.

Lemma rec_step_If_i fns h b K e1 e2 `{!RecExprFill e K (If (Val (ValBool b)) e1 e2)}:
  TStepI rec_trans (Rec e h fns) (λ G,
    (G true None (λ G', G' (Rec (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. apply steps_impl_step_end => ?? /prim_step_inv_head[| |?[??]].
  { solve_sub_redexes_are_values. } { done. } subst.
  inv_all head_step.
  naive_solver.
Qed.
Global Hint Resolve rec_step_If_i | 10 : typeclass_instances.

Lemma rec_step_If_s fns h v K e1 e2 `{!RecExprFill e K (If (Val v) e1 e2)}:
  TStepS rec_trans (Rec e h fns) (λ G,
    (G None (λ G', ∀ b, v = ValBool b → G' (Rec (expr_fill K (if b then e1 else e2)) h fns)))).
Proof.
  destruct RecExprFill0; subst.
  constructor => ? HG. split!; [done|]. move => /= ??.
  apply: steps_spec_step_end; [econs; [done|by econs]|] => ? /=?.
  destruct!. destruct v => //. naive_solver.
Qed.
Global Hint Resolve rec_step_If_s | 10 : typeclass_instances.

(** * Proof techniques *)
Definition rec_proof_call (n : ordinal) (fns1 fns2 : gmap string fndef) :=
  (∀ n' f es1' es2' K1' K2' es1 es2 vs1' vs2' h1' h2' b,
      RecExprFill es1' K1' (Call (Val (ValFn f)) es1) →
      RecExprFill es2' K2' (Call (Val (ValFn f)) es2) →
      n' ⊆ n →
      Forall2 (λ e v, e = Val v) es1 vs1' →
      Forall2 (λ e v, e = Val v) es2 vs2' →
      vs1' = vs2' →
      h1' = h2' →
      (∀ v'' h'',
          Rec (expr_fill K1' (Val v'')) h'' fns1
              (* TODO: it possible to make it b instead of false? *)
              ⪯{rec_trans, rec_trans, n', false}
              Rec (expr_fill K2' (Val v'')) h'' fns2) →
      Rec es1' h1' fns1
          ⪯{rec_trans, rec_trans, n', b}
      Rec es2' h2' fns2).

Lemma rec_proof fns1 fns2:
  (∀ f, fns1 !! f = None ↔ fns2 !! f = None) →
  (∀ n K1 K2 f fn1 vs h,
      fns1 !! f = Some fn1 →
      ∃ fn2, fns2 !! f = Some fn2 ∧ length (fd_args fn1) = length (fd_args fn2) ∧ (
        length vs = length (fd_args fn1) →
      (* Call *)
      rec_proof_call n fns1 fns2 →
      (* Return *)
      (∀ n' v1' v2' h1' h2' b,
         n' ⊆ n →
         v1' = v2' →
         h1' = h2' →
         Rec (expr_fill K1 (Val v1')) h1' fns1
             ⪯{rec_trans, rec_trans, n', b}
         Rec (expr_fill K2 (Val v2')) h2' fns2) →

       Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f fn1.(fd_static_vars) $ subst_l fn1.(fd_args) vs (fd_body fn1))) h fns1
           ⪯{rec_trans, rec_trans, n, false}
       Rec (expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f fn2.(fd_static_vars) $ subst_l fn2.(fd_args) vs (fd_body fn2))) h fns2)) →

  trefines (rec_mod fns1) (rec_mod fns2).
Proof.
  move => Hf Hc.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(Rec e2 h2 fns2'),
     ∃ K1 K2 b,
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       h1 = h2 ∧
       e1 = expr_fill K1 (Waiting b) ∧
       e2 = expr_fill K2 (Waiting b) ∧
       ∀ v' h',
         b →
         Rec (expr_fill K1 (Val v')) h' fns1
             ⪯{rec_trans, rec_trans, n', false}
         Rec (expr_fill K2 (Val v')) h' fns2

  ). } { eexists [], []. split!. }
  { move => /= ?? [???] [???] *. destruct!. split!; [done..|].
    move => ???. apply: tsim_mono; [naive_solver|done]. }
  move => /= n1 ? IH [???] [???] ?. destruct!.
  tstep_both. split!.
  2: { move => *. tstep_s. right. split!; [done|]. tend. apply: tsim_mono_b. naive_solver. }
  move => f fn1 vs h ?.
  have [fn2 ?] : is_Some (fns2 !! f). { apply not_eq_None_Some. naive_solver. }
  tstep_s. left. split!; [done..|]. tstep_s. left. split!. move => ?. tend.
  have ? : length (fd_args fn1) = length (fd_args fn2).
  { move: (Hc n0 [] [] f fn1 [] h). naive_solver. }
  tstep_i. split!; [|naive_solver]. move => ??. simplify_eq/=. split; [congruence|].
  unshelve eapply tsim_remember. { simpl. exact (λ n' '(Rec e1 h1 fns1') '(Rec e2 h2 fns2'),
     ∃ K1 K2 f vs fn1 fn2,
       fns1' = fns1 ∧
       fns2' = fns2 ∧
       h1 = h2 ∧
       fns1 !! f = Some fn1 ∧
       fns2 !! f = Some fn2 ∧
       e1 = expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f fn1.(fd_static_vars) $ subst_l (fd_args fn1) vs (fd_body fn1)) ∧
       e2 = expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f fn2.(fd_static_vars) $ subst_l (fd_args fn2) vs (fd_body fn2)) ∧
       length vs = length (fd_args fn1) ∧
       ∀ v' h',
         Rec (expr_fill K1 (Val v')) h' fns1
             ⪯{rec_trans, rec_trans, n', false}
         Rec (expr_fill K2 (Val v')) h' fns2

  ). }
  { eexists (ReturnExtCtx _ :: _), (ReturnExtCtx _ :: _). split!; [try done; congruence..|].
    move => ??. tstep_both. tstep_s. split!; [done|]. tend.
    apply IH; [done|]. by split!. }
  { move => /= ?? [???] [???] *. destruct!. split!; [done..|].
    move => ??. apply: tsim_mono; [naive_solver|]. by apply o_lt_impl_le. }
  move => n2 ? IH2 [???] [???] ?. destruct!.
  exploit Hc; [done|]. move => [?[?[?]]]. simplify_eq.
  apply; [lia|..].
  - move => n' f' ?? ?? es1 es2 vs1' vs2' ??? [?][?] ? Hall1 Hall2 ???.
    have ?: es1 = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
    have ?: es2 = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
    tstep_both. split.
    + move => fn1' ?. tstep_s. left.
      have [fn2' ?] : is_Some (fns2 !! f'). { apply not_eq_None_Some. naive_solver. }
      have ? : length (fd_args fn1') = length (fd_args fn2').
      { move: (Hc n0 [] [] f' fn1' [] h). naive_solver. }
      split! => ?. tend. split; [lia|].
      apply IH2; [done|]. split!; [done..|lia|done].
    + move => ?. tstep_s. right. split!; [naive_solver|done|]. tend.
      apply IH; [etrans; [done|]; etrans; [|done]; apply o_le_S|]. split!; [done..|].
      naive_solver.
  - move => *. subst. apply: tsim_mono; [|done]. apply tsim_mono_b_false. naive_solver.
Qed.

Lemma rec_prepost_proof {S} {M : ucmra} `{!Shrink M} R `{!∀ b, Transitive (R b)} i o fns1 fns2 (s0 : S) (r0 : uPred M):
  (* R true: public transition relation, R false: private transition relation *)
  R false (s0, r0) (s0, r0) →
  (∀ s2 rr2, R false (s0, r0) (s2, rr2) → R true (s2, rr2) (s2, rr2)) →
  (∀ s r s' r', R true (s, r) (s', r') → R false (s, r) (s', r')) →
  (∀ n K1 K2 f fn1 vs1 h1 s1 r1,
      R false (s0, r0) (s1, r1) →
      fns1 !! f = Some fn1 →
      pp_to_all (i (Incoming, ERCall f vs1 h1) s1) (λ '(e', s2) r2, ∀ r2',
      satisfiable (r1 ∗ r2 ∗ r2') →
      ∃ vs2 h2 fn2, e' = (Incoming, ERCall f vs2 h2) ∧ fns2 !! f = Some fn2 ∧ (
        length vs2 = length (fd_args fn2) →
          length vs1 = length (fd_args fn1) ∧ (
      (* Call *)
      (∀ n' f K1' K2' es1 es2 vs1' vs2' h1' h2' b s3 r3,
         n' ⊆ n →
         fns1 !! f = None →
         fns2 !! f = None →
         Forall2 (λ e v, e = Val v) es1 vs1' →
         Forall2 (λ e v, e = Val v) es2 vs2' →
         pp_to_ex (o (Outgoing, ERCall f vs2' h2') s3) (λ '(e''', s4) r4, ∃ r4',
            e''' = (Outgoing, ERCall f vs1' h1') ∧ R false (s1, r1) (s4, r4') ∧
            satisfiable (r4' ∗ r4 ∗ r3) ∧
           ∀ v1'' h1'' s5 r5, R true (s4, r4') (s5, r5) →
                   pp_to_all (i (Incoming, ERReturn v1'' h1'') s5) (λ '(e''''', s6) r6, ∀ r6',
                     satisfiable (r5 ∗ r6 ∗ r6') →
            ∃ v2'' h2'', e''''' = (Incoming, ERReturn v2'' h2'') ∧
          Rec (expr_fill K1' (Val v1'')) h1'' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', true}
          (SMProg, Rec (expr_fill K2' (Val v2'')) h2'' fns2, (PPInside, s6, uPred_shrink r6')))) →

          Rec (expr_fill K1' (Call (Val (ValFn f)) es1)) h1' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', b}
          (SMProg, Rec (expr_fill K2' (Call (Val (ValFn f)) es2)) h2' fns2, (PPInside, s3, uPred_shrink r3))) →
      (* Return *)
      (∀ n' v1 v2 h1' h2' b s3 r3,
         n' ⊆ n →
         pp_to_ex (o (Outgoing, ERReturn v2 h2') s3) (λ '(e''', s4) r4, ∃ r4',
               e''' = (Outgoing, ERReturn v1 h1') ∧ R true (s1, r1) (s4, r4') ∧ satisfiable (r4' ∗ r4 ∗ r3)) →
          Rec (expr_fill K1 (Val v1)) h1' fns1
              ⪯{rec_trans, prepost_trans i o rec_trans, n', b}
          (SMProg, Rec (expr_fill K2 (Val v2)) h2' fns2, (PPInside, s3, uPred_shrink r3))) →
      Rec (expr_fill K1 (AllocA fn1.(fd_vars) $ subst_static f fn1.(fd_static_vars) $ subst_l fn1.(fd_args) vs1 fn1.(fd_body))) h1 fns1
          ⪯{rec_trans, prepost_trans i o rec_trans, n, false}
          (SMProg, Rec (expr_fill K2 (AllocA fn2.(fd_vars) $ subst_static f fn2.(fd_static_vars) $  subst_l fn2.(fd_args) vs2 fn2.(fd_body))) h2 fns2, (PPInside, s2, uPred_shrink r2')))))) →
  trefines (rec_mod fns1) (prepost_mod i o (rec_mod fns2) s0 r0).
Proof.
  move => ?? HR Hc.
  apply: tsim_implies_trefines => n0 /=.
  unshelve eapply tsim_remember_call.
  { simpl. exact (λ d b '((Rec ei1 hi1 fnsi1), (ips1, Rec es1 hs1 fnss1, (pp1, s1, r1)))
                    '((Rec ei2 hi2 fnsi2), (ips2, Rec es2 hs2 fnss2, (pp2, s2, r2))),
    ∃ Ki Ks rr1 rr2,
      r1 = uPred_shrink rr1 ∧ r2 = uPred_shrink rr2 ∧
      fnsi2 = fns1 ∧
      fnss2 = fns2 ∧
      ei2 = expr_fill Ki (Waiting (bool_decide (d ≠ 0%nat))) ∧
      es2 = expr_fill Ks (Waiting (bool_decide (d ≠ 0%nat))) ∧
      pp2 = PPOutside ∧
      ips2 = SMFilter ∧
      R b (s1, rr1) (s2, rr2) ∧
      if b then
        ei2 = ei1 ∧
        es2 = es1
      else
        True
                 ). }
  { simpl. exact (λ  '(Rec ei1 hi1 fnsi1) '(ips1, Rec es1 hs1 fnss1, (pp1, s1, r1))
                     '(Rec ei2 hi2 fnsi2) '(ips2, Rec es2 hs2 fnss2, (pp2, s2, r2)),
    ∃ Ki b v rr,
      r1 = uPred_shrink rr ∧ r2 = uPred_shrink rr ∧
      fnsi2 = fnsi1 ∧
      fnss2 = fnss1 ∧
      ei1 = expr_fill Ki (Waiting b) ∧
      es2 = es1 ∧
      ei2 = expr_fill Ki (Val v) ∧
      ips2 = SMFilter ∧
      hs2 = hs1 ∧
      pp2 = PPRecv1 (Incoming, ERReturn v hi2) ∧
      s2 = s1). }
  { move => ??? *. destruct!. repeat case_match; naive_solver. }
  { move => /= *. destruct!. repeat case_match. naive_solver. }
  { move => /=. eexists [], []. split!. }
  move => /= n [ei hi fnsi] [[ips [es hs fnss]] [[pp {}s] r]] d ? ? Hstay Hcall Hret. destruct!.
  tstep_i. split => *.
  - tstep_s. split!.
    tstep_s. apply: pp_to_all_mono. { by eapply (Hc n (ReturnExtCtx _ :: Ki) (ReturnExtCtx _ :: Ks)). }
    move => -[??] ? Hcall' ??. move: Hcall' => /(_ _ ltac:(done))[?[?[?[?[? Hcall']]]]]. simplify_eq/=.
    tstep_s. left. split!. tstep_s. left. split!. move => ?.
    tstep_i. split; [|naive_solver]. move => ??. simplify_eq. split; [naive_solver|].
    have [//|? {}Hcall'] := Hcall'. apply: tsim_mono_b. apply: Hcall'.
    + move => n' f K1' K2' es1 es2 vs1' vs2' ???????? Hall1 Hall2 ?.
      have ?: es1 = Val <$> vs1'. { clear -Hall1. elim: Hall1; naive_solver. } subst.
      have ?: es2 = Val <$> vs2'. { clear -Hall2. elim: Hall2; naive_solver. } subst.
      tstep_i. split => *; simplify_eq. tstep_s. right. split!.
      tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? /= [?[?[?[??]]]]. simplify_eq. split!; [done|].
      apply Hcall; [done| |]. { split!; [done..|]. by etrans. }
      move => [ei2 hi2 fnsi2] [[ips2 [es2 hs2 fnss2]] [[pp2 {}s2] r2]].
      move => [ei3 hi3 fnsi3] [[ips3 [es3 hs3 fnss3]] [[pp3 {}s3] r3]] ??.
      destruct!.
      tstep_s. apply: pp_to_all_mono; [naive_solver|].
      move => [??] ? Hsim ??. move: Hsim => /(_ _ ltac:(done))?. destruct!/=.
      tstep_s. right. split!.
      repeat match goal with | H : expr_fill _ _ = expr_fill _ _ |- _ => apply expr_fill_Waiting_inj in H end.
      destruct!. done.
    + move => *. tstep_s. tstep_i. tstep_s. apply: pp_to_ex_mono; [done|].
      move => [??] ? [?[?[??]]] /=. subst. split!; [done|]. apply: tsim_mono; [|done].
      apply: Hstay; [done|]. split!; [done..|]. naive_solver.
  - tstep_s. split!.
    apply: Hret; [done|naive_solver| |].
    + split! => //. naive_solver.
    + by split!.
Qed.

(** * closing *)
(**
module rec_event:
Incoming, Call f vs h -> Outgoing, Call f' vs' h' → Incoming, Return v h' -> Outgoing, Return v' h''


module rec_closed_event:
Start f vs            -> Call f' vs' v                                     -> Return v'
*)

Inductive rec_closed_event : Type :=
| ERCStart (f : string) (args: list Z)
| ERCCall (f : string) (args: list Z) (ret : Z)
| ERCEnd (ret : val)
.

Inductive rec_closed_state :=
| RCStart (h : heap_state)
| RCRecvStart (h : heap_state) (f : string) (vs : list Z)
| RCRunning
| RCRecvCall1 (f : string) (args : list val) (h : heap_state)
| RCRecvCall2 (f : string) (args : list Z) (h : heap_state)
| RCRecvRet (v : Z) (h : heap_state)
| RCRecvEnd1 (v : val)
| RCRecvEnd2 (v : Z)
| RCEnd.

Inductive rec_closed_step :
  rec_closed_state → option (sm_event rec_event rec_closed_event) → (rec_closed_state → Prop) → Prop :=
| RCStartS h f vs:
  rec_closed_step (RCStart h) (Some (SMEEmit (ERCStart f vs))) (λ σ, σ = RCRecvStart h f vs)
| RCRecvStartS h f vs:
  rec_closed_step (RCRecvStart h f vs)
                  (Some (SMEReturn (Some (Incoming, ERCall f (ValNum <$> vs) h)))) (λ σ, σ = RCRunning)
| RCRunningS f vs h:
  rec_closed_step RCRunning (Some (SMERecv (Outgoing, ERCall f vs h))) (λ σ, σ = RCRecvCall1 f vs h)
| RCRecvCall1S f vs h:
  rec_closed_step (RCRecvCall1 f vs h) None (λ σ,
         ∃ vs', vs = ValNum <$> vs' ∧ σ = RCRecvCall2 f vs' h)
| RCRecvCall2S f vs rv h:
  rec_closed_step (RCRecvCall2 f vs h)
                  (Some (SMEEmit (ERCCall f vs rv))) (λ σ, σ = RCRecvRet rv h)
| RCRecvRetS v h:
  rec_closed_step (RCRecvRet v h)
                  (Some (SMEReturn (Some (Incoming, ERReturn (ValNum v) h)))) (λ σ, σ = RCRunning)
| RCRunningEndS v h:
  rec_closed_step RCRunning (Some (SMERecv (Outgoing, ERReturn v h))) (λ σ, σ = RCRecvEnd1 v)
| RCRecvEnd1EndS v:
  rec_closed_step (RCRecvEnd1 v) None (λ σ, ∃ v', v = ValNum v' ∧ σ = RCRecvEnd2 v')
| RCEndS v:
  rec_closed_step (RCRecvEnd2 v) (Some (SMEEmit (ERCEnd v))) (λ σ, σ = RCEnd)
.

Definition rec_closed_filter_trans : mod_trans (sm_event rec_event rec_closed_event) :=
  ModTrans rec_closed_step.

Definition rec_closed_filter (h : heap_state) : module (sm_event rec_event rec_closed_event) :=
  Mod rec_closed_filter_trans (RCStart h).

Global Instance rec_closed_filter_vis_no_all : VisNoAng rec_closed_filter_trans.
Proof. move => ????. inv_all @m_step; naive_solver. Qed.

Definition rec_closed (h : heap_state) (m : module rec_event) : module rec_closed_event :=
  seq_map_mod m (rec_closed_filter h) SMFilter.

(** * Linking *)
(** ** Syntactic linking *)
Definition rec_syn_link (fns1 fns2 : gmap string fndef) : gmap string fndef :=
  fns1 ∪ fns2.

Definition rec_ctx_refines (fnsi fnss : gmap string fndef) :=
  ∀ C,
    (* TODO: Move this constraint to fndef? *)
    map_Forall (λ f fn, Forall (λ z, 0 < z) fn.(fd_static_vars).*2) C →
    trefines
         (rec_closed (heap_from_blocks (fds_init_heap (fd_static_vars <$> fnsi ∪ C))) (rec_mod (rec_syn_link fnsi C)))
         (rec_closed (heap_from_blocks (fds_init_heap (fd_static_vars <$> fnss ∪ C))) (rec_mod (rec_syn_link fnss C))).

(** ** Semantic linking *)
Definition rec_link_filter (fns1 fns2 : gset string) : seq_product_case → list seq_product_case → rec_ev → seq_product_case → list seq_product_case → rec_ev → bool → Prop :=
  λ p cs e p' cs' e' ok,
    e' = e ∧
    ok = true ∧
    match e with
    | ERCall f vs h =>
        p' = (if bool_decide (f ∈ fns1) then Some SPLeft else if bool_decide (f ∈ fns2) then Some SPRight else None) ∧
        (cs' = p::cs) ∧
        p ≠ p'
    | ERReturn v h =>
        cs = p'::cs' ∧
        p ≠ p'
    end.
Arguments rec_link_filter _ _ _ _ _ _ _ _ /.

Definition rec_link_trans (fns1 fns2 : gset string) (m1 m2 : mod_trans rec_event) : mod_trans rec_event :=
  link_trans (rec_link_filter fns1 fns2) m1 m2.

Definition rec_link (fns1 fns2 : gset string) (m1 m2 : module rec_event) : module rec_event :=
  Mod (rec_link_trans fns1 fns2 m1.(m_trans) m2.(m_trans)) (MLFRun None, [], m1.(m_init), m2.(m_init)).

Lemma rec_link_trefines m1 m1' m2 m2' fns1 fns2 `{!VisNoAng m1.(m_trans)} `{!VisNoAng m2.(m_trans)}:
  trefines m1 m1' →
  trefines m2 m2' →
  trefines (rec_link fns1 fns2 m1 m2) (rec_link fns1 fns2 m1' m2').
Proof. move => ??. by apply link_mod_trefines. Qed.

(** ** Relating semantic and syntactic linking *)
Inductive rec_link_combine_ectx :
  nat → bool → bool → link_case rec_ev → list seq_product_case → list expr_ectx → list expr_ectx → list expr_ectx → Prop :=
| RPCENil:
  rec_link_combine_ectx 0 false false (MLFRun None) [] [] [] []
| RPCENoneToLeft n cs K Kl Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun None) cs K Kl Kr →
  rec_link_combine_ectx (S n) bl br (MLFRun (Some SPLeft)) (None :: cs)
                             (ReturnExtCtx (bl || br)::K) (ReturnExtCtx bl::Kl) Kr
| RPCENoneToRight n cs K Kl Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun None) cs K Kl Kr →
  rec_link_combine_ectx (S n) bl br (MLFRun (Some SPRight)) (None :: cs)
                             (ReturnExtCtx (bl || br)::K) Kl (ReturnExtCtx br::Kr)
| RPCELeftToRight n cs K Kl Kl' Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun (Some SPLeft)) cs K Kl Kr →
  is_static_expr true (expr_fill Kl' (Var "")) →
  rec_link_combine_ectx (S n) true br (MLFRun (Some SPRight)) (Some SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) (ReturnExtCtx br::Kr)
| RPCELeftToNone n cs K Kl Kl' Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun (Some SPLeft)) cs K Kl Kr →
  is_static_expr true (expr_fill Kl' (Var "")) →
  rec_link_combine_ectx (S n) true br (MLFRun None) (Some SPLeft :: cs)
                             (Kl' ++ K) (Kl' ++ Kl) Kr
| RPCERightToLeft n cs K Kl Kr' Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun (Some SPRight)) cs K Kl Kr →
  is_static_expr true (expr_fill Kr' (Var "")) →
  rec_link_combine_ectx (S n) bl true (MLFRun (Some SPLeft)) (Some SPRight :: cs)
                             (Kr' ++ K) (ReturnExtCtx bl::Kl) (Kr' ++ Kr)
| RPCERightToNone n cs K Kl Kr' Kr bl br:
  rec_link_combine_ectx n bl br (MLFRun (Some SPRight)) cs K Kl Kr →
  is_static_expr true (expr_fill Kr' (Var "")) →
  rec_link_combine_ectx (S n) bl true (MLFRun None) (Some SPRight :: cs)
                             (Kr' ++ K) Kl (Kr' ++ Kr)
.

Definition rec_link_inv (bv : bool) (fns1 fns2 : gmap string fndef) (σ1 : rec_trans.(m_state)) (σ2 : link_case rec_ev * list seq_product_case * rec_state * rec_state) : Prop :=
  let 'Rec e1 h1 fns1' := σ1 in
  let '(σf, cs, Rec el hl fnsl, Rec er hr fnsr) := σ2 in
  ∃ n K Kl Kr e1' el' er' bl br,
  fns1' = fns1 ∪ fns2 ∧
  fnsl = fns1 ∧
  fnsr = fns2 ∧
  rec_link_combine_ectx n bl br σf cs K Kl Kr ∧
  e1 = expr_fill K e1' ∧
  el = expr_fill Kl el' ∧
  er = expr_fill Kr er' ∧
  match σf with
  | MLFRun (Some SPLeft) => e1' = el' ∧ is_static_expr true el' ∧ er' = Waiting br ∧ h1 = hl
              ∧ (if bv then to_val el' = None else True)
  | MLFRun (Some SPRight) => e1' = er' ∧ is_static_expr true er' ∧ el' = Waiting bl ∧ h1 = hr
               ∧ (if bv then to_val er' = None else True)
  | (MLFRun None) => e1' = Waiting (bl || br) ∧ el' = Waiting bl ∧ er' = Waiting br
  | _ => False
  end.


Lemma rec_syn_link_refines_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (rec_mod (rec_syn_link fns1 fns2))
           (rec_link (dom fns1) (dom fns2) (rec_mod fns1) (rec_mod fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, rec_link_inv true fns1 fns2). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [m [K [Kl [Kr ?]]]].
  have {}Hloop : ∀ σi σs,
            rec_link_inv false fns1 fns2 σi σs
            → σi ⪯{rec_trans, rec_link_trans (dom fns1) (dom fns2) rec_trans rec_trans, n, true} σs. {
    clear -Hloop. move => [e1 h1 fns1'] [[[ipfs cs] [el hl fnsl]] [er hr fnsr]].
    move => [m [K [Kl [Kr [e1' [el' [er' [bl [br [?[?[?[HK[?[?[? Hm]]]]]]]]]]]]]]]]; simplify_eq.
    elim/lt_wf_ind: m ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hm => m IHm.
    move => ipfs h1 hl hr cs K Kl Kr e1' el' er' bl br HK Hmatch.
    repeat case_match; destruct!/=.
    - destruct (to_val el') eqn:?; [ |apply: Hloop; naive_solver].
      destruct el'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!; [done..|] => /=. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply is_static_expr_expr_fill.
    - destruct (to_val er') eqn:?; [ |apply: Hloop; naive_solver].
      destruct er'; simplify_eq/=.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i. tstep_s. split!. apply: Hloop; [done|]. by split!.
      * tstep_s. split!.
        tstep_s. split!.
        rewrite !expr_fill_app. apply: IHm; [|done|]; [lia|]. split!. by apply is_static_expr_expr_fill.
    - apply: Hloop; naive_solver.
  }
  destruct!/=. repeat case_match; destruct!.
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    inv_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
    + tstep_s. done.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
    + tstep_s => *. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s. naive_solver.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * tstep_s. left. split!. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. do 2 apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. tstep_s. left. split! => ?. tend.
        split!. apply: Hloop. split!; [by econs|done..|].
        do 2 apply is_static_expr_subst_l. apply is_static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!; [done|]. tend. split!.
      apply: Hloop. split!; [by econs|done..].
  - tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]].
    simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
    rewrite -expr_fill_app.
    inv_all head_step => //.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s => b ?. subst. tend. split!. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
    + tstep_s => *. tend. split!; [done..|]. apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
    + tstep_s. done.
    + tstep_s => *. split!; [done..|] => /= *; simplify_eq. tend. split!.
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
    + tstep_s => *. tend. split!; [done..|].
      apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
      by apply is_static_expr_expr_fill.
    + tstep_s. naive_solver.
    + revert select ((_ ∪ _) !! _ = Some _) => /lookup_union_Some_raw[?|[??]].
      * have ? : fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. right. simpl_map_decide. split!.
        tstep_s. left. split!. tstep_s. left. split! => ?.
        tend. split!. apply: Hloop. split!; [by econs|done..|].
        do 2 apply is_static_expr_subst_l. apply is_static_expr_mono. apply fd_static.
      * tstep_s. left. split! => /= ?. tend. split!.
        apply: Hloop. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. do 2 apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
    + revert select ((_ ∪ _) !! _ = None) => /lookup_union_None[??].
      tstep_s. right. simpl_map_decide. split!;[done|] => /=. tend. split!; [done..|].
      apply: Hloop. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i. split.
    + move => f fn vs h' /lookup_union_Some_raw[?|[??]].
      * have ?: fns2 !! f = None by apply: map_disjoint_Some_l.
        tstep_s. eexists (ERCall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!.
        apply Hloop. split!; [by econs|done..| ]. apply is_static_expr_forallb.
      * tstep_s. eexists (ERCall _ _ _) => /=. simpl. simpl_map_decide. split!.
        tstep_s. split!.
        apply Hloop. split!; [by econs|done..| ]. apply is_static_expr_forallb.
    + move => v h' ?.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/= => //.
      * tstep_s. eexists (ERReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
      * tstep_s. eexists (ERReturn _ _) => /=. split!.
        tstep_s. split!.
        apply Hloop. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
Qed.

Lemma rec_link_refines_syn_link fns1 fns2:
  fns1 ##ₘ fns2 →
  trefines (rec_link (dom fns1) (dom fns2) (rec_mod fns1) (rec_mod fns2))
           (rec_mod (rec_syn_link fns1 fns2)).
Proof.
  move => Hdisj.
  apply tsim_implies_trefines => /= n.
  unshelve apply: tsim_remember. { exact: (λ _, flip (rec_link_inv false fns1 fns2)). }
  { split!. 1: by econs. all: done. } { done. }
  move => /= {}n _ Hloop [[[ipfs cs] [el hl fnsl]] [er hr fnsr]] [e1 h1 fns1'] [m [K [Kl [Kr ?]]]].
  destruct!/=. repeat case_match; destruct!.
  - destruct (to_val el') eqn:?.
    + destruct el'; simplify_eq/=.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq/=.
      * tstep_i => *; destruct!. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct!/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      inv_all/= head_step => //; destruct!.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
      * by tstep_s.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s. naive_solver.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. do 2 apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * move => *. destruct!/=. repeat case_bool_decide => //.
        -- tend. split!. tstep_i. split => *; simplify_eq.
           apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom| done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|done..].
  - destruct (to_val er') eqn:?.
    + destruct er'; simplify_eq/=.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK. inv/= HK.
      * tstep_i => *; destruct!. tstep_s. split!.
        apply: Hloop; [done|]. by split!.
      * tstep_i => *; destruct!/=.
        tstep_i; split => *; simplify_eq.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        by apply is_static_expr_expr_fill.
    + tstep_both. apply: steps_impl_step_end => ?? /prim_step_inv[//|?[?[?[?[??]]]]] *.
      simplify_eq. revert select (Is_true (is_static_expr _ _)) => /is_static_expr_expr_fill/=[??]//.
      rewrite -expr_fill_app.
      inv_all/= head_step => //; destruct!.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s => b ?. subst. tend. split!. apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. destruct b; naive_solver.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst.
      * by tstep_s.
      * tstep_s => *. split!; [done..|] => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        apply is_static_expr_expr_fill. split!. by apply is_static_expr_subst_l.
      * tstep_s => *. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..| ].
        by apply is_static_expr_expr_fill.
      * tstep_s. naive_solver.
      * tstep_s. left. split!; [apply lookup_union_Some; naive_solver|] => ?. tend. split!; [done..|].
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done..|].
        apply is_static_expr_expr_fill. split!. do 2 apply is_static_expr_subst_l.
        apply is_static_expr_mono. apply fd_static.
      * move => *. destruct!/=. repeat case_bool_decide => //.
        -- tend. split!. tstep_i. split => *; simplify_eq.
           apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
        -- tstep_s. right. split!; [apply lookup_union_None;split!;by apply not_elem_of_dom|done|].
           tend. split!. apply: Hloop; [done|]. split!; [by econs|rewrite ?orb_true_r; done..].
  - tstep_i => *.
    repeat match goal with | x : rec_ev |- _ => destruct x end; simplify_eq/=; destruct!/=.
    + tstep_s. left. repeat case_bool_decide => //.
      all: revert select (_ ∈ dom _) => /elem_of_dom[??]; split!;
               [rewrite lookup_union_Some //; naive_solver |].
      * tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
      * tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. split!; [by econs|done..|]. apply is_static_expr_forallb.
    + tstep_s. right.
      revert select (rec_link_combine_ectx _ _ _ _ _ _ _ _) => HK.
      inversion HK; clear HK; simplify_eq; rewrite ?orb_true_r.
      * split!. tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply is_static_expr_expr_fill.
      * split!. tstep_i. split => *; destruct!/=.
        apply: Hloop; [done|]. rewrite !expr_fill_app. split!; [done|done..|].
        by apply is_static_expr_expr_fill.
Qed.

Lemma rec_trefines_implies_ctx_refines fnsi fnss :
  dom fnsi = dom fnss →
  fd_static_vars <$> fnsi = fd_static_vars <$> fnss →
  trefines (rec_mod fnsi) (rec_mod fnss) →
  rec_ctx_refines fnsi fnss.
Proof.
  move => Hdom Hs Href C ?. rewrite /rec_syn_link map_difference_union_r (map_difference_union_r fnss).
  rewrite !map_fmap_union Hs. rewrite {1}(map_difference_eq_dom_L C fnsi fnss) //.
  apply seq_map_mod_trefines. { apply _. } { apply _. }
  etrans. { apply rec_syn_link_refines_link. apply map_disjoint_difference_r'. }
  etrans. 2: { apply rec_link_refines_syn_link. apply map_disjoint_difference_r'. }
  rewrite !dom_difference_L Hdom.
  apply rec_link_trefines; [apply _..| |].
  - apply: Href.
  - erewrite map_difference_eq_dom_L => //. apply _.
Qed.

(** ** Properties of rec_link *)
Lemma rec_link_comm fns1 fns2 m1 m2 :
  fns1 ## fns2 →
  trefines (rec_link fns1 fns2 m1 m2)
           (rec_link fns2 fns1 m2 m1).
Proof.
  move => ?. unshelve apply: link_comm. {
    exact (λ _ s1 s2, s2 = (λ o : seq_product_case, sp_opp <$> o) <$> s1). }
  { done. }
  move => /= p s e p' s' e' ok s2 HR1 ?. destruct!/=. split!.
  case_match; destruct!/=; split!; repeat case_bool_decide => //=.
  1: set_solver.
  all: try destruct p as [[]|]; try destruct p' as [[]|]; naive_solver.
Qed.

(** ** Commuting and associativity of semantic linking (WIP) *)
(*
(* TODO: track a stack of this and compute every thing from it (also keep an optional event) *)
Inductive rec_prod_assoc_state :=
| IPA1 | IPA2 | IPA3 | IPANone.

(* Inductive rec_prod_assoc_stack (m1 m2 m3 : module rec_event) : *)
(*   link_case rec_ev → list seq_product_case → link_case rec_ev → list seq_product_case → *)
(*   link_case rec_ev → list seq_product_case → link_case rec_ev → list seq_product_case → Prop := *)
(* | IPASNil : *)
(*   rec_prod_assoc_stack m1 m2 m3 (MLFRun None) [] (MLFRun None) [] (MLFRun None) [] (MLFRun None) [] *)
(* | IPASNil : *)
(*   rec_prod_assoc_stack m1 m2 m3 (MLFRun None) [] (MLFRun None) [] (MLFRun None) [] (MLFRun None) [] *)
(* . *)

Definition rec_prod_assoc_inv (fns1 fns2 fns3 : gset string) (m1 m2 m3 : module rec_event)
  (σ1 : link_case rec_ev * list seq_product_case * m1.(m_state) *
          (link_case rec_ev * list seq_product_case * m2.(m_state) * m3.(m_state)))
  (σ2 : link_case rec_ev * list seq_product_case * (link_case rec_ev * list seq_product_case * m1.(m_state) * m2.(m_state)) * m3.(m_state)) : Prop :=
  let '(σfi1, csi1, σi1, (σfi2, csi2, σi2, σi3)) := σ1 in
  let '(σfs1, css1, (σfs2, css2, σs1, σs2), σs3) := σ2 in
  ∃ ipacur,
  σi1 = σs1 ∧
  σi2 = σs2 ∧
  σi3 = σs3 ∧
  match ipacur with
  | IPA1 => False
  | IPA2 => False
  | IPA3 => False
  | IPANone => σfi1 = (MLFRun None) ∧ σfi2 = (MLFRun None) ∧ σfs1 = (MLFRun None) ∧ σfs2 = (MLFRun None)
  end.
  (* rec_prod_assoc_stack m1 m2 m3 σfi1 csi1 σfi2 csi2 σfs1 css1 σfs2 css2. *)


Lemma rec_prod_assoc1 fns1 fns2 fns3 m1 m2 m3 σ1 σ2 σ3:
  fns1 ## fns2 →
  trefines (MS (rec_link fns1 (fns2 ∪ fns3) m1 (rec_link fns2 fns3 m2 m3))
              (initial_rec_link_state m1 (rec_link _ _ m2 m3) σ1
                  (initial_rec_link_state m2 m3 σ2 σ3)))
           (MS (rec_link (fns1 ∪ fns2) fns3 (rec_link fns1 fns2 m1 m2) m3)
               (initial_rec_link_state (rec_link _ _ m1 m2) m3
                  (initial_rec_link_state m1 m2 σ1 σ2) σ3)
           ).
Proof.
  move => Hdisj12.
  apply tsim_implies_trefines => n /=.
  unshelve apply: tsim_remember. { exact: (λ _, rec_prod_assoc_inv fns1 fns2 fns3 m1 m2 m3). }
  { eexists IPANone. split!. } { done. }
  move => ?? IH [[[??]?][[[??]?]?]] [[[??][[[??]?]?]]?] /= ?. destruct!.
  (* revert select (rec_prod_assoc_stack _ _ _ _ _ _ _ _ _ _ _) => Hstack. inversion Hstack; simplify_eq. *)
  case_match; destruct!.
  tstep_i => *. case_match; destruct!.
  tstep_s. split!; [repeat case_bool_decide; set_solver|].
  case_bool_decide => /=.
  - rewrite bool_decide_true; [|set_solver].
    tstep_s. split!; [repeat case_bool_decide; set_solver|].
    rewrite bool_decide_true /=; [|set_solver].
    apply IH; [done|]. split!.
  repeat case_bool_decide => /=.

  set_unfold; naive_solver.
  set_unfold; naive_solver.

set_unfold; naive_solver.
try by exfalso; set_unfold; naive_solver.
  - tstep_s. split!; [repeat case_bool_decide; set_solver|].
    apply IH; [done|]. split!.
  tstep_i.
*)
