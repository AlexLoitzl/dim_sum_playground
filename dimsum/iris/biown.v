From iris.bi Require Import bi.
From iris.algebra Require Import cmra updates.
From iris.base_logic.lib Require Import iprop own.
From iris.proofmode Require Import proofmode.

(** * BiOwn *)

Record BiOwn (PROP : bi) `{!BUpd PROP} (r : ucmra) := {
  bi_own : r → PROP;
  bi_own_valid x : bi_own x ⊢ ⌜✓ x⌝;
  bi_own_op x y : bi_own (x ⋅ y) ⊣⊢ bi_own x ∗ bi_own y;
  bi_own_bupd x y : x ~~> y → bi_own x ⊢ |==> bi_own y;
  bi_own_proper : Proper ((≡) ==> (≡)) bi_own
}.
Arguments bi_own {_ _ _} _ _.

(** ** Instance for [own] *)
Program Definition bi_own_own (r : ucmra) `{!inG Σ r} `{!CmraDiscrete r} (γ : gname) :
  BiOwn (iProp Σ) r := {|
  bi_own r := own γ r;
|}.
Next Obligation. move => ?????? /=. rewrite own_valid_r. by iIntros "[? %]". Qed.
Next Obligation. move => * /=. by apply own_op. Qed.
Next Obligation. move => * /=. by apply own_update. Qed.
Next Obligation. move => * /=. solve_proper. Qed.
