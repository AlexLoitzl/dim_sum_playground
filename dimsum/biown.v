From iris.bi Require Import bi.
From iris.algebra Require Import cmra updates.

(** * BiOwn *)

Record BiOwn (PROP : bi) `{!BUpd PROP} (r : ucmra) := {
  bi_own : r → PROP;
  bi_own_valid x : bi_own x ⊢ ⌜✓ x⌝;
  bi_own_op x y : bi_own (x ⋅ y) ⊣⊢ bi_own x ∗ bi_own y;
  bi_own_bupd x y : x ~~> y → bi_own x ⊢ |==> bi_own y;
  bi_own_proper : Proper ((≡) ==> (≡)) bi_own
}.
Arguments bi_own {_ _ _} _ _.
