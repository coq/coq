(**
 * Efficient (but uncertified) extraction of usual [Z] functions
 * into equivalent versions in Haskell's Prelude that are defined
 * for any [Num] typeclass instances.  Useful in combination with
 * [Extract Inductive Z] that maps [Z] onto a Haskell type that
 * implements [Num].
 *)

Require Coq.extraction.Extraction.

Require Import ZArith.
Require Import EqNat.

Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".

Extract Constant Z.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
