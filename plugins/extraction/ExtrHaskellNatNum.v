(**
 * Efficient (but uncertified) extraction of usual [nat] functions
 * into equivalent versions in Haskell's Prelude that are defined
 * for any [Num] typeclass instances.  Useful in combination with
 * [Extract Inductive nat] that maps [nat] onto a Haskell type that
 * implements [Num].
 *)

Require Coq.extraction.Extraction.

Require Import Arith.
Require Import EqNat.

Extract Inlined Constant Nat.add => "(Prelude.+)".
Extract Inlined Constant Nat.mul => "(Prelude.*)".
Extract Inlined Constant Nat.max => "Prelude.max".
Extract Inlined Constant Nat.min => "Prelude.min".
Extract Inlined Constant Init.Nat.add => "(Prelude.+)".
Extract Inlined Constant Init.Nat.mul => "(Prelude.*)".
Extract Inlined Constant Init.Nat.max => "Prelude.max".
Extract Inlined Constant Init.Nat.min => "Prelude.min".
Extract Inlined Constant Compare_dec.lt_dec => "(Prelude.<)".
Extract Inlined Constant Compare_dec.leb => "(Prelude.<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(Prelude.<=)".
Extract Inlined Constant EqNat.beq_nat => "(Prelude.==)".
Extract Inlined Constant EqNat.eq_nat_decide => "(Prelude.==)".
Extract Inlined Constant Peano_dec.eq_nat_dec => "(Prelude.==)".

Extract Constant Nat.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant Init.Nat.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant Init.Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".

Extract Constant Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Nat.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
Extract Constant Init.Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Init.Nat.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
