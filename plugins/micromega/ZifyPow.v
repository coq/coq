Require Import Arith Max Min BinInt BinNat Znat Nnat.
Require Import ZifyClasses.
Require Export ZifyInst.

Instance Op_Z_pow_pos : BinOp Z.pow_pos :=
  { TBOp := Z.pow ; TBOpInj := ltac:(reflexivity) }.
Add BinOp Op_Z_pow_pos.
