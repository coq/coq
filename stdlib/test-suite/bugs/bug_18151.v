From Stdlib Require Import BinInt.
From Stdlib Require Import Zify ZifyClasses.
Import Z.
Open Scope Z_scope.

#[global] Instance sat_mod_le : ZifyClasses.Saturate BinIntDef.Z.modulo :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a;
    ZifyClasses.PArg2 := fun b => 0 < b;
    ZifyClasses.PRes := fun a b ab => ab <= a;
    ZifyClasses.SatOk := mod_le
  |}.
Add Zify Saturate sat_mod_le.

Lemma shiftr_lbound a n:
   0 <= a -> True -> 0 <= (Z.shiftr a n).
Proof. now intros; apply Z.shiftr_nonneg. Qed.

#[global] Instance sat_shiftr_lbound : ZifyClasses.Saturate BinIntDef.Z.shiftr :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a;
    ZifyClasses.PArg2 := fun b => True;
    ZifyClasses.PRes := fun a b ab => 0 <= ab;
    ZifyClasses.SatOk := shiftr_lbound
  |}.
Add Zify Saturate sat_shiftr_lbound.

Axiom TODO: forall {P}, P.

Goal forall x4 x5 t0 : N,
 0 <= of_N x4 <= 18446744073709551615 ->
 land
   (shiftr (of_N x4) (of_N t0) mod 2 ^ of_N (Npos 64))
   (shiftl 1 (of_N x5) - 1) =
 land (shiftr (of_N x4) (of_N t0))
   (shiftl 1 (of_N x5) - 1).
Proof.
  intros.
  zify.
  apply TODO.
Qed.
(* Qed used to fail with the following error before #18152.
Error: No such section variable or assumption: __sat6. *)
