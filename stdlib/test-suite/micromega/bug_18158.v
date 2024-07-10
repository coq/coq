From Stdlib Require Import ZArith.
Import Lia.
Open Scope Z_scope.

Lemma shiftr_lbound a n:
   0 <= a -> True -> 0 <= (Z.shiftr a n).
Proof. now intros; apply Z.shiftr_nonneg. Qed.


Lemma shiftr_ubound a n b :
   0 <= n -> 0 <= a < b -> (Z.shiftr a n) < b.
Proof.
  intros.
  rewrite -> Z.shiftr_div_pow2 by assumption.

  apply Zdiv.Zdiv_lt_upper_bound.
  - now apply Z.pow_pos_nonneg.
  -
    eapply Z.lt_le_trans.
    2: apply Z.le_mul_diag_r; try lia.
    lia.
Qed.

Lemma shiftrContractive8 v r :
   0 <= v < 2 ^ 8 -> 0 <= r -> (Z.shiftr v r) <  2 ^ 8.
Proof.
  intros; apply shiftr_ubound; assumption.
Qed.


Lemma shiftrContractive16 v r :
   0 <= v < 2 ^ 16 -> 0 <= r -> (Z.shiftr v r) <  2 ^ 16.
Proof.
  intros; apply shiftr_ubound; assumption.
Qed.

Lemma shiftrContractive32 v r :
   0 <= v < 2 ^ 32 -> 0 <= r -> (Z.shiftr v r) <  2 ^ 32.
Proof.
  intros; apply shiftr_ubound; assumption.
Qed.

#[global] Instance sat_shiftr_lbound : ZifyClasses.Saturate BinIntDef.Z.shiftr :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a;
    ZifyClasses.PArg2 := fun b => True;
    ZifyClasses.PRes := fun a b ab => 0 <= ab;
    ZifyClasses.SatOk := shiftr_lbound
  |}.
Add Zify Saturate sat_shiftr_lbound.

#[global] Instance sat_shiftr_contr_8 : ZifyClasses.Saturate BinIntDef.Z.shiftr :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a < 2 ^ 8;
    ZifyClasses.PArg2 := fun b => 0 <= b;
    ZifyClasses.PRes := fun a b ab => ab < 2 ^ 8;
    ZifyClasses.SatOk := shiftrContractive8
  |}.
Add Zify Saturate sat_shiftr_contr_8.

#[global] Instance sat_shiftr_contr_16 : ZifyClasses.Saturate BinIntDef.Z.shiftr :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a < 2 ^ 16;
    ZifyClasses.PArg2 := fun b => 0 <= b;
    ZifyClasses.PRes := fun a b ab => ab < 2 ^ 16;
    ZifyClasses.SatOk := shiftrContractive16
  |}.
Add Zify Saturate sat_shiftr_contr_16.


#[global] Instance sat_shiftr_contr_32 : ZifyClasses.Saturate BinIntDef.Z.shiftr :=
  {|
    ZifyClasses.PArg1 := fun a => 0 <= a < 2 ^ 32;
    ZifyClasses.PArg2 := fun b => 0 <= b;
    ZifyClasses.PRes := fun a b ab => ab < 2 ^ 32;
    ZifyClasses.SatOk := shiftrContractive32
  |}.
Add Zify Saturate sat_shiftr_contr_32.


Goal forall x y ,
    Z.le (Z.shiftr x 16) 255
    -> Z.le (Z.shiftr x 8) 255
    -> Z.le (Z.shiftr x 0 ) 255
    -> Z.le (Z.shiftr y 8) 255
    -> Z.le (Z.shiftr x 24) 255.
  intros.
  Zify.zify_saturate.
  (* [xlia zchecker] used to raise a [Stack overflow] error. It is supposed to fail normally. *)
  assert_fails (xlia zchecker).
Abort.
