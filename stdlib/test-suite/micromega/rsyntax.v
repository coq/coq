From Stdlib Require Import ZArith.
From Stdlib Require Import Lra.
From Stdlib Require Import Reals.

Goal (1 / (1 - 1) = 0)%R.
  Fail lra. (* division by zero *)
Abort.

Goal (0 / (1 - 1) = 0)%R.
  lra. (* 0 * x = 0 *)
Qed.

Goal (10 ^ 2 = 100)%R.
  lra. (* pow is reified as a constant *)
Qed.

Goal (2 / (1/2) ^ 2 = 8)%R.
  lra. (* pow is reified as a constant *)
Qed.


Goal ( IZR (Z.sqrt 4) = 2)%R.
Proof.
  Fail lra.
Abort.

From Stdlib Require Import DeclConstant.

#[export] Instance Dsqrt : DeclaredConstant Z.sqrt := {}.

Goal ( IZR (Z.sqrt 4) = 2)%R.
Proof.
  lra.
Qed.

From Stdlib Require Import QArith.
From Stdlib Require Import Qreals.

Goal (Q2R (1 # 2) = 1/2)%R.
Proof.
  lra.
Qed.

Goal ( 1 ^ (2 + 2) = 1)%R.
Proof.
  Fail lra.
Abort.

#[export] Instance Dplus : DeclaredConstant Init.Nat.add := {}.

Goal ( 1 ^ (2 + 2) = 1)%R.
Proof.
  lra.
Qed.

From Stdlib Require Import Lia.

Goal ( 1 ^ (2 + 2) = 1)%Z.
Proof.
  lia. (* exponent is a constant expr *)
Qed.

Goal (1 / IZR (Z.pow_pos 10 25) = 1 / 10 ^ 25)%R.
Proof.
  lra.
Qed.
