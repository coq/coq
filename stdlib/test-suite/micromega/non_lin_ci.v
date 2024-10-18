From Stdlib Require Import ZArith.
From Stdlib Require Import Lia Psatz.
Open Scope Z_scope.




(* From fiat-crypto Generalized.v *)


Goal forall (x1 : Z) (x2 : Z) (x3 : Z) (x4 : Z) (x5 : Z) (x6 : Z) (x7 : Z) (x8 : Z) (x9 : Z) (x10 : Z) (x11 : Z) (x12 : Z) (x13 : Z) (x14 : Z) (x15 : Z) (x16 : Z) (x17 : Z) (x18 : Z)
(H0 : -1 + -x1^2 + x3*x5 + x1^2*x2 + -x2*x3*x4 >= 0)
(H1 : -1 + x4 >= 0)
(H2 : -1 + x6 >= 0)
(H3 : -1 + -x4 + x1 >= 0)
(H4 : x3 + -x7 = 0)
(H5 : x8 >= 0)
(H6 : -1 + x4 >= 0)
(H7 : x9 >= 0)
(H8 : -x8 + x10 >= 0)
(H9 : -1 + x1^2 + -x9 >= 0)
(H10 : x4 + -x11 >= 0)
(H11 : -x3 + x1*x12 + -x12*x13 >= 0)
(H12 : -1 + -x9 + x1*x4 >= 0)
(H13 : -1 + x4 + -x13 >= 0)
(H14 : x13 >= 0)
(H15 : -1 + x5 >= 0)
(H16 : -1 + x1 + -x2 >= 0)
(H17 : x1^2 + -x13 + -x3*x4 = 0)
(H18 : -1 + x12 + -x14 >= 0)
(H19 : x14 >= 0)
(H20 : x1 + -x14 + -x5*x12 = 0)
(H21 : -1 + x4 + -x15 >= 0)
(H22 : x15 >= 0)
(H23 : x9 + -x15 + -x2*x4 = 0)
(H24 : -x9 + x16 + x4*x17 = 0)
(H25 : x17 + -x18 = 0)
, False
.
Proof.
  intros.
  Time nia.
Qed.

Goal
  forall (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13
  x14 x15 x16 : Z)
         (H6 : x8 < x10 ^ 2 * x15 ^ 2 + 2 * x10 * x15 * x14 + x14 ^ 2)
         (H7 : 0 <= x8)
         (H12 : 0 <= x14)
         (H0 : x8 = x15 * x11 + x9)
         (H14 : x10 ^ 2 * x15 + x10 * x14 < x16)
         (H17 : x16 <= 0)
         (H15 : 0 <= x9)
         (H18 : x9 < x15)
         (H16 : 0 <= x12)
         (H19 : x12 < (x10 * x15 + x14) * x10)
  , False.
Proof.
  intros.
  Time nia.
Qed.


(* From fiat-crypto Toplevel1.v *)


Goal forall
    (x1 x2 x3 x4 x5 x7 : Z)
    (H0 : x1 + x2 - x3 = 0) (* substitute x1, nothing happens *)
    (H1 : 2 * x2 - x4 - 1 >= 0)
    (H2 : - x2 + x4 >= 0)
    (H3 : 2 * x2 - x5 - 1 >= 0)
    (H5 : x2 - 4 >= 0)
    (H7 : - x2 * x7 + x4 * x5 >= 0)
    (H6 : x2 * x7 + x2 - x4 * x5 - 1 >= 0)
    (H9 : x7 - x2 ^ 2 >= 0), (* x2^2 is *visibly* positive *)
  False.
Proof.
  intros.
  nia.
Qed.

Goal forall
    (x1 x2 x3 x4 x5 x7 : Z)
    (H0 : x2 + x1 - x3 = 0) (* substitute x2= x3 -x1 ... *)
    (H1 : 2 * x2 - x4 - 1 >= 0)
    (H2 : - x2 + x4 >= 0)
    (H3 : 2 * x2 - x5 - 1 >= 0)
    (H5 : x2 - 4 >= 0)
    (H7 : - x2 * x7 + x4 * x5 >= 0)
    (H6 : x2 * x7 + x2 - x4 * x5 - 1 >= 0)
    (H9 : x7 - x2 ^ 2 >= 0), (* (x3 - x1)^2 is not visibly positive *)
  False.
Proof.
  intros.
  nia.
Qed.

(* From bedrock2 FlatToRisc.v *)

(* Variant of the following - omega fails (bad linearisation?)*)
Goal forall
    (PXLEN XLEN r : Z)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * PXLEN * q0 + (4 * q + r))
    (H6 : 0 <= 4 * q + r)
    (H7 : 4 * q + r < 4 * PXLEN)
    (H8 : r <= 3)
    (H4 : r >= 1),
  False.
Proof.
  intros.
  Time lia.
Qed.

Goal forall
    (PXLEN XLEN r : Z)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * PXLEN * q0 + (4 * q + r))
    (H6 : 0 <= 4 * q + r)
    (H7 : 4 * q + r < 4 * PXLEN)
    (H8 : r <= 3)
    (H4 : r >= 1),
  False.
Proof.
  intros.
  Time nia.
Qed.


(** Very slow *)
Goal forall
    (XLEN r : Z)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (q q0 r0 a : Z)
    (H3 : 4 * a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H5 : r0 = 4 * q + r)
    (H6 : 0 <= r0)
    (H7 : r0 < 4 * 2 ^ (XLEN - 2))
    (H2 : 0 <= r)
    (H8 : r < 4)
    (H4 : r > 0)
    (H9 : 0 < 2 ^ (XLEN - 2)),
    False.
Proof.
  intros.
  Time nia.
Qed.

Goal forall
    (XLEN r : Z)
    (R : r > 0 \/ r < 0)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (H1 : ~ (0 <= XLEN - 2) \/ 0 < 2 ^ (XLEN - 2))
     (q  q0 r0 a : Z)
    (H2 : 0 <= r0 < 4 * 2 ^ (XLEN - 2))
    (H3 : 4 *  a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H4 : 0 <= r < 4)
    (H5 : r0 = 4 * q + r),
    False.
Proof.
  intros.
  Time nia.
Qed.

Goal forall
    (XLEN r : Z)
    (R : r > 0 \/ r < 0)
    (H : 4 < 2 ^ XLEN)
    (H0 : 8 <= XLEN)
    (H1 : ~ (0 <= XLEN - 2) \/ 0 < 2 ^ (XLEN - 2))
     (q  q0 r0 a : Z)
    (H2 : 0 <= r0 < 4 * 2 ^ (XLEN - 2))
    (H3 : 4 *  a = 4 * 2 ^ (XLEN - 2) * q0 + r0)
    (H4 : 0 <= r < 4)
    (H5 : r0 = 4 * q + r),
    False.
Proof.
  intros.
  intuition idtac.
  Time   all:nia.
Qed.



Goal forall
    (XLEN a q q0 z : Z)
    (HR : 4 * a - 4 * z * q0 - 4 * q > 0)
    (H0 : 8 <= XLEN)
    (H1 : 0 < z)
    (H : 0 <= 4 * a - 4 * z * q0 - 4 * q)
    (H3 : 4 * a - 4 * z * q0 - 4 * q < 4)
    (H4 : 4 * a - 4 * z * q0 < 4 * z),
  False.
Proof.
  intros.
  Time nia.
Qed.



(* From fiat-crypto Modulo.v *)

Goal forall  (b : Z)
             (H : 0 <> b)
             (c  r q1 q2 r2 : Z)
             (H2 : r2 < c)
             (q0 : Z)
             (H7 : r < b)
             (H5 : 0 <= r)
             (H6 : r < b)
             (H12 : 0 < c)
             (H13 : 0 <> c)
             (H0 : 0 <> c * b)
             (H1 : 0 <= r2)
             (H14 : 0 <= q0)
             (H9 : c * q1 + q0 = c * q2 + r2)
             (H4 : 0 <= b * q0 + - r)
             (H10 : b * q0 + - r < c * b),
  q1 = q2.
Proof.
  intros.
  Fail nia.
Abort.


(* From Sozeau's plugin Equations *)


Goal forall x p2 p1 m,
    x <> 0%Z  ->
    (Z.abs (x *  p2 ) > Z.abs (Z.abs p1 + Z.abs m))%Z ->
    (Z.abs (x * (p1 + x * p2 )) > Z.abs m)%Z.
Proof.
  intros.
  Time nia.
Qed.


Goal forall z z0 z1 m
            (Heqz0 : z0 = ((1 + z) * z1)%Z)
            (H0 : (0 <= m)%Z)
            (H3 : z = m)
            (H1 : (0 <= z0)%Z)
            (H4 : z1 = z0)
            (H2 : (z1 > 0)%Z),
  (z1 > z)%Z.
Proof.
  intros.
  Time nia.
Qed.




(* Known issues.

  - Found proof may violate  Proof using ...
    There may be a compliant proof but lia has no way to know.
    Proofs could be optimised to minimise the number of hypotheses,
    but this seems to costly.
Section S.
  Variable z z0 z1 z2 : Z.
  Variable H2 : 0 <= z2.
  Variable H3 : z2 < z1.
  Variable H4 : 0 <= z0.
  Variable H5 : z0 < z1.
  Variable H6 : z = - z2.

  Goal -z1 -z2  >= 0 -> False.
  Proof using  H2 H3  H6.
    intros.
    lia.
  Qed.
*)
