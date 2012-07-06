(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import ZArith.
Require Import Psatz.
Open Scope Z_scope.
Require Import ZMicromega.
Require Import VarMap.

(* false in Q : x=1/2 and n=1 *)

Lemma not_so_easy : forall x n : Z,
  2*x + 1 <= 2 *n -> x <= n-1.
Proof.
  intros.
  lia.
Qed.


(* From Laurent Théry *)

Lemma some_pol : forall x, 4 * x ^ 2 + 3 * x + 2 >= 0.
Proof.
  intros.
  psatz Z 2.
Qed.


Lemma Zdiscr: forall a b c x,
  a * x ^ 2 + b * x + c = 0 -> b ^ 2 - 4 * a * c >= 0.
Proof.
  intros ; psatz Z 4.
Qed.


Lemma plus_minus : forall x y,
  0 = x + y -> 0 =  x -y -> 0 = x /\ 0 = y.
Proof.
  intros.
  lia.
Qed.



Lemma mplus_minus : forall x y,
  x + y >= 0 -> x -y >= 0 -> x^2 - y^2 >= 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma pol3: forall x y, 0 <= x + y ->
  x^3 + 3*x^2*y + 3*x* y^2 + y^3 >= 0.
Proof.
  intros; psatz Z 4.
Qed.


(* Motivating example from: Expressiveness + Automation + Soundness:
   Towards COmbining SMT Solvers and Interactive Proof Assistants *)
Parameter rho : Z.
Parameter rho_ge : rho >= 0.
Parameter correct : Z -> Z -> Prop.


Definition rbound1 (C:Z -> Z -> Z) : Prop :=
  forall p s t, correct p t /\ s <= t -> C p t - C p s <= (1-rho)*(t-s).

Definition rbound2 (C:Z -> Z -> Z) : Prop :=
  forall p s t, correct p t /\ s <= t ->  (1-rho)*(t-s) <= C p t - C p s.


Lemma bounded_drift : forall s t p q C D, s <= t /\ correct p t  /\ correct q t /\
  rbound1 C /\ rbound2 C /\ rbound1 D /\ rbound2 D  ->
  Z.abs (C p t - D q t) <= Z.abs (C p s - D q s) + 2 * rho * (t- s).
Proof.
  intros.
  generalize (Z.abs_eq (C p t - D q t)).
  generalize (Z.abs_neq (C p t - D q t)).
  generalize (Z.abs_eq (C p s -D q s)).
  generalize (Z.abs_neq (C p s - D q s)).
  unfold rbound2 in H.
  unfold rbound1 in H.
  intuition.
  generalize (H6 _ _ _ (conj H H4)).
  generalize (H7 _ _ _ (conj H H4)).
  generalize (H8 _ _ _ (conj H H4)).
  generalize (H10 _ _ _ (conj H H4)).
  generalize (H6 _ _ _ (conj H5 H4)).
  generalize (H7 _ _ _ (conj H5 H4)).
  generalize (H8 _ _ _ (conj H5 H4)).
  generalize (H10 _ _ _ (conj H5 H4)).
  generalize rho_ge.
  psatz Z 2.
Qed.

(* Rule of signs *)

Lemma sign_pos_pos: forall x y,
  x > 0 -> y > 0 -> x*y > 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_pos_zero: forall x y,
  x > 0 -> y = 0 -> x*y = 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_pos_neg: forall x y,
  x > 0 -> y < 0 -> x*y < 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_zer_pos: forall x y,
  x = 0 -> y > 0 -> x*y = 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_zero_zero: forall x y,
  x = 0 -> y = 0 -> x*y = 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_zero_neg: forall x y,
  x = 0 -> y < 0 -> x*y = 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_neg_pos: forall x y,
  x < 0 -> y > 0 -> x*y < 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_neg_zero: forall x y,
  x < 0 -> y = 0 -> x*y = 0.
Proof.
  intros; psatz Z 2.
Qed.

Lemma sign_neg_neg: forall x y,
  x < 0 -> y < 0 -> x*y > 0.
Proof.
  intros; psatz Z 2.
Qed.


(* Other (simple) examples *)

Lemma binomial : forall x y, (x+y)^2 = x^2 + 2*x*y + y^2.
Proof.
  intros.
  lia.
Qed.

Lemma product : forall x y, x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
  intros.
  psatz Z 2.
Qed.


Lemma product_strict : forall x y, x > 0 -> y > 0 -> x * y > 0.
Proof.
  intros.
  psatz Z 2.
Qed.


Lemma pow_2_pos : forall x, x ^ 2 + 1 = 0 ->  False.
Proof.
  intros ; psatz Z 2.
Qed.

(* Found in Parrilo's talk *)
(* BUG?: certificate with **very** big coefficients *)
Lemma parrilo_ex : forall x y, x - y^2 + 3 >= 0 -> y + x^2 + 2 = 0 -> False.
Proof.
  intros.
  psatz Z 2.
Qed.

(* from hol_light/Examples/sos.ml *)

Lemma hol_light1 : forall a1 a2 b1 b2,
  a1 >= 0 -> a2 >= 0 ->
   (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) ->
   (a1 * b1 + a2 * b2 = 0) -> a1 * a2 - b1 * b2 >= 0.
Proof.
  intros ; psatz Z 4.
Qed.


Lemma hol_light2 : forall x a,
        3 * x + 7 * a < 4 -> 3 < 2 * x -> a < 0.
Proof.
 intros ; psatz Z 2.
Qed.

Lemma hol_light3 : forall b a c x,
  b ^ 2 < 4 * a * c -> (a * x ^2  + b * x + c = 0) -> False.
Proof.
intros ; psatz Z 4.
Qed.

Lemma hol_light4 : forall a c b x,
  a * x ^ 2 + b * x + c = 0 -> b ^ 2 >= 4 * a * c.
Proof.
intros ; psatz Z 4.
Qed.

Lemma hol_light5 : forall x y,
    0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1
     -> x ^ 2 + y ^ 2 < 1 \/
      (x - 1) ^ 2 + y ^ 2 < 1 \/
      x ^ 2 + (y - 1) ^ 2 < 1 \/
      (x - 1) ^ 2 + (y - 1) ^ 2 < 1.
Proof.
intros; psatz Z 3.
Qed.



Lemma hol_light7 : forall x y z,
 0<= x /\ 0 <= y /\ 0 <= z /\ x + y + z <= 3
  -> x * y + x * z + y * z >= 3 * x * y * z.
Proof.
intros ; psatz Z 3.
Qed.

Lemma hol_light8 : forall x y z,
 x ^ 2 + y ^ 2 + z ^ 2 = 1 -> (x + y + z) ^ 2 <= 3.
Proof.
  intros ; psatz Z 2.
Qed.

Lemma hol_light9 : forall w x y z,
 w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1
  -> (w + x + y + z) ^ 2 <= 4.
Proof.
  intros; psatz Z 2.
Qed.

Lemma hol_light10 : forall x y,
 x >= 1 /\ y >= 1 -> x * y >= x + y - 1.
Proof.
  intros ; psatz Z 2.
Qed.

Lemma hol_light11 : forall x y,
 x > 1 /\ y > 1 -> x * y > x + y - 1.
Proof.
  intros ; psatz Z 2.
Qed.


Lemma hol_light12: forall x y z,
  2 <= x /\ x <= 125841 / 50000 /\
  2 <= y /\ y <= 125841 / 50000 /\
  2 <= z /\ z <= 125841 / 50000
   -> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= 0.
Proof.
  intros x y z ; set (e:= (125841 / 50000)).
  compute in e.
  unfold e ; intros ; psatz Z 2.
Qed.

Lemma hol_light14 : forall x y z,
 2 <= x /\ x <= 4 /\ 2 <= y /\ y <= 4 /\ 2 <= z /\ z <= 4
  -> 12 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z).
Proof.
  intros ;psatz Z 2.
Qed.

(* ------------------------------------------------------------------------- *)
(* Inequality from sci.math (see "Leon-Sotelo, por favor").                  *)
(* ------------------------------------------------------------------------- *)

Lemma hol_light16 : forall x y,
  0 <= x /\ 0 <= y /\ (x * y = 1)
   -> x + y <= x ^ 2 + y ^ 2.
Proof.
  intros ; psatz Z 2.
Qed.

Lemma hol_light17 : forall x y,
  0 <= x /\ 0 <= y /\ (x * y = 1)
   -> x * y * (x + y) <= x ^ 2 + y ^ 2.
Proof.
  intros ; psatz Z 3.
Qed.

Lemma hol_light18 : forall x y,
  0 <= x /\ 0 <= y -> x * y * (x + y) ^ 2 <= (x ^ 2 + y ^ 2) ^ 2.
Proof.
  intros ; psatz Z 4.
Qed.

(* ------------------------------------------------------------------------- *)
(* Some examples over integers and natural numbers.                          *)
(* ------------------------------------------------------------------------- *)

Lemma hol_light19 : forall m n, 2 * m + n = (n + m) + m.
Proof.
  intros ; lia.
Qed.

Lemma hol_light22 : forall n, n >= 0 -> n <= n * n.
Proof.
  intros.
  psatz Z 2.
Qed.


Lemma hol_light24 : forall x1 y1 x2 y2, x1 >= 0 -> x2 >= 0 -> y1 >= 0 -> y2 >= 0 ->
  ((x1 + y1) ^2 + x1 + 1 = (x2 + y2) ^ 2 + x2 + 1)
                -> (x1 + y1 = x2 + y2).
Proof.
  intros.
  psatz Z 2.
Qed.

Lemma motzkin' : forall x y, (x^2+y^2+1)*(x^2*y^4 + x^4*y^2 + 1 - 3*x^2*y^2) >= 0.
Proof.
  intros.
  psatz Z 1.
Qed.



Lemma motzkin : forall x y, (x^2*y^4 + x^4*y^2 + 1 - 3*x^2*y^2)  >= 0.
Proof.
  intros.
  generalize (motzkin' x y).
  psatz Z 8.
Qed.
