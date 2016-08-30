(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import Lqa.
Require Import QArith.

Lemma plus_minus : forall x y,
  0 == x + y -> 0 ==  x -y -> 0 == x /\ 0 == y.
Proof.
  intros.
  lra.
Qed.

(* Other (simple) examples *)
Open Scope Q_scope.

Lemma binomial : forall x y:Q, ((x+y)^2 == x^2 + (2 # 1) *x*y + y^2).
Proof.
  intros.
  lra.
Qed.


Lemma hol_light19 : forall m n, (2 # 1) * m + n == (n + m) + m.
Proof.
  intros ; lra.
Qed.
Open Scope Z_scope.
Open Scope Q_scope.

Lemma vcgen_25 : forall
  (n : Q)
  (m : Q)
  (jt : Q)
  (j : Q)
  (it : Q)
  (i : Q)
  (H0 : 1 * it + (-2 # 1) * i + (-1 # 1) == 0)
  (H :  1 * jt + (-2 # 1) * j + (-1 # 1) == 0)
  (H1 : 1 * n + (-10 # 1) = 0)
  (H2 : 0 <= (-4028 # 1)  * i + (6222 # 1) * j + (705 # 1)  * m + (-16674 # 1))
  (H3 : 0 <= (-418 # 1) * i + (651 # 1) * j + (94 # 1) * m + (-1866 # 1))
  (H4 : 0 <= (-209 # 1) * i + (302 # 1) * j + (47 # 1) * m + (-839 # 1))
  (H5 : 0 <= (-1 # 1) * i + 1 * j + (-1 # 1))
  (H6 : 0 <= (-1 # 1) * j + 1 * m + (0 # 1))
  (H7 : 0 <= (1 # 1) * j + (5 # 1) * m + (-27 # 1))
  (H8 : 0 <= (2 # 1) * j + (-1 # 1) * m + (2 # 1))
  (H9 : 0 <= (7 # 1) * j + (10 # 1) * m + (-74 # 1))
  (H10 : 0 <= (18 # 1) * j + (-139 # 1) * m + (1188 # 1))
  (H11 : 0 <= 1  * i + (0 # 1))
  (H13 : 0 <= (121 # 1)  * i + (810 # 1)  * j + (-7465 # 1) * m + (64350 # 1)),
  (( 1# 1) == (-2 # 1) * i + it).
Proof.
  intros.
  lra.
Qed.

Goal forall x : Q, x * x >= 0.
  intro; nra. 
Qed.

Goal forall x, -x^2 >= 0 -> x - 1 >= 0 -> False.
Proof.
  intros.
  psatz Q 3.
Qed.

Lemma motzkin' : forall x y, (x^2+y^2+1)*(x^2*y^4 + x^4*y^2 + 1 - (3 # 1) *x^2*y^2) >= 0.
Proof.
  intros ; psatz Q 3.
Qed.



