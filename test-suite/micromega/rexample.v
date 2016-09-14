(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import Lra.
Require Import Reals.

Open Scope R_scope.


Lemma cst_test : 5^5 = 5 * 5 * 5 *5 *5.
Proof.
  lra.
Qed.

Lemma yplus_minus : forall x y,
  0 = x + y -> 0 =  x -y -> 0 = x /\ 0 = y.
Proof.
  intros.
  lra.
Qed.

(* Other (simple) examples *)

Lemma binomial : forall x y, ((x+y)^2 = x^2 + 2 *x*y + y^2).
Proof.
  intros.
  lra.
Qed.


Lemma hol_light19 : forall m n, 2 * m + n = (n + m) + m.
Proof.
  intros ; lra.
Qed.


Lemma vcgen_25 : forall
  (n : R)
  (m : R)
  (jt : R)
  (j : R)
  (it : R)
  (i : R)
  (H0 : 1 * it + (-2%R  ) * i + (-1%R  ) = 0)
  (H :  1 * jt + (-2  ) * j + (-1  ) = 0)
  (H1 : 1 * n + (-10  ) = 0)
  (H2 : 0 <= (-4028  )  * i + (6222  ) * j + (705  )  * m + (-16674  ))
  (H3 : 0 <= (-418  ) * i + (651  ) * j + (94  ) * m + (-1866  ))
  (H4 : 0 <= (-209  ) * i + (302  ) * j + (47  ) * m + (-839  ))
  (H5 : 0 <= (-1  ) * i + 1 * j + (-1  ))
  (H6 : 0 <= (-1  ) * j + 1 * m + (0  ))
  (H7 : 0 <= (1  ) * j + (5  ) * m + (-27  ))
  (H8 : 0 <= (2  ) * j + (-1  ) * m + (2  ))
  (H9 : 0 <= (7  ) * j + (10  ) * m + (-74  ))
  (H10 : 0 <= (18  ) * j + (-139  ) * m + (1188  ))
  (H11 : 0 <= 1  * i + (0  ))
  (H13 : 0 <= (121  )  * i + (810  )  * j + (-7465  ) * m + (64350  )),
  (( 1 ) = (-2  ) * i + it).
Proof.
  intros.
  lra.
Qed.

Goal forall x, -x^2 >= 0 -> x - 1 >= 0 -> False.
Proof.
  intros.
  psatz R 3.
Qed.

Lemma motzkin' : forall x y, (x^2+y^2+1)*(x^2*y^4 + x^4*y^2 + 1 - (3 ) *x^2*y^2) >= 0.
Proof.
  intros ; psatz R 2.
Qed.

Lemma l1 : forall x y z : R, Rabs (x - z) <= Rabs (x - y) + Rabs (y - z).
intros; split_Rabs; lra.
Qed.

(*  Bug 5073 *)
Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
Proof.
  lra.
Qed.
