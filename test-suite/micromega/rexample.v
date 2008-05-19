(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

Require Import Micromegatac.
Require Import Reals.
Require Import Ring_normalize.

Open Scope R_scope.

Lemma plus_minus : forall x y, 
  0 = x + y -> 0 =  x -y -> 0 = x /\ 0 = y.
Proof.
  intros.
  omicron R.
Qed.

(* Other (simple) examples *)

Lemma binomial : forall x y, ((x+y)^2 = x^2 + 2 *x*y + y^2).
Proof.
  intros.
  omicron R.
Qed.


Lemma hol_light19 : forall m n, 2 * m + n = (n + m) + m.
Proof.
  intros ; omicron R.
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
  omicron R.
Qed.
