Require Import ZArith.
Require Import Micromegatac.
Open Scope Z_scope.

Lemma two_x_eq_1 : forall x, 2 * x = 1 -> False.
Proof.
  intros.
  omicron Z.
Qed.

Lemma two_x_y_eq_1 : forall x y, 2 * x + 2 * y = 1 -> False.
Proof.
  intros.
  omicron Z.
Qed.

Lemma two_x_y_z_eq_1 : forall x y z, 2 * x + 2 * y + 2 * z= 1 -> False.
Proof.
  intros.
  omicron Z.
Qed.

Lemma omega_nightmare : forall x y, 27 <= 11 * x + 13 * y <= 45 -> 7 * x - 9 * y = 4 -> -10 <= 7 * x - 9 * y <= 4 -> False.
Proof.
  intros ; intuition auto.
  omicron Z.
Qed.  
