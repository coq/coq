(* Test apply in *)

Goal (forall x y, x = S y -> y=y) -> 2 = 4 -> 3=3.
intros H H0.
apply H in H0.
assumption.
Qed.

Require Import ZArith.
Open Scope Z_scope.
Goal forall x y z, ~ z <= 0 -> x * z < y * z -> x <= y.
intros; apply Znot_le_gt, Zgt_lt in H.
apply Zmult_lt_reg_r, Zlt_le_weak in H0; auto.
Qed.

(* Check if it unfolds when there are not enough premises *)

Goal forall n, n = S n -> False.
intros.
apply n_Sn in H.
assumption.
Qed.

(* Check naming in with bindings; printing used to be inconsistent before *)
(* revision 9450 *)

Notation S':=S (only parsing).
Goal (forall S, S = S' S) -> (forall S, S = S' S).
intros.
apply H with (S0 := S).
