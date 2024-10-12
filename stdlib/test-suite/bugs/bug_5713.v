(* Checking that classical_right/classical_left work in an empty context *)

Require Import Classical.

Parameter A:Prop.

Goal A \/ ~A.
classical_right.
assumption.
Qed.

Goal ~A \/ A.
classical_left.
assumption.
Qed.
