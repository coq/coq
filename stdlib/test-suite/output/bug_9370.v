From Stdlib Require Import Reals.
Open Scope R_scope.
Goal 1/1=1.
Proof.
  field_simplify (1/1).
Show.
  field_simplify.
Show.
  field_simplify.
Show.
  reflexivity.
Qed.
