Require Import Program.Tactics.

Definition bla (A:Type) := A.
Existing Class bla.

Program Instance fubar : bla nat := {}.
Next Obligation.
Fail exact bool.
exact 0.
Qed.
