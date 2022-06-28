Require Import Program.Tactics.

Definition bla (A:Type) := A.
Existing Class bla.

#[export] Program Instance fubar : bla nat := {}.
Next Obligation.
Fail exact bool.
exact 0.
Qed.
