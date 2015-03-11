(* Supporting tactic notations within Ltac in the presence of an
  "ident" entry which does not expect a fresh ident *)
(* Of course, this is a matter of convention of what "ident" is
   supposed to denote, but in practice, it seems more convenient to
   have less constraints on ident at interpretation time, as
   otherwise more ad hoc entries would be necessary (as e.g. a special
   "quantified_hypothesis" entry for dependent destruction). *)
Require Import Program.
Goal nat -> Type.
  intro x.
  lazymatch goal with
  | [ x : nat |- _ ] => dependent destruction x
  end.
