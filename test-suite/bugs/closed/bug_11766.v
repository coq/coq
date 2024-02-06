Require Import Program.Tactics.

Set Universe Polymorphism.
(* needed because we don't enforce universe declarations on
   obligations, in univ poly mode however the universes must be
   redeclared for the main definition so we do see the error *)

Program Definition bla@{} : nat := _.
Next Obligation.
  let x := constr:(Type) in exact 0.
Defined. (* unbound univ *)

Program Fixpoint blo@{} (s : bool) : nat := _.
Next Obligation.
  let x := constr:(Type) in exact 0.
Defined. (* unbound univ *)
