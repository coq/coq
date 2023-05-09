Require Import Ltac2.Ltac2.

Set Primitive Projections.
Record R A := mkR { r : A }.

Ltac2 Type exn ::= [ E (constr) ].

Set Printing Projections.
Set Printing Primitive Projection Parameters.

Fail Ltac2 Eval Control.zero (E open_constr:(_.(r _))).
(* Error: Uncaught Ltac2 exception: E (constr:(...)) *)
