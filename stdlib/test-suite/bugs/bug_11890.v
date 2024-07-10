From Stdlib Require Import Orders ZArith Mergesort.
(* Note that this has always worked fine without the '; we are testing importing notations from the stdlib here *)
Declare Module A : LeBool'.
Declare Module B : LtBool'.
Import A B NatOrder.
(*
Error: Notation "_ <=? _" is already defined at level 70 with arguments constr
at next level, constr at next level while it is now required to be at level 35
with arguments constr at next level, constr at next level.
*)
