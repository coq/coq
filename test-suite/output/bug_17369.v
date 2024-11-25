(* Ensure that 'logical inductive' comments in extracted Haskell
 * do not get uncommented by line wrapping *)

From Corelib Require Import Extraction.

Set Printing Width 60.

Inductive my_inductive_prop : Prop :=
  constr_1 | constr_2 | constr_3 | constr_4 | constr_5 | constr_6 | constr_7
.

Extraction Language Haskell.
Extraction my_inductive_prop.
