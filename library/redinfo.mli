
(* $Id$ *)

(*i*)
open Names
open Term
(*i*)

(* Elimination constants. This module implements a table which associates
   to each constant some reduction informations used by tactics like Simpl. 
   The following table is mostly used by the module [Tacred] 
   (section~\refsec{tacred}). *)

type constant_evaluation = 
  | Elimination of (int * constr) list * int * bool
  | NotAnElimination

val constant_eval : section_path -> constant_evaluation

