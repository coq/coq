
(*i $Id$ i*)

(*i*)
open Names
open Tacmach
(*i*)

(* Programmable destruction of hypotheses and conclusions. *)

val dHyp : identifier -> tactic
val dConcl : tactic
