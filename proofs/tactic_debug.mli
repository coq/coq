
(*i $Id$ i*)

open Proof_type
open Term

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn
  | DebugOff
  | Exit

(* Prints the state and waits *)
val debug_prompt : goal sigma option -> Coqast.t -> debug_info

(* Prints a matched hypothesis *)
val db_matched_hyp : debug_info -> Environ.env -> string * constr -> unit

(* Prints the matched conclusion *)
val db_matched_concl : debug_info -> Environ.env -> constr -> unit
