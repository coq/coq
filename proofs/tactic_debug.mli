(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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

(* Prints a constr *)
val db_constr : debug_info -> Environ.env -> constr -> unit

(* Prints a matched hypothesis *)
val db_matched_hyp : debug_info -> Environ.env -> string * constr -> unit

(* Prints the matched conclusion *)
val db_matched_concl : debug_info -> Environ.env -> constr -> unit
