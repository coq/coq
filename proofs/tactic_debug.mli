(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Proof_type
open Names
open Term

(* This module intends to be a beginning of debugger for tactic expressions.
   Currently, it is quite simple and we can hope to have, in the future, a more
   complete panel of commands dedicated to a proof assistant framework *)

(* Debug information *)
type debug_info =
  | DebugOn of int
  | DebugOff
  | Exit

(* Prints the state and waits *)
val debug_prompt : int -> goal sigma option -> Tacexpr.raw_tactic_expr ->
      (debug_info -> 'a) -> (unit -> 'a) -> 'a

(* Prints a constr *)
val db_constr : debug_info -> Environ.env -> constr -> unit

(* Prints a matched hypothesis *)
val db_matched_hyp : debug_info -> Environ.env -> identifier * constr -> unit

(* Prints the matched conclusion *)
val db_matched_concl : debug_info -> Environ.env -> constr -> unit
