(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Vernacinterp
(*i*)

(* Vernacular entries. This module registers almost all the vernacular entries,
   by side-effects using [Vernacinterp.vinterp_add]. *)

val join_binders : ('a list * 'b) list -> ('a * 'b) list
val add : string -> (vernac_arg list -> unit -> unit) -> unit
val show_script : unit -> unit
val show_prooftree : unit -> unit
val show_open_subgoals : unit -> unit
val show_nth_open_subgoal : int -> unit
val show_open_subgoals_focused : unit -> unit
val show_node : unit -> unit

(* This function can be used by any command that want to observe terms
   in the context of the current goal, as for instance in pcoq *)
val get_current_context_of_args : vernac_arg list -> Proof_type.enamed_declarations * Environ.env

(* this function is used to analyse the extra arguments in search commands.
   It is used in pcoq. *)
val inside_outside : vernac_arg list -> dir_path list * bool;;

(* This function makes sure that the function given is argument is preceded
   by a command aborting all proofs if necessary.
   It is used in pcoq. *)
val abort_refine : ('a -> unit) -> 'a -> unit;;
