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
open Vernacexpr
(*i*)

(* Vernacular entries. This module registers almost all the vernacular entries,
   by side-effects using [Vernacinterp.vinterp_add]. *)

(* Moved to g_vernac.ml4
val join_binders : ('a list * 'b) list -> ('a * 'b) list
*)

(* Synonym for Vernacinterp.vinterp_add
val add : string -> (Vernacexpr.vernac_arg list -> unit -> unit) -> unit
*)

val show_script : unit -> unit
val show_prooftree : unit -> unit
val show_open_subgoals : unit -> unit
val show_nth_open_subgoal : int -> unit

(* Merged with show_open_subgoals !
val show_open_subgoals_focused : unit -> unit
*)

val show_node : unit -> unit

(* This function can be used by any command that want to observe terms
   in the context of the current goal, as for instance in pcoq *)
val get_current_context_of_args : int option -> Evd.evar_map * Environ.env

(* this function is used to analyse the extra arguments in search commands.
   It is used in pcoq. *) (*i anciennement: inside_outside i*)
(*
val interp_search_restriction : search_restriction -> dir_path list * bool
*)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : Libnames.qualid Util.located -> unit;
  print_check : Environ.unsafe_judgment -> unit;
  print_eval : (constr -> constr) -> Environ.env -> Coqast.t -> Environ.unsafe_judgment -> unit;
  show_goal : int option -> unit
}

val set_pcoq_hook : pcoq_hook -> unit

(* This function makes sure that the function given is argument is preceded
   by a command aborting all proofs if necessary.
   It is used in pcoq. *)
val abort_refine : ('a -> unit) -> 'a -> unit;;

val interp : Vernacexpr.vernac_expr -> unit
