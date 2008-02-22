(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Vernacinterp
open Vernacexpr
open Topconstr
(*i*)

(* Vernacular entries *)

val show_script : unit -> unit
val show_prooftree : unit -> unit

val show_node : unit -> unit

(* This function can be used by any command that want to observe terms
   in the context of the current goal, as for instance in pcoq *)
val get_current_context_of_args : int option -> Evd.evar_map * Environ.env

(*i
(* this function is used to analyse the extra arguments in search commands.
   It is used in pcoq. *) (*i anciennement: inside_outside i*)
val interp_search_restriction : search_restriction -> dir_path list * bool
i*)

type pcoq_hook = {
  start_proof : unit -> unit;
  solve : int -> unit;
  abort : string -> unit;
  search : searchable -> dir_path list * bool -> unit;
  print_name : Libnames.reference -> unit;
  print_check : Environ.env -> Environ.unsafe_judgment -> unit;
  print_eval : Reductionops.reduction_function -> Environ.env -> Evd.evar_map -> constr_expr ->
    Environ.unsafe_judgment -> unit;
  show_goal : int option -> unit
}

val set_pcoq_hook : pcoq_hook -> unit

(* This function makes sure that the function given in argument is preceded
   by a command aborting all proofs if necessary.
   It is used in pcoq. *)
val abort_refine : ('a -> unit) -> 'a -> unit;;

val interp : Vernacexpr.vernac_expr -> unit

val vernac_reset_name : identifier Util.located -> unit 
