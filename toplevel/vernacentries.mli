
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

(* This function is used to transform a qualified identifier into a
   global reference, with a nice error message in case of failure.
   It is used in pcoq. *)
val global : Coqast.loc -> qualid -> global_reference;;

(* this function is used to analyse the extra arguments in search commands.
   It is used in pcoq. *)
val inside_outside : vernac_arg list -> dir_path list * bool;;
