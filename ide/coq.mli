(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Names
open Term
open Environ
open Evd

val version : unit -> string

val init : unit -> string list 
val interp : string -> Util.loc * Vernacexpr.vernac_expr
val interp_last : Util.loc * Vernacexpr.vernac_expr -> unit

val is_tactic : Vernacexpr.vernac_expr -> bool
val is_state_preserving : Vernacexpr.vernac_expr -> bool

(* type hyp = (identifier * constr option * constr) * string *)

type hyp = env * evar_map * 
           ((identifier*string) * constr option * constr) * (string * string)
type concl = env * evar_map * constr * string
type goal = hyp list * concl

val get_current_goals : unit -> goal list

val get_current_goals_nb : unit -> int

val print_no_goal : unit -> string

val process_exn : exn -> string*((int*int) option)

type reset_info = NoReset | Reset of Names.identifier * bool ref

val compute_reset_info : Vernacexpr.vernac_expr -> reset_info
val reset_initial : unit -> unit
val reset_to : identifier -> unit
val reset_to_mod : identifier -> unit

val hyp_menu : hyp -> (string * string) list
val concl_menu : concl -> (string * string) list

val is_in_coq_lib : string -> bool
val is_in_coq_path : string -> bool

val make_cases : string -> string list list


type tried_tactic = 
  | Interrupted
  | Success of int (* nb of goals after *)
  | Failed

val try_interptac: string -> tried_tactic

(* Message to display in lower status bar. *)

val current_status : unit -> string
