(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Interpretation of extended vernac phrases. *)

type deprecation = bool

type atts = {
  loc : Loc.t option;
  locality : bool option;
}

type vernac_command =
  Genarg.raw_generic_argument list ->
  atts:atts -> st:Vernacstate.t ->
  Vernacstate.t

val vinterp_add : deprecation -> Vernacexpr.extend_name -> vernac_command -> unit

val overwriting_vinterp_add : Vernacexpr.extend_name -> vernac_command -> unit

val vinterp_init : unit -> unit

val call : ?locality:bool -> ?loc:Loc.t ->
  Vernacexpr.extend_name * Genarg.raw_generic_argument list ->
  st:Vernacstate.t -> Vernacstate.t
