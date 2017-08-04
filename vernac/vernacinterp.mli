(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Interpretation of extended vernac phrases. *)

type deprecation = bool
type vernac_command = Genarg.raw_generic_argument list -> unit -> unit

val vinterp_add : deprecation -> Vernacexpr.extend_name ->
  vernac_command -> unit
val overwriting_vinterp_add :
  Vernacexpr.extend_name -> vernac_command -> unit

val vinterp_init : unit -> unit

val call : ?locality:bool -> Vernacexpr.extend_name * Genarg.raw_generic_argument list -> unit
(** This function is responsible for interpreting [Vernacexpr.VernacExtend] commands.
    It is called by {!Vernacentries.interp} function. *)
