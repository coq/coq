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
(** For each "rule"
    (see the [rule] non-teriminal defined in [grammar/vernacextend.mlp] file)
    camlp5 generates one function of the [vernac_command] type which
    defines how a given Vernacular command, introduced by the "rule",
    should be interpreted.

    The actual arguments of the Vernacular command
    (see the [args] non-terminal defined in [grammar/vernacextend.mlp] file)
    are passed via the first parameter of this function. *)

val vinterp_add : deprecation -> Vernacexpr.extend_name ->
  vernac_command -> unit
val overwriting_vinterp_add :
  Vernacexpr.extend_name -> vernac_command -> unit

val vinterp_init : unit -> unit

val call : ?locality:bool -> Vernacexpr.extend_name * Genarg.raw_generic_argument list -> unit
(** This function is responsible for interpreting [Vernacexpr.VernacExtend] commands.
    It is called by {!Vernacentries.interp} function. *)
