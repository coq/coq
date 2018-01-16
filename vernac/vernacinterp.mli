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
  polymorphic : bool;
  program : bool;
}

type 'a vernac_command = 'a -> atts:atts -> st:Vernacstate.t -> Vernacstate.t

type plugin_args = Genarg.raw_generic_argument list

val vinterp_init : unit -> unit
val vinterp_add : deprecation -> Vernacexpr.extend_name -> plugin_args vernac_command -> unit
val overwriting_vinterp_add : Vernacexpr.extend_name -> plugin_args vernac_command -> unit

val call : Vernacexpr.extend_name -> plugin_args -> atts:atts -> st:Vernacstate.t -> Vernacstate.t
