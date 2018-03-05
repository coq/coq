(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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
