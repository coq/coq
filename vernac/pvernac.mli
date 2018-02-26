(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pcoq
open Genredexpr
open Vernacexpr

val uvernac : gram_universe

module Vernac_ :
  sig
    val gallina : vernac_expr Gram.entry
    val gallina_ext : (vernac_flag list * vernac_expr) Gram.entry
    val command : vernac_expr Gram.entry
    val syntax : vernac_expr Gram.entry
    val vernac_control : vernac_control Gram.entry
    val rec_definition : (fixpoint_expr * decl_notation list) Gram.entry
    val noedit_mode : vernac_expr Gram.entry
    val command_entry : vernac_expr Gram.entry
    val red_expr : raw_red_expr Gram.entry
    val hint_info : Hints.hint_info_expr Gram.entry
  end

(** The main entry: reads an optional vernac command *)
val main_entry : (Loc.t * vernac_control) option Gram.entry

(** Handling of the proof mode entry *)
val get_command_entry : unit -> vernac_expr Gram.entry
val set_command_entry : vernac_expr Gram.entry -> unit
