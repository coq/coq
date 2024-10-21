(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Procq
open Genredexpr
open Vernacexpr

type proof_mode

module Vernac_ :
  sig
    val gallina : synpure_vernac_expr Entry.t
    val gallina_ext : vernac_expr Entry.t
    val command : vernac_expr Entry.t
    val syntax : vernac_expr Entry.t
    val vernac_control : vernac_control Entry.t
    val inductive_or_record_definition : (inductive_expr * notation_declaration list) Entry.t
    val fix_definition : fixpoint_expr Entry.t
    val noedit_mode : vernac_expr Entry.t
    val command_entry : vernac_expr Entry.t
    val main_entry : vernac_control option Entry.t
    val red_expr : raw_red_expr Entry.t
    val hint_info : hint_info_expr Entry.t
  end

(* To be removed when the parser is made functional wrt the tactic
 * non terminal *)
module Unsafe : sig
  (* To let third party grammar entries reuse Vernac_ and
   * do something with the proof mode *)
  val set_tactic_entry : proof_mode option -> unit
end

(** The main entry: reads an optional vernac command *)
val main_entry : proof_mode option -> vernac_control option Entry.t

(** Grammar entry for tactics: proof mode(s).
  By default Coq's grammar has an empty entry (non-terminal) for
  tactics.  A plugin can register its non-terminal by providing a name
  and a grammar entry.

  For example the Ltac plugin register the "Classic" grammar
  entry for parsing its tactics.
  *)

val register_proof_mode : string -> Vernacexpr.vernac_expr Entry.t -> proof_mode
val lookup_proof_mode : string -> proof_mode option
val proof_mode_to_string : proof_mode -> string
val list_proof_modes : unit -> Vernacexpr.vernac_expr Entry.t CString.Map.t
