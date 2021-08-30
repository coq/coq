(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Libnames
open Vernacexpr
open Notation

(** * Number notation *)

type number_string_via = qualid * (bool * qualid * qualid) list
type number_option =
  | After of numnot_option
  | Via of number_string_via

val vernac_number_notation : locality_flag ->
                             qualid ->
                             qualid -> qualid ->
                             number_option list ->
                             Notation_term.scope_name -> unit

(** These are also used in string notations *)
val locate_global_inductive : bool -> Libnames.qualid -> Names.inductive * Constr.t option list
val elaborate_to_post_params : Environ.env -> Evd.evar_map -> Names.inductive -> Constr.t option list -> (Names.GlobRef.t * Names.GlobRef.t * Notation.to_post_arg list) list array * Names.GlobRef.t list
val elaborate_to_post_via : Environ.env -> Evd.evar_map -> Libnames.qualid -> Names.inductive -> (bool * Libnames.qualid * Libnames.qualid) list -> (Names.GlobRef.t * Names.GlobRef.t * Notation.to_post_arg list) list array * Names.GlobRef.t list
