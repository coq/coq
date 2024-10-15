(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type tac_option_locality

val tac_option_locality : tac_option_locality Attributes.attribute

val declare_tactic_option : ?default:Tacexpr.glob_tactic_expr -> string ->
  (* put *) (?loc:Loc.t -> tac_option_locality -> Tacexpr.glob_tactic_expr -> unit) *
  (* get *) (unit -> unit Proofview.tactic) *
  (* print *) (unit -> Pp.t)
