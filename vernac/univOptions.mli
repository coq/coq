(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Global settings for universe polymorphism and cumulativity *)

(** For internal use. *)
val universe_polymorphism_option_name : string list

val is_universe_polymorphism : unit -> bool
val is_cumulative : PolyFlags.construction_kind -> bool
val should_collapse_sort_variables : unit -> bool

val poly_for_ind : Declarations.mutual_inductive_body -> PolyFlags.t
