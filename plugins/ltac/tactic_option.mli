(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Tacexpr
open Vernacexpr

val declare_tactic_option : ?default:Tacexpr.glob_tactic_expr -> string -> 
  (* put *) (locality_flag -> glob_tactic_expr -> unit) *
  (* get *) (unit -> locality_flag * unit Proofview.tactic) *
  (* print *) (unit -> Pp.t)
