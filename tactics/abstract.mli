(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open EConstr

val cache_term_by_tactic_then
  :  opaque:bool
  -> name_op:Id.t option
  -> ?goal_type:(constr option)
  -> unit Proofview.tactic
  -> (constr -> constr list -> unit Proofview.tactic)
  -> unit Proofview.tactic

val tclABSTRACT : ?opaque:bool -> Id.t option -> unit Proofview.tactic -> unit Proofview.tactic
