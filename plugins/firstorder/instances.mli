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
open Rules

val collect_quantified : Evd.evar_map -> Sequent.t -> Formula.t list * Sequent.t

val give_instances : Environ.env -> Evd.evar_map -> Formula.t list -> Sequent.t ->
  (Unify.instance * GlobRef.t) list

val quantified_tac : Formula.t list -> seqtac with_backtracking




