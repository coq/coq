(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Globnames
open Rules

val collect_quantified : Evd.evar_map -> Sequent.t -> Formula.t list * Sequent.t

val give_instances : Evd.evar_map -> Formula.t list -> Sequent.t ->
  (Unify.instance * global_reference) list

val quantified_tac : Formula.t list -> seqtac with_backtracking




