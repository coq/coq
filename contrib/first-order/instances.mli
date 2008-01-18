(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Term
open Names
open Libnames
open Rules
  
val collect_quantified : Sequent.t -> Formula.t list * Sequent.t

val give_instances : Formula.t list -> Sequent.t -> 
  (Unify.instance * global_reference) list

val quantified_tac : Formula.t list -> seqtac with_backtracking




