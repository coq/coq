(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

open Term
open Tacmach
open Names
open Libnames
open Rules
  
val give_right_instances : metavariable -> constr -> bool -> Formula.atoms -> 
  Sequent.t -> Unify.instance list option

val give_left_instances : Formula.left_formula list-> Sequent.t -> 
  (Unify.instance*global_reference) list

val collect_forall : Sequent.t -> Formula.left_formula list * Sequent.t

val left_instance_tac : Unify.instance * global_reference -> seqtac

val left_forall_tac : Formula.left_formula list -> seqtac

val dummy_exists_tac : constr -> seqtac

val right_instance_tac : Unify.instance -> seqtac

val exists_tac : Unify.instance list -> seqtac
	       






