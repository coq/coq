(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

open Term
open Tacmach
open Names
open Libnames

type hptac= Sequent.t -> (Sequent.t -> tactic) -> Formula.counter -> tactic

type lhptac= global_reference -> hptac

val wrap : int -> bool -> hptac

val clear_global: global_reference -> tactic

val axiom_tac : constr -> Sequent.t -> tactic

val and_tac : hptac

val left_and_tac : inductive -> lhptac

val or_tac : hptac

val left_or_tac : inductive -> lhptac

val forall_tac : hptac

val left_forall_tac : int -> types -> (bool * constr) list -> lhptac

val arrow_tac : hptac

val exists_tac : int -> types -> (bool * constr) list -> hptac
	       
val left_exists_tac : lhptac

val ll_arrow_tac : constr -> constr -> constr -> lhptac

val ll_atom_tac : constr -> lhptac

val ll_false_tac : lhptac

val left_false_tac : global_reference -> tactic

val ll_ind_tac : inductive -> constr list -> lhptac

val ll_forall_tac : types -> lhptac
