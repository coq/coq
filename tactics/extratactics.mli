(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

open Util
open Names
open Term
open Proof_type
open Rawterm
open Tacexpr
open Topconstr
open Genarg

val h_discrHyp : quantified_hypothesis -> tactic
val h_injHyp : quantified_hypothesis -> tactic

val refine_tac : Genarg.open_constr -> tactic



(* Julien: Mise en commun des differentes version de replace with in by 
   TODO:  deplacer dans extraargs

*)


val rawwit_in_arg_hyp: identifier located option raw_abstract_argument_type

val in_arg_hyp: identifier located option Pcoq.Gram.Entry.e



val rawwit_by_arg_tac :
  (raw_tactic_expr option, constr_expr, raw_tactic_expr) abstract_argument_type
  
val by_arg_tac : Tacexpr.raw_tactic_expr option Pcoq.Gram.Entry.e
