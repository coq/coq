(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Names
open Term
open Sign
open Environ
open Evd
open Refiner
open Proof_type
(*i*)

type wc = named_context sigma (* for a better reading of the following *)

(* Refinement of existential variables. *)

val rc_of_glsigma : goal sigma -> wc

(* A [w_tactic] is a tactic which modifies the a set of evars of which
   a goal depend, either by instantiating one, or by declaring a new
   dependent goal *)
type w_tactic = wc -> wc

val w_Declare    : evar -> types -> w_tactic

val w_refine :  evar -> Rawterm.rawconstr  -> w_tactic

val instantiate_pf_com :
  int -> Topconstr.constr_expr -> pftreestate -> pftreestate

(* the instantiate tactic was moved to tactics/evar_tactics.ml *) 
