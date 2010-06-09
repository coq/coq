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
open Environ
open Evd
open Refiner
open Pretyping
open Rawterm
(*i*)

(* Refinement of existential variables. *)

val w_refine : evar * evar_info ->
  rawconstr_ltac_closure -> evar_map -> evar_map

val instantiate_pf_com :
  int -> Topconstr.constr_expr -> pftreestate -> pftreestate

(* the instantiate tactic was moved to [tactics/evar_tactics.ml] *)
