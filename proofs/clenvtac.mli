(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Clenv
open Proof_type
(*i*)

(* Tactics *)
val unify : constr -> tactic
val clenv_refine : wc clausenv -> tactic
val res_pf      : wc clausenv -> tactic
val res_pf_cast : wc clausenv -> tactic
val elim_res_pf : wc clausenv -> bool -> tactic
val e_res_pf : wc clausenv -> tactic
val elim_res_pf_THEN_i : wc clausenv -> (wc clausenv -> tactic array) -> tactic
