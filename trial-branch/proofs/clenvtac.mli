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
open Tacexpr
(*i*)

(* Tactics *)
val unify : constr -> tactic
val clenv_refine : evars_flag -> clausenv -> tactic
val res_pf : clausenv -> ?with_evars:evars_flag -> ?allow_K:bool -> tactic
val elim_res_pf_THEN_i : clausenv -> (clausenv -> tactic array) -> tactic

(* Compatibility, use res_pf ?with_evars:true instead *)
val e_res_pf : clausenv -> tactic
