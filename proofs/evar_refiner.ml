(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Pp
open Util
open Names
open Rawterm
open Term
open Termops
open Environ
open Evd
open Sign
open Reductionops
open Typing
open Tacred
open Proof_trees
open Proof_type
open Logic
open Refiner
open Tacexpr
open Nameops


type wc = named_context sigma (* for a better reading of the following *)

let rc_of_glsigma sigma = rc_of_gc sigma.sigma sigma.it

type w_tactic = named_context sigma -> named_context sigma

let extract_decl sp evc =
  let evdmap = evc.sigma in
  let evd = Evd.map evdmap sp in 
    { it = evd.evar_hyps;
      sigma = Evd.rmv evdmap sp }

let restore_decl sp evd evc =
  (rc_add evc (sp,evd))

(******************************************)
(* Instantiation of existential variables *)
(******************************************)

(* w_tactic pour instantiate *) 

let w_refine ev rawc wc =
  if Evd.is_defined wc.sigma ev then 
    error "Instantiate called on already-defined evar";
  let e_info = Evd.map wc.sigma ev in
  let env = Evarutil.evar_env e_info in
  let evd,typed_c = 
    Pretyping.understand_gen_tcc wc.sigma env [] 
      (Some e_info.evar_concl) rawc in
  let inst_info = {e_info with evar_body = Evar_defined typed_c } in
    restore_decl ev inst_info (extract_decl ev {wc with sigma=evd})
 (*   w_Define ev typed_c {wc with sigma=evd} *)

(* the instantiate tactic was moved to tactics/evar_tactics.ml *) 

(* vernac command Existential *)

let instantiate_pf_com n com pfts = 
  let gls = top_goal_of_pftreestate pfts in
  let wc = project_with_focus gls in
  let sigma = wc.sigma in 
  let (sp,evd) (* as evc *) = 
    try
      List.nth (Evarutil.non_instantiated sigma) (n-1) 
    with Failure _ -> 
      error "not so many uninstantiated existential variables"
  in 
  let e_info = Evd.map sigma sp in
  let env = Evarutil.evar_env e_info in
  let rawc = Constrintern.interp_rawconstr sigma env com in 
  let wc' = w_refine sp rawc wc in
  change_constraints_pftreestate wc'.sigma pfts
