(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

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
open Instantiate
open Tacred
open Proof_trees
open Proof_type
open Logic
open Refiner
open Tacexpr
open Nameops


type wc = named_context sigma (* for a better reading of the following *)

let rc_of_pfsigma sigma = rc_of_gc sigma.sigma sigma.it.goal
let rc_of_glsigma sigma = rc_of_gc sigma.sigma sigma.it

type w_tactic = named_context sigma -> named_context sigma

let startWalk gls =
  let evc = project_with_focus gls in
  (evc,
   (fun wc' gls' ->
      if not !Options.debug or (gls.it = gls'.it) then
(*        if Intset.equal (get_lc gls.it) (get_focus (ids_it wc')) then*)
          tclIDTAC {it=gls'.it; sigma = (get_gc wc')}
(*        else
          (local_Constraints (get_focus (ids_it wc'))
             {it=gls'.it; sigma = get_gc (ids_it wc')})*)
      else error "Walking"))

let extract_decl sp evc =
  let evdmap = evc.sigma in
  let evd = Evd.map evdmap sp in 
    { it = evd.evar_hyps;
      sigma = Evd.rmv evdmap sp }

let restore_decl sp evd evc =
  (rc_add evc (sp,evd))


(* [w_Focusing sp wt wc]
 *
 * Focuses the walking context WC onto the declaration SP, given that
 * this declaration is UNDEFINED.  Then, it runs the walking_tactic,
 * WT, on this new context.  When the result is returned, we recover
 * the resulting focus (access list) and restore it to SP's declaration.
 *
 * It is an error to cause SP to change state while we are focused on it. *)

(* let w_Focusing_THEN sp (wt : 'a result_w_tactic) (wt' : 'a -> w_tactic)
                       (wc : named_context sigma) =
  let hyps  = wc.it
  and evd   = Evd.map wc.sigma sp in
  let (wc' : named_context sigma) = extract_decl sp wc in
  let (wc'',rslt) = wt wc' in 
(*  if not (ids_eq wc wc'') then error "w_saving_focus"; *)
  if wc'==wc'' then 
    wt' rslt wc
  else 
    let wc''' = restore_decl sp evd wc'' in 
    wt' rslt {it = hyps; sigma = wc'''.sigma} *)
      
let w_add_sign (id,t) (wc : named_context sigma) =
  { it = Sign.add_named_decl (id,None,t) wc.it;
    sigma = wc.sigma }

let w_Focus sp wc = extract_decl sp wc

let w_Underlying wc = wc.sigma
let w_whd wc c      = Evarutil.whd_castappevar (w_Underlying wc) c
let w_type_of wc c  =
  type_of (Global.env_of_context wc.it) wc.sigma c
let w_env     wc    = get_env wc
let w_hyps    wc    = named_context (get_env wc)
let w_defined_evar wc k      = Evd.is_defined (w_Underlying wc) k
let w_const_value wc         = constant_value (w_env wc)
let w_conv_x wc m n          = is_conv (w_env wc) (w_Underlying wc) m n
let w_whd_betadeltaiota wc c = whd_betadeltaiota (w_env wc) (w_Underlying wc) c
let w_hnf_constr wc c        = hnf_constr (w_env wc) (w_Underlying wc) c


let w_Declare sp ty (wc : named_context sigma) =
  let _ = w_type_of wc ty in (* Utile ?? *)
  let sign = get_hyps wc in
  let newdecl = mk_goal sign ty in 
  ((rc_add wc (sp,newdecl)): named_context sigma)

let w_Define sp c wc =
  let spdecl = Evd.map (w_Underlying wc) sp in
  let cty = 
    try 
      w_type_of (w_Focus sp wc) (mkCast (c,spdecl.evar_concl))
    with 
	Not_found -> error "Instantiation contains unlegal variables"
      | (Type_errors.TypeError (e, Type_errors.UnboundVar v))-> 
      errorlabstrm "w_Define"
      (str "Cannot use variable " ++ pr_id v ++ str " to define " ++ 
       str (string_of_existential sp))
  in 
  match spdecl.evar_body with
    | Evar_empty ->
    	let spdecl' = { evar_hyps = spdecl.evar_hyps;
                       	evar_concl = spdecl.evar_concl;
                       	evar_body = Evar_defined c }
    	in 
	  Proof_trees.rc_add wc (sp,spdecl')
    | _ -> error "define_evar"


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
  let sigma = (w_Underlying wc) in 
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
  let newgc = (w_Underlying wc') in
    change_constraints_pftreestate newgc pfts
