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
open Stamps
open Names
open Term
open Environ
open Evd
open Reductionops
open Typing
open Instantiate
open Tacred
open Proof_trees
open Proof_type
open Logic
open Refiner

let rc_of_pfsigma sigma = rc_of_gc sigma.sigma sigma.it.goal
let rc_of_glsigma sigma = rc_of_gc sigma.sigma sigma.it

type walking_constraints = readable_constraints idstamped
type 'a result_w_tactic = walking_constraints -> walking_constraints * 'a
type w_tactic = walking_constraints -> walking_constraints


let local_Constraints lc gs = refiner Change_evars gs

let startWalk gls =
  let evc = project_with_focus gls in
  let wc = (ids_mk evc) in 
  (wc,
   (fun wc' gls' ->
      if not !Options.debug or (ids_eq wc wc' & gls.it = gls'.it) then
(*        if Intset.equal (get_lc gls.it) (get_focus (ids_it wc')) then*)
          tclIDTAC {it=gls'.it; sigma = get_gc (ids_it wc')}
(*        else
          (local_Constraints (get_focus (ids_it wc'))
             {it=gls'.it; sigma = get_gc (ids_it wc')})*)
      else error "Walking"))

let walking_THEN wt rt gls =
  let (wc,kONT) = startWalk gls in
  let (wc',rslt) = wt wc in 
  tclTHEN (kONT wc') (rt rslt) gls

let walking wt = walking_THEN (fun wc -> (wt wc,())) (fun () -> tclIDTAC)

let extract_decl sp evc =
  let evdmap = (ts_it evc).decls in
  let evd = Evd.map evdmap sp in 
  (ts_mk { hyps = evd.evar_hyps;
           decls = Evd.rmv evdmap sp })

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

let w_Focusing_THEN sp (wt : 'a result_w_tactic) (wt' : 'a -> w_tactic)
                       (wc : walking_constraints) =
  let hyps  = (ts_it (ids_it wc)).hyps
  and evd   = Evd.map (ts_it (ids_it wc)).decls sp in
  let (wc' : walking_constraints) = ids_mod (extract_decl sp) wc in
  let (wc'',rslt) = wt wc' in 
  if not (ids_eq wc wc'') then error "w_saving_focus";
  if ts_eq (ids_it wc') (ids_it wc'') then 
    wt' rslt wc
  else 
    let wc''' = ids_mod (restore_decl sp evd) wc'' in 
    wt' rslt
      (ids_mod
         (ts_mod (fun evc ->
                    { hyps = hyps;
                      decls = evc.decls }))
         wc''')
      
let w_add_sign (id,t) (wc : walking_constraints) =
  ids_mk (ts_mod
            (fun evr ->
	       { hyps = Sign.add_named_decl (id,None,t) evr.hyps;
		 decls = evr.decls })
            (ids_it wc))

let ctxt_type_of evc c = 
  type_of (Global.env_of_context (ts_it evc).hyps) (ts_it evc).decls c

let w_IDTAC wc = wc

let w_Focusing sp wt = 
  w_Focusing_THEN sp (fun wc -> (wt wc,())) (fun _ -> w_IDTAC)

let w_Focus sp wc = ids_mod (extract_decl sp) wc

let w_Underlying wc = (ts_it (ids_it wc)).decls
let w_whd wc c      = Evarutil.whd_castappevar (w_Underlying wc) c
let w_type_of wc c  = ctxt_type_of (ids_it wc) c
let w_env     wc    = get_env (ids_it wc)
let w_hyps    wc    = named_context (get_env (ids_it wc))
let w_ORELSE wt1 wt2 wc = 
  try wt1 wc with e when catchable_exception e -> wt2 wc
let w_defined_const wc sp = defined_constant (w_env wc) sp
let w_defined_evar wc k      = Evd.is_defined (w_Underlying wc) k
let w_const_value wc         = constant_value (w_env wc)
let w_conv_x wc m n          = is_conv (w_env wc) (w_Underlying wc) m n
let w_whd_betadeltaiota wc c = whd_betadeltaiota (w_env wc) (w_Underlying wc) c
let w_hnf_constr wc c        = hnf_constr (w_env wc) (w_Underlying wc) c


let w_Declare sp ty (wc : walking_constraints) =
  let _ = w_type_of wc ty in (* Utile ?? *)
  let sign = get_hyps (ids_it wc) in
  let newdecl = mk_goal sign ty in 
  ((ids_mod (fun evc -> (rc_add evc (sp,newdecl))) wc): walking_constraints)

let w_Define sp c wc =
  let spdecl = Evd.map (w_Underlying wc) sp in
  let cty = 
    try 
      ctxt_type_of (ids_it (w_Focus sp wc)) (mkCast (c,spdecl.evar_concl))
    with Not_found -> 
      error "Instantiation contains unlegal variables"
  in 
  match spdecl.evar_body with
    | Evar_empty ->
    	let spdecl' = { evar_hyps = spdecl.evar_hyps;
                       	evar_concl = spdecl.evar_concl;
                       	evar_body = Evar_defined c }
    	in 
	(ids_mod (fun evc -> (Proof_trees.remap evc (sp,spdecl'))) wc)
    | _ -> error "define_evar"


(******************************************)
(* Instantiation of existential variables *)
(******************************************)

let instantiate_pf n c pfts = 
  let gls = top_goal_of_pftreestate pfts in
  let (wc,_) = startWalk gls in
  let sigma  = (w_Underlying wc) in 
  let (sp,_) = 
    try 
      List.nth (Evd.non_instantiated sigma) (n-1)
    with Failure _ -> 
      error "not so many uninstantiated existential variables"
  in 
  let wc' = w_Define sp c wc in 
  let newgc = ts_mk (w_Underlying wc') in 
  change_constraints_pftreestate newgc pfts

let instantiate_pf_com n com pfts = 
  let gls = top_goal_of_pftreestate pfts in
  let (wc,_) = startWalk gls in
  let sigma = (w_Underlying wc) in 
  let (sp,evd) = 
    try
      List.nth (Evd.non_instantiated sigma) (n-1) 
    with Failure _ -> 
      error "not so many uninstantiated existential variables"
  in 
  let c = Astterm.interp_constr sigma (Evarutil.evar_env evd) com in     
  let wc' = w_Define sp c wc in
  let newgc = ts_mk (w_Underlying wc') in
  change_constraints_pftreestate newgc pfts
