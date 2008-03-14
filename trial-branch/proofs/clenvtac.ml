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
open Nameops
open Term
open Termops
open Sign
open Environ
open Evd
open Evarutil
open Proof_type
open Refiner
open Proof_trees
open Logic
open Reduction
open Reductionops
open Tacmach
open Evar_refiner
open Rawterm
open Pattern
open Tacexpr
open Clenv

    
(* This function put casts around metavariables whose type could not be
 * infered by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv = 
  let rec crec u =
    match kind_of_term u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_,_) when isMeta c -> u
      | _  -> map_constr crec u
	    
  and crec_hd u =
    match kind_of_term (strip_outer_cast u) with
      | Meta mv ->
	  (try 
            let b = Typing.meta_type clenv.evd mv in
	    if occur_meta b then u
            else mkCast (mkMeta mv, DEFAULTcast, b)
	  with Not_found -> u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
      | _ -> u
  in 
  crec

let clenv_refine with_evars clenv gls =
  let clenv = if with_evars then clenv_pose_dependent_evars clenv else clenv in
  tclTHEN
    (tclEVARS (evars_of clenv.evd)) 
    (refine (clenv_cast_meta clenv (clenv_value clenv)))
    gls


let res_pf clenv ?(with_evars=false) ?(allow_K=false) gls =
  clenv_refine with_evars (clenv_unique_resolver allow_K clenv gls) gls

let elim_res_pf_THEN_i clenv tac gls =  
  let clenv' = (clenv_unique_resolver true clenv gls) in
  tclTHENLASTn (clenv_refine false clenv') (tac clenv') gls

let e_res_pf clenv = res_pf clenv ~with_evars:true ~allow_K:false


(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unifyTerms m n gls = 
  let env = pf_env gls in
  let evd = create_goal_evar_defs (project gls) in
  let evd' = Unification.w_unify false env CONV m n evd in
  tclIDTAC {it = gls.it; sigma = evars_of evd'}

let unify m gls =
  let n = pf_concl gls in unifyTerms m n gls
