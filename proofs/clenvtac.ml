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
open Reductionops
open Tacmach
open Evar_refiner
open Rawterm
open Pattern
open Tacexpr
open Clenv

    
let clenv_wtactic wt clenv =
  { templval = clenv.templval;
    templtyp = clenv.templtyp;
    namenv = clenv.namenv;
    env = clenv.env;
    hook = wt clenv.hook }

(* This function put casts around metavariables whose type could not be
 * infered by the refiner, that is head of applications, predicates and
 * subject of Cases.
 * Does check that the casted type is closed. Anyway, the refiner would
 * fail in this case... *)

let clenv_cast_meta clenv = 
  let rec crec u =
    match kind_of_term u with
      | App _ | Case _ -> crec_hd u
      | Cast (c,_) when isMeta c -> u
      | _  -> map_constr crec u
	    
  and crec_hd u =
    match kind_of_term (strip_outer_cast u) with
      | Meta mv ->
	  (try 
	     match Metamap.find mv clenv.env with
               | Cltyp b ->
		   let b' = clenv_instance clenv b in 
		   if occur_meta b' then u else mkCast (mkMeta mv, b')
	       | Clval(_) -> u
	   with Not_found -> 
	     u)
      | App(f,args) -> mkApp (crec_hd f, Array.map crec args)
      | Case(ci,p,c,br) ->
	  mkCase (ci, crec_hd p, crec_hd c, Array.map crec br)
      | _ -> u
  in 
  crec


let clenv_refine clenv gls =
  tclTHEN
    (tclEVARS clenv.hook.sigma) 
    (refine (clenv_instance_template clenv)) gls

let clenv_refine_cast clenv gls =
  tclTHEN
    (tclEVARS clenv.hook.sigma) 
    (refine (clenv_cast_meta clenv (clenv_instance_template clenv)))
    gls

let res_pf clenv gls =
  clenv_refine (clenv_unique_resolver false clenv gls) gls
    
let res_pf_cast clenv gls =
  clenv_refine_cast (clenv_unique_resolver false clenv gls) gls

let elim_res_pf clenv allow_K gls =
  clenv_refine_cast (clenv_unique_resolver allow_K clenv gls) gls

let elim_res_pf_THEN_i clenv tac gls =  
  let clenv' = (clenv_unique_resolver true clenv gls) in
  tclTHENLASTn (clenv_refine clenv') (tac clenv') gls

(* [clenv_pose_dependent_evars clenv]
 * For each dependent evar in the clause-env which does not have a value,
 * pose a value for it by constructing a fresh evar.  We do this in
 * left-to-right order, so that every evar's type is always closed w.r.t.
 * metas. *)

let clenv_pose_dependent_evars clenv =
  let dep_mvs = clenv_dependent false clenv in
  List.fold_left
    (fun clenv mv ->
       let evar = Evarutil.new_evar_in_sign (get_env clenv.hook) in
       let (evar_n,_) = destEvar evar in
       let tY = clenv_instance_type clenv mv in
       let clenv' = clenv_wtactic (w_Declare evar_n tY) clenv in
       clenv_assign mv evar clenv')
    clenv
    dep_mvs

let e_res_pf clenv gls =
  clenv_refine
    (clenv_pose_dependent_evars (clenv_unique_resolver false clenv gls)) gls



(* [unifyTerms] et [unify] ne semble pas gérer les Meta, en
   particulier ne semblent pas vérifier que des instances différentes
   d'une même Meta sont compatibles. D'ailleurs le "fst" jette les metas
   provenant de w_Unify. (Utilisé seulement dans prolog.ml) *)

(* let unifyTerms m n = walking (fun wc -> fst (w_Unify CONV m n [] wc)) *)
let unifyTerms m n gls = 
  let env = pf_env gls in
  let maps = (create_evar_defs (project gls), Evd.Metamap.empty) in
  let maps' = Unification.w_unify false env CONV m n maps in
  tclIDTAC {it = gls.it; sigma = evars_of (fst maps')}

let unify m gls =
  let n = pf_concl gls in unifyTerms m n gls
