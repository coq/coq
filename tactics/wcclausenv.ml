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
open Term
open Sign
open Reduction
open Environ
open Logic
open Tacmach
open Evd
open Proof_trees
open Clenv
open Evar_refiner

(* If you have a precise idea of the intended use of the following code, please
   write to Eduardo.Gimenez@inria.fr and ask for the prize :-)
   -- Eduardo (11/8/97) *)

type wc = walking_constraints

let pf_get_new_id id gls = 
  next_ident_away id (pf_ids_of_hyps gls)

let pf_get_new_ids ids gls =
  let avoid = pf_ids_of_hyps gls in
  List.fold_right
    (fun id acc -> (next_ident_away id (acc@avoid))::acc)
    ids []

type arg_binder =
  | Dep of identifier
  | Nodep of int
  | Abs of int

type arg_bindings = (arg_binder * constr) list

let clenv_constrain_with_bindings bl clause =
  if bl = [] then 
    clause 
  else 
    let all_mvs = collect_metas (clenv_template clause).rebus
    and ind_mvs = clenv_independent clause
		    (clenv_template clause,
                     clenv_template_type clause) in
    let nb_indep = List.length ind_mvs in
    let rec matchrec clause = function
      | []       -> clause
      | (b,c)::t ->
          let k = 
            match b with
              | Dep s ->
		  if List.mem_assoc b t then 
		    errorlabstrm "clenv_match_args" 
                      [< 'sTR "The variable "; pr_id s; 
			 'sTR " occurs more than once in binding" >];
		  clenv_lookup_name clause s
              | Nodep n ->
		  let index = if n > 0 then n-1 else nb_indep+n in
                  if List.mem_assoc (Nodep (index+1)) t or 
                    List.mem_assoc (Nodep (index-nb_indep)) t
                  then errorlabstrm "clenv_match_args"
                    [< 'sTR "The position "; 'iNT n ;
		       'sTR " occurs more than once in binding" >];
		  (try 
		     List.nth ind_mvs index
		   with Failure _ ->
                     errorlabstrm "clenv_constrain_with_bindings"
                       [< 'sTR"Clause did not have " ; 'iNT n ; 'sTR"-th" ;
                          'sTR" unnamed argument" >])
              | Abs n -> 
                  (try
                     if n > 0 then 
		       List.nth all_mvs (n-1)
                     else if n < 0 then 
		       List.nth (List.rev all_mvs) (-n-1)
                     else error "clenv_constrain_with_bindings" 
                   with Failure _ ->
                     errorlabstrm "clenv_constrain_with_bindings"
                       [< 'sTR"Clause did not have " ; 'iNT n ; 'sTR"-th" ;
                          'sTR" absolute argument" >])
	  in
	  let env = Global.env () in
	  let sigma = Evd.empty in
	  let k_typ = nf_betaiota (clenv_instance_type clause k) in
	  let c_typ = nf_betaiota (w_type_of clause.hook c) in 
	  matchrec (clenv_assign k c (clenv_unify k_typ c_typ clause)) t
    in 
    matchrec clause bl

let add_prod_rel sigma (t,env) =
  match kind_of_term t with
    | IsProd (na,t1,b) ->
        (b,push_rel_assum (na, t1) env)
    | IsLetIn (na,c1,t1,b) ->
        (b,push_rel_def (na,c1, t1) env)
    | _ -> failwith "add_prod_rel"

let rec add_prods_rel sigma (t,env) =
  try 
    add_prods_rel sigma (add_prod_rel sigma (whd_betadeltaiota env sigma t,env))
  with Failure "add_prod_rel" -> 
    (t,env)

(* What follows is part of the contents of the former file tactics3.ml *)
    
let res_pf_THEN kONT clenv tac gls =
  let clenv' = (clenv_unique_resolver false clenv gls) in 
  (tclTHEN (clenv_refine kONT clenv') (tac clenv')) gls

let res_pf_THEN_i kONT clenv tac gls =
  let clenv' = (clenv_unique_resolver false clenv gls) in 
  tclTHEN_i (clenv_refine kONT clenv') (tac clenv') gls

let elim_res_pf_THEN_i kONT clenv tac gls =  
  let clenv' = (clenv_unique_resolver true clenv gls) in
  tclTHEN_i (clenv_refine kONT clenv') (tac clenv') gls

let rec build_args acc ce p_0 p_1 =
  match kind_of_term p_0, p_1 with 
    | (IsProd (na,a,b), (a_0::bargs)) ->
        let (newa,ce') = (build_term ce (na,Some a) a_0) in 
	build_args (newa::acc) ce' (subst1 a_0 b) bargs
    | (IsLetIn (na,a,t,b), args) -> build_args acc ce (subst1 a b) args
    | (_, [])     -> (List.rev acc,ce)
    | (_, (_::_)) -> failwith "mk_clenv_using"

and build_term ce p_0 c =
  let env = w_env ce.hook in
  match p_0, kind_of_term c with 
    | ((na,Some t), IsMeta mv) -> 
(*    	let mv = new_meta() in *)
	(mkMeta mv, clenv_pose (na,mv,t) ce)
    | ((na,_), IsCast (c,t)) -> build_term ce (na,Some t) c
    | ((na,Some t), _) ->
    	if (not((occur_meta c))) then 
	  (c,ce)
    	else 
	  let (hd,args) = 
	    whd_betadeltaiota_stack env (w_Underlying ce.hook) c in
          let hdty = w_type_of ce.hook hd in
          let (args,ce') =
	    build_args [] ce (w_whd_betadeltaiota ce.hook hdty) args in
          let newc = applist(hd,args) in
          let t' = clenv_type_of ce' newc in  
	  if w_conv_x ce'.hook t t' then 
	    (newc,ce') 
	  else 
	    failwith "mk_clenv_using"
    | ((na,None), _) ->
    	if (not((occur_meta c))) then 
	  (c,ce)
    	else 
	  let (hd,args) = 
	    whd_betadeltaiota_stack env (w_Underlying ce.hook) c in
          let hdty = w_type_of ce.hook hd in
          let (args,ce') = 
	    build_args [] ce (w_whd_betadeltaiota ce.hook hdty) args in
          let newc = applist(hd,args) in
	  (newc,ce')

let mk_clenv_using wc c =
  let ce = mk_clenv wc mkImplicit in
  let (newc,ce') = 
    try 
      build_term ce (Anonymous,None) c
    with Failure _ -> 
      raise (RefinerError (NotWellTyped c))
  in
  clenv_change_head (newc,clenv_type_of ce' newc) ce'

let applyUsing c gl =
  let (wc,kONT) = startWalk gl in
  let clause = mk_clenv_using wc c in 
  res_pf kONT clause gl

let clenv_apply_n_times n ce =
  let templtyp = clenv_instance_template_type ce
  and templval = (clenv_template ce).rebus in   
  let rec apprec ce argacc (n,ty) =
    let env = Global.env () in
    let templtyp = whd_betadeltaiota env (w_Underlying ce.hook) ty in
    match (n, kind_of_term templtyp) with 
      | (0, _) ->
	  clenv_change_head (applist(templval,List.rev argacc), templtyp) ce
      | (n, IsProd (na,dom,rng)) ->
          let mv = new_meta() in
          let newce = clenv_pose (na,mv,dom) ce in
	  apprec newce (mkMeta mv::argacc) (n-1, subst1 (mkMeta mv) rng)
      | (n, IsLetIn (na,b,t,c)) ->
	  apprec ce argacc (n, subst1 b c)
      | (n, _) -> failwith "clenv_apply_n_times"
  in 
  apprec ce [] (n, templtyp)
