
(* $Id$ *)

open Pp
open Util
open Names
(* open Generic *)
open Term
open Declarations
open Inductive
open Instantiate
open Environ
open Reduction
open Typeops
open Type_errors
open Indtypes (* pour les erreurs *)

let make_prod_dep dep env = if dep then prod_name env else mkProd

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

(**********************************************************************)
(* Building case analysis schemes *)
(* Nouvelle version, plus concise mais plus coûteuse à cause de
   lift_constructor et lift_inductive_family qui ne se contente pas de 
   lifter les paramètres globaux *)

let mis_make_case_com depopt env sigma mispec kind =
  let lnamespar = mis_params_ctxt mispec in
  let nparams = mis_nparams mispec in
  let dep = match depopt with 
    | None -> mis_sort mispec <> (Prop Null)
    | Some d -> d
  in
  if not (List.exists (base_sort_cmp CONV kind) (mis_kelim mispec)) then
    raise
      (InductiveError
	 (NotAllowedCaseAnalysis (dep,kind,mis_inductive mispec)));

  let nbargsprod = mis_nrealargs mispec + 1 in

  (* Pas génant car env ne sert pas à typer mais juste à renommer les Anonym *)
  (* mais pas très joli ... (mais manque get_sort_of à ce niveau) *)
  let env' = (* push_rels lnamespar *) env in

  let constrs = get_constructors(make_ind_family(mispec,rel_list 0 nparams)) in

  let rec add_branch k = 
    if k = mis_nconstr mispec then
      let nbprod = k+1 in
      let ind = make_ind_family (mispec,rel_list nbprod nparams) in
      let lnamesar,_ = get_arity ind in
      let ci = make_default_case_info mispec in
      it_lambda_name env'
       	(lambda_create env'
           (build_dependent_inductive ind,
            mkMutCase (ci,
		       mkRel (nbprod+nbargsprod),
		       mkRel 1,
		       rel_vect nbargsprod k)))
       	lnamesar
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      mkLambda_string "f"
	(build_branch_type env' dep (mkRel (k+1)) cs)
	(add_branch (k+1))
  in
  let indf = make_ind_family (mispec,rel_list 0 nparams) in
  let typP = make_arity env' dep indf kind in
  it_mkLambda_or_LetIn_name env (mkLambda_string "P" typP (add_branch 0)) lnamespar
    
(* check if the type depends recursively on one of the inductive scheme *)

(**********************************************************************)
(* Building the recursive elimination *)

(*
 * t is the type of the constructor co and recargs is the information on 
 * the recursive calls. (It is assumed to be in form given by the user).
 * build the type of the corresponding branch of the recurrence principle
 * assuming f has this type, branch_rec gives also the term 
 *   [x1]..[xk](f xi (F xi) ...) to be put in the corresponding branch of 
 * the case operation
 * FPvect gives for each inductive definition if we want an elimination 
 * on it with which predicate and which recursive function. 
 *)

let type_rec_branch dep env sigma (vargs,depPvect,decP) co t recargs = 
  let make_prod = make_prod_dep dep in
  let nparams = Array.length vargs in
  let st = hnf_prod_appvect env sigma t vargs in
  let process_pos depK pk = 
    let rec prec i p = 
      let p',largs = whd_betadeltaiota_stack env sigma p in
      match kind_of_term p' with
	| IsProd (n,t,c) -> assert (largs=[]); make_prod env (n,t,prec (i+1) c)
     	| IsMutInd (_,_) -> 
	    let (_,realargs) = list_chop nparams largs in 
	    let base = applist (lift i pk,realargs) in       
            if depK then 
	      mkApp (base, [|appvect (mkRel (i+1),rel_vect 0 i)|])
            else 
	      base
      	| _ -> assert false 
    in
    prec 0 
  in
  let rec process_constr i c recargs co = 
    let c', largs = whd_stack c in
    match kind_of_term c' with 
      | IsProd (n,t,c_0) ->
	  assert (largs = []);
          let (optionpos,rest) = 
	    match recargs with 
	      | [] -> None,[] 
	      | Param _ :: rest -> (None,rest)
	      | Norec :: rest   -> (None,rest)
	      | Imbr _ :: rest  -> 
		  warning "Ignoring recursive call"; (None,rest) 
	      | Mrec j :: rest -> (depPvect.(j),rest)
	  in 
          (match optionpos with 
	     | None -> 
		 make_prod env (n,t,process_constr (i+1) c_0 rest 
				  (mkApp (lift 1 co, [|mkRel 1|])))
             | Some(dep',p) -> 
		 let nP = lift (i+1+decP) p in
		 let t_0 = process_pos dep' nP (lift 1 t) in 
		 make_prod_dep (dep or dep') env
                   (n,t,mkArrow t_0 (process_constr (i+2) (lift 1 c_0) rest
				       (mkApp (lift 2 co, [|mkRel 2|])))))
      | IsLetIn (n,b,t,c_0) ->
	  assert (largs = []);
	  mkLetIn (n,b,t,process_constr (i+1) c_0 recargs (lift 1 co))

      | IsMutInd ((_,tyi),_) -> 
      	  let nP = match depPvect.(tyi) with 
	    | Some(_,p) -> lift (i+decP) p
	    | _ -> assert false in
      	  let (_,realargs) = list_chop nparams largs in
      	  let base = applist (nP,realargs) in
          if dep then mkApp (base, [|co|]) else base
      | _ -> assert false
  in 
  process_constr 0 st recargs (appvect(co,vargs))

let make_rec_branch_arg env sigma (nparams,fvect,decF) f cstr recargs = 
  let process_pos fk  =
    let rec prec i p =
      let p',largs = whd_betadeltaiota_stack env sigma p in
      match kind_of_term p' with
	| IsProd (n,t,c) -> lambda_name env (n,t,prec (i+1) c)
     	| IsMutInd _ -> 
            let (_,realargs) = list_chop nparams largs
            and arg = appvect (mkRel (i+1),rel_vect 0 i) in 
            applist(lift i fk,realargs@[arg])
     	| _ -> assert false
    in
    prec 0 
  in
  (* ici, cstrprods est la liste des produits du constructeur instantié *)
  let rec process_constr i f = function
    | (n,None,t)::cprest, recarg::rest -> 
        let optionpos = 
	  match recarg with 
            | Param i -> None
            | Norec   -> None
            | Imbr _  -> None
            | Mrec i  -> fvect.(i)
	in 
        (match optionpos with 
           | None -> 
	       lambda_name env
		 (n,incast_type t,process_constr (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1)])))
		    (cprest,rest))
           | Some(_,f_0) -> 
	       let nF = lift (i+1+decF) f_0 in
	       let arg = process_pos nF (lift 1 (body_of_type t)) in 
               lambda_name env
		 (n,incast_type t,process_constr (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1); arg])))
		    (cprest,rest)))
    | (n,Some c,t)::cprest, rest ->
	       mkLetIn
		 (n,c,incast_type t,
		  process_constr (i+1) (lift 1 f) (cprest,rest))
    | [],[] -> f
    | _,[] | [],_ -> anomaly "process_constr"

  in
  process_constr 0 f (List.rev cstr.cs_args, recargs)

(* Main function *)
let mis_make_indrec env sigma listdepkind mispec =
  let nparams = mis_nparams mispec in
  let lnamespar = mis_params_ctxt mispec in
  let env' = (* push_rels lnamespar *) env in
  let nrec = List.length listdepkind in
  let depPvec =
    Array.create (mis_ntypes mispec) (None : (bool * constr) option) in 
  let _ = 
    let rec 
      assign k = function 
	| [] -> ()
        | (mispeci,dep,_)::rest -> 
            (Array.set depPvec (mis_index mispeci) (Some(dep,mkRel k));
             assign (k-1) rest)
    in 
    assign nrec listdepkind  
  in 
  let recargsvec = mis_recargs mispec in
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln ltyp ldef = function
	| (mispeci,dep,_)::rest ->
	    let tyi = mis_index mispeci in
	    let nctyi = mis_nconstr mispeci in (* nb constructeurs du type *) 

            (* arity in the context P1..P_nrec f1..f_nbconstruct *)
	    let params = rel_list (nrec+nbconstruct) nparams in
	    let indf = make_ind_family (mispeci,params) in
	    let lnames,_ = get_arity indf in

	    let nar = mis_nrealargs mispeci in
	    let decf = nar+nrec+nbconstruct+nrec in 
	    let dect = nar+nrec+nbconstruct in
	    let vecfi = rel_vect (dect+1-i-nctyi) nctyi in

	    let constrs =
	      get_constructors 
		(make_ind_family (mispeci,rel_list (decf+1) nparams)) in
	    let branches = 
	      array_map3
		(make_rec_branch_arg env sigma (nparams,depPvec,nar+1))
                vecfi constrs recargsvec.(tyi) in
	    let j = (match depPvec.(tyi) with 
		       | Some (_,c) when isRel c -> destRel c 
		       | _ -> assert false) in
	    let indf = make_ind_family
			 (mispeci,rel_list (nrec+nbconstruct) nparams) in
	    let deftyi = 
	      it_lambda_name env
		(lambda_create env
		   (build_dependent_inductive
		      (lift_inductive_family nrec indf),
		    mkMutCase (make_default_case_info mispeci,
			       mkRel (dect+j+1), mkRel 1, branches)))
		(lift_context nrec lnames)
	    in
	    let typtyi = 
	      it_prod_name env
		(prod_create env
		   (build_dependent_inductive indf,
		    (if dep then 
		       appvect (mkRel (nbconstruct+nar+j+1), rel_vect 0 (nar+1)) 
		     else 
		       appvect (mkRel (nbconstruct+nar+j+1), rel_vect 1 nar))))
          	lnames
	    in 
	    mrec (i+nctyi) (nar::ln) (typtyi::ltyp) (deftyi::ldef) rest
        | [] -> 
	    let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in 
            let names = list_tabulate (fun _ -> Name(id_of_string "F")) nrec in
	    mkFix ((fixn,p),(fixtyi,names,fixdef))
      in 
      mrec 0 [] [] [] 
    in 
    let rec make_branch i = function 
      | (mispeci,dep,_)::rest ->
          let tyi = mis_index mispeci in
	  let (lc,lct) = mis_type_mconstructs mispeci in 
	  let rec onerec j = 
	    if j = Array.length lc then 
	      make_branch (i+j) rest 
	    else 
	      let co = lc.(j) in
	      let t = lct.(j) in
	      let recarg = recargsvec.(tyi).(j) in
	      let vargs = rel_vect (nrec+i+j) nparams in
	      let p_0 = 
		type_rec_branch dep env sigma (vargs,depPvec,i+j) co t recarg
	      in 
	      mkLambda_string "f" p_0 (onerec (j+1))
	  in onerec 0
      | [] -> 
	  makefix i listdepkind
    in 
    let rec put_arity i = function 
      | (mispeci,dep,kinds)::rest -> 
	  let indf = make_ind_family (mispeci,rel_list i nparams) in
	  let typP = make_arity env dep indf kinds in
	  mkLambda_string "P" typP (put_arity (i+1) rest)
      | [] -> 
	  make_branch 0 listdepkind 
    in 
    let (mispeci,dep,kind) = List.nth listdepkind p in
    if mis_is_recursive_subset
      (List.map (fun (mispec,_,_) -> mis_index mispec) listdepkind) mispeci
    then 
      it_mkLambda_or_LetIn_name env (put_arity 0 listdepkind) lnamespar
    else 
      mis_make_case_com (Some dep) env sigma mispeci kind 
  in 
  list_tabulate make_one_rec nrec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let make_case_com depopt env sigma ity kind =
  let mispec = lookup_mind_specif ity env in 
  mis_make_case_com depopt env sigma mispec kind

let make_case_dep env   = make_case_com (Some true) env
let make_case_nodep env = make_case_com (Some false) env 
let make_case_gen env   = make_case_com None env


(**********************************************************************)
(* [instanciate_indrec_scheme s rec] replace the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort = 
  let rec drec a = match kind_of_term a with
    | IsCast (c,t) -> drec c 
    | IsProd (n,t,c) -> mkProd (n, t, drec c)
    | IsSort _ -> mkSort sort
    | _ -> assert false
  in 
  drec 

let instanciate_indrec_scheme sort =
  let rec drec npar elim =
    let (n,t,c) = destLambda (strip_outer_cast elim) in
    if npar = 0 then 
      mkLambda (n, change_sort_arity sort t, c)
    else 
      mkLambda (n, t, drec (npar-1) c) 
  in
  drec

(**********************************************************************)
(* Interface to build complex Scheme *)

let check_arities listdepkind = 
  List.iter 
    (function (mispeci,dep,kinds) -> 
       let id = mis_typename mispeci  in
       let kelim = mis_kelim mispeci in
       if not (List.exists (base_sort_cmp CONV kinds) kelim) then
	 raise (InductiveError (BadInduction (dep, id, kinds))))
    listdepkind

let build_mutual_indrec env sigma = function 
  | (mind,dep,s)::lrecspec ->
      let ((sp,tyi),_) = mind in
      let mispec = lookup_mind_specif mind env in
      let listdepkind = 
    	(mispec, dep,s)::
    	(List.map
	   (function (mind',dep',s') ->
	      let ((sp',_),_) = mind' in
	      if sp=sp' then 
		(lookup_mind_specif mind' env,dep',s') 
	      else 
		raise (InductiveError NotMutualInScheme))
	   lrecspec)
      in
      let _ = check_arities listdepkind in 
      mis_make_indrec env sigma listdepkind mispec
  | _ -> anomaly "build_indrec expects a non empty list of inductive types"

let build_indrec env sigma mispec =
  let kind = mis_sort mispec in
  let dep = kind <> Prop Null in
  List.hd (mis_make_indrec env sigma [(mispec,dep,kind)] mispec)

(**********************************************************************)
(* To handle old Case/Match syntax in Pretyping                       *)

(***********************************)
(* To interpret the Match operator *)

let type_mutind_rec env sigma (IndType (indf,realargs) as ind) pt p c = 
  let (mispec,params) = dest_ind_family indf in
  let tyi = mis_index mispec in
  if mis_is_recursive_subset [tyi] mispec then
    let dep = find_case_dep_nparams env sigma (c,p) indf pt in 
    let init_depPvec i = if i = tyi then Some(dep,p) else None in
    let depPvec = Array.init (mis_ntypes mispec) init_depPvec in
    let vargs = Array.of_list params in
    let (constrvec,typeconstrvec) = mis_type_mconstructs mispec in
    let recargs = mis_recarg mispec in
    let lft = array_map3 (type_rec_branch dep env sigma (vargs,depPvec,0)) 
                constrvec typeconstrvec recargs in
    (lft,
     if dep then applist(p,realargs@[c]) 
     else applist(p,realargs) )
  else 
    type_case_branches env sigma ind pt p c

let type_rec_branches recursive env sigma ind pt p c =
  if recursive then 
    type_mutind_rec env sigma ind pt p c
  else 
    type_case_branches env sigma ind pt p c

