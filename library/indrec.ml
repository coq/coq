
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Declarations
open Inductive
open Instantiate
open Environ
open Reduction
open Typeops
open Type_errors
open Indtypes (* pour les erreurs *)

let simple_prod (n,t,c) = mkProd n t c
let make_prod_dep dep env = if dep then prod_name env else simple_prod

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
      let lnamesar,_ = get_arity env' sigma ind in
      let ci = make_default_case_info mispec in
      it_lambda_name env'
       	(lambda_create env'
           (build_dependent_inductive ind,
            mkMutCaseA ci
	      (Rel (nbprod+nbargsprod))
              (Rel 1)
              (rel_vect nbargsprod k)))
       	lnamesar
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      mkLambda_string "f"
	(build_branch_type env' dep (Rel (k+1)) cs)
	(add_branch (k+1))
  in
  let indf = make_ind_family (mispec,rel_list 0 nparams) in
  let typP = make_arity env' sigma dep indf kind in
  it_lambda_name env (mkLambda_string "P" typP (add_branch 0)) lnamespar
    
(* check if the type depends recursively on one of the inductive scheme *)

(**********************************************************************)
(* Building the recursive elimination *)

(*
 * t is the type of the constructor co and recargs is the information on 
 * the recursive calls.                                                  
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
      match whd_betadeltaiota_stack env sigma p [] with 
	| (DOP2(Prod,t,DLAM(n,c))),[] -> make_prod env (n,t,prec (i+1) c)
     	| (DOPN(MutInd _,_),largs) -> 
	    let (_,realargs) = list_chop nparams largs in 
	    let base = applist (lift i pk,realargs) in       
            if depK then 
	      mkAppList base [appvect (Rel (i+1),rel_vect 0 i)]
            else 
	      base
      	| _ -> assert false 
    in
    prec 0 
  in
  let rec process_constr i c recargs co = 
    match whd_betadeltaiota_stack env sigma c [] with 
      | (DOP2(Prod,t,DLAM(n,c_0)),[]) -> 
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
				  (mkAppList (lift 1 co) [Rel 1]))
             | Some(dep',p) -> 
		 let nP = lift (i+1+decP) p in
		 let t_0 = process_pos dep' nP (lift 1 t) in 
		 make_prod_dep (dep or dep') env
                   (n,t,mkArrow t_0 (process_constr (i+2) (lift 1 c_0) rest
				       (mkAppList (lift 2 co) [Rel 2]))))
      | (DOPN(MutInd(_,tyi),_),largs) -> 
      	  let nP = match depPvect.(tyi) with 
	    | Some(_,p) -> lift (i+decP) p
	    | _ -> assert false in
      	  let (_,realargs) = list_chop nparams largs in
      	  let base = applist (nP,realargs) in
          if dep then mkAppList base [co] else base
      | _ -> assert false
  in 
  process_constr 0 st recargs (appvect(co,vargs))

let make_rec_branch_arg env sigma (nparams,fvect,decF) f cstr recargs = 
  let process_pos fk  =
    let rec prec i p = 
      (match whd_betadeltaiota_stack env sigma p [] with 
	 | (DOP2(Prod,t,DLAM(n,c))),[] -> lambda_name env (n,t,prec (i+1) c) 
     	 | (DOPN(MutInd _,_),largs) -> 
             let (_,realargs) = list_chop nparams largs
             and arg = appvect (Rel (i+1),rel_vect 0 i) in 
             applist(lift i fk,realargs@[arg])
     	 | _ -> assert false) 
    in
    prec 0 
  in
  (* ici, cstrprods est la liste des produits du constructeur instantié *)
  let rec process_constr i cstrprods f recargs = 
    match cstrprods with 
      | (n,t)::cprest -> 
          let (optionpos,rest) = 
	    match recargs with 
	      | [] -> (* Impossible?! *) None,[] 
              | (Param(i)::rest) -> None,rest 
              | (Norec::rest) -> None,rest 
              | (Imbr _::rest) -> None,rest 
              | (Mrec i::rest) -> fvect.(i),rest 
	  in 
          (match optionpos with 
             | None -> 
		 lambda_name env
		   (n,t,process_constr (i+1) cprest 
		      (applist(whd_beta_stack env sigma (lift 1 f) 
				 [(Rel 1)])) rest)
             | Some(_,f_0) -> 
		 let nF = lift (i+1+decF) f_0 in
		 let arg = process_pos nF (lift 1 t) in 
                 lambda_name env
		   (n,t,process_constr (i+1) cprest 
		      (applist(whd_beta_stack env sigma (lift 1 f) 
				 [(Rel 1); arg])) 
		      rest))
      | [] -> f
  in 
  process_constr 0 (List.rev cstr.cs_args) f recargs 

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
            (Array.set depPvec (mis_index mispeci) (Some(dep,Rel k));
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
	    let lnames,_ = get_arity env sigma indf in

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
		       | Some (_,Rel j) -> j 
		       | _ -> assert false) in
	    let indf = make_ind_family
			 (mispec,rel_list (nrec+nbconstruct) nparams) in
	    let deftyi = 
	      it_lambda_name env
		(lambda_create env
		   (build_dependent_inductive
		      (lift_inductive_family nrec indf),
		    mkMutCaseA (make_default_case_info mispec)
                      (Rel (dect+j+1)) (Rel 1) branches))
		(lift_context nrec lnames)
	    in
	    let typtyi = 
	      it_prod_name env
		(prod_create env
		   (build_dependent_inductive indf,
		    (if dep then 
		       appvect (Rel (nbconstruct+nar+j+1), rel_vect 0 (nar+1)) 
		     else 
		       appvect (Rel (nbconstruct+nar+j+1), rel_vect 1 nar))))
          	lnames
	    in 
	    mrec (i+nctyi) (nar::ln) (typtyi::ltyp) (deftyi::ldef) rest
        | [] -> 
	    let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in 
            let makefixdef = 
              put_DLAMSV 
		(list_tabulate (fun _ -> Name(id_of_string "F")) nrec) fixdef 
	    in 
            let fixspec = Array.append fixtyi [|makefixdef|] in 
	    DOPN(Fix(fixn,p),fixspec)
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
	  let typP = make_arity env sigma dep indf kinds in
	  mkLambda_string "P" typP (put_arity (i+1) rest)
      | [] -> 
	  make_branch 0 listdepkind 
    in 
    let (mispeci,dep,kind) = List.nth listdepkind p in
    if mis_is_recursive_subset
      (List.map (fun (mispec,_,_) -> mis_index mispec) listdepkind) mispeci
    then 
      it_lambda_name env (put_arity 0 listdepkind) lnamespar
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
  let rec drec = function 
    | (DOP2(Cast,c,t)) -> drec c 
    | (DOP2(Prod,t,DLAM(n,c))) -> DOP2(Prod,t,DLAM(n,drec c))
    | (DOP0(Sort(_))) -> DOP0(Sort(sort))
    | _ -> assert false
  in 
  drec 

let instanciate_indrec_scheme sort =
  let rec drec npar elim =
    let (n,t,c) = destLambda (strip_outer_cast elim) in
    if npar = 0 then 
      mkLambda n (change_sort_arity sort t) c
    else 
      mkLambda n t (drec (npar-1) c) 
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
  strip_all_casts
    (List.hd (mis_make_indrec env sigma [(mispec,dep,kind)] mispec))

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

(***************************************************)
(* Building ML like case expressions without types *)

let concl_n env sigma = 
  let rec decrec m c = if m = 0 then c else 
    match whd_betadeltaiota env sigma c with
      | DOP2(Prod,_,DLAM(n,c_0)) -> decrec (m-1) c_0
      | _                        -> failwith "Typing.concl_n"
  in 
  decrec

let count_rec_arg j = 
  let rec crec i = function 
    | [] -> i 
    | (Mrec k::l) -> crec (if k=j then (i+1) else i) l
    | (_::l) -> crec i l
  in 
  crec 0

(* if arity of mispec is (p_bar:P_bar)(a_bar:A_bar)s where p_bar are the
 * K parameters. Then then build_notdep builds the predicate
 * [a_bar:A'_bar](lift k pred) 
 * where A'_bar = A_bar[p_bar <- globargs] *)

let build_notdep_pred env sigma indf pred =
  let arsign,_ = get_arity env sigma indf in
  let nar = List.length arsign in
  it_lambda_name env (lift nar pred) arsign


let pred_case_ml_fail env sigma isrec (IndType (indf,realargs)) (i,ft) =
  let pred =
    let mispec,_ = dest_ind_family indf in
    let recargs = mis_recarg mispec in
    assert (Array.length recargs <> 0);
    let recargi = recargs.(i-1) in
    let j = mis_index mispec in
    let nbrec = if isrec then count_rec_arg j recargi else 0 in
    let nb_arg = List.length (recargs.(i-1)) + nbrec in
    let pred = concl_n env sigma nb_arg ft in
    if noccur_bet 1 nb_arg pred then 
      lift (-nb_arg) pred
    else 
      failwith "Dependent"
  in
  if realargs = [] then 
    pred
  else (* we try with [_:T1]..[_:Tn](lift n pred) *)
    build_notdep_pred env sigma indf pred  

let pred_case_ml env sigma isrec indt lf (i,ft) = 
    pred_case_ml_fail env sigma isrec indt (i,ft)

(* similar to pred_case_ml but does not expect the list lf of braches *)
let pred_case_ml_onebranch env sigma isrec indt (i,f,ft) = 
    pred_case_ml_fail env sigma isrec indt (i,ft)

(* Used in Program only *)      
let make_case_ml isrec pred c ci lf = 
  if isrec then 
    DOPN(XTRA("REC"),Array.append [|pred;c|] lf)
  else 
    mkMutCaseA ci pred c lf
