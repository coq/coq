
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Inductive
open Instantiate
open Environ
open Reduction
open Typeops
open Type_errors

let make_lambda_string s t c = DOP2(Lambda,t,DLAM(Name(id_of_string s),c))

let make_prod_string s t c = DOP2(Prod,t,DLAM(Name(id_of_string s),c))

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

let prod_create env (a,b) = 
  mkProd (named_hd env a Anonymous) a b
let lambda_create env (a,b) = 
  mkLambda (named_hd env a Anonymous) a b

let simple_prod (n,t,c) = DOP2(Prod,t,DLAM(n,c))
let make_prod_dep dep env = if dep then prod_name env else simple_prod

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

(**********************************************************************)
(* Building case analysis schemes *)

let mis_make_case_com depopt env sigma mispec kind =
 
  let nparams = mis_nparams mispec in
  let mind = mkMutInd ((mispec.mis_sp,mispec.mis_tyi),mispec.mis_args) in
  let t = mis_arity mispec in
  let (lc,lct) = mis_type_mconstructs mispec in
  let lnames,sort = splay_prod env sigma t in
  let nconstr = Array.length lc in
  let dep = match depopt with 
    | None -> (sort<>DOP0(Sort(Prop Null)))
    | Some d -> d
  in
  if not (List.exists (base_sort_cmp CONV kind) (mis_kelim mispec)) then begin
    errorlabstrm "Case analysis"
      [< 'sTR (if dep then "Dependent" else "Non Dependent");
	 'sTR " case analysis on sort: "; print_sort kind; 'fNL;
         'sTR "is not allowed for inductive definition: ";
	 print_sp mispec.mis_sp >]
  end;
  let lnamesar,lnamespar = list_chop (List.length lnames - nparams) lnames in
  let lgar = List.length lnamesar in
  let ar = hnf_prod_appvect env sigma "make_case_dep" t (rel_vect 0 nparams) in
  let typP = 
    if dep then 
      make_arity_dep env sigma (DOP0(Sort kind)) ar 
       	(appvect (mind,rel_vect 0 nparams))
    else 
      make_arity_nodep env sigma (DOP0(Sort kind)) ar 
  in 
  let rec add_branch k = 
    if k = nconstr then 
      it_lambda_name env
       	(lambda_create env
           (appvect (mind,
                     (Array.append (rel_vect (nconstr+lgar+1) nparams)
                       	(rel_vect 0 lgar))),
            mkMutCaseA (make_default_case_info mispec)
	      (Rel (nconstr+lgar+2))
              (Rel 1)
              (rel_vect (lgar+1) nconstr)))
       	(lift_context (nconstr+1) lnamesar)
    else
      make_lambda_string "f" 
       	(if dep then 
	   type_one_branch_dep env sigma
             (nparams,(rel_list (k+1) nparams),Rel (k+1)) lc.(k) lct.(k)
         else 
	  type_one_branch_nodep env sigma
            (nparams,(rel_list (k+1) nparams),Rel (k+1)) lct.(k))
       	(add_branch (k+1))
  in 
  it_lambda_name env (make_lambda_string "P" typP (add_branch 0)) lnamespar
    
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
  let st = hnf_prod_appvect env sigma "type_rec_branch" t vargs in
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
	      | (Param(_)::rest) -> (None,rest)
	      | (Norec::rest) -> (None,rest)
	      | (Imbr _::rest) -> 
		  warning "Ignoring recursive call"; (None,rest) 
	      |(Mrec j::rest) -> (depPvect.(j),rest)
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

let make_rec_branch_arg env sigma (vargs,fvect,decF) f t recargs = 
  let nparams = Array.length vargs in
  let st = hnf_prod_appvect env sigma "type_rec_branch" t vargs in
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
  let rec process_constr i c f recargs = 
    match whd_betadeltaiota_stack env sigma c [] with 
      | (DOP2(Prod,t,DLAM(n,c_0)),[]) -> 
          let (optionpos,rest) = 
	    match recargs with 
	      | [] -> None,[] 
              | (Param(i)::rest) -> None,rest 
              | (Norec::rest) -> None,rest 
              | (Imbr _::rest) -> None,rest 
              | (Mrec i::rest) -> fvect.(i),rest 
	  in 
          (match optionpos with 
             | None -> 
		 lambda_name env
		   (n,t,process_constr (i+1) c_0 
		      (applist(whd_beta_stack env sigma (lift 1 f) 
				 [(Rel 1)])) rest)
             | Some(_,f_0) -> 
		 let nF = lift (i+1+decF) f_0 in
		 let arg = process_pos nF (lift 1 t) in 
                 lambda_name env
		   (n,t,process_constr (i+1) c_0 
		      (applist(whd_beta_stack env sigma (lift 1 f) 
				 [(Rel 1); arg])) 
		      rest))
      | (DOPN(MutInd(_,tyi),_),largs) -> f
      | _ -> assert false
  in 
  process_constr 0 st f recargs 

(* Main function *)
let mis_make_indrec env sigma listdepkind mispec =
  let nparams = mis_nparams mispec in
  let recargsvec = mis_recargs mispec in
  let ntypes = mis_ntypes mispec in
  let mind_arity = mis_arity mispec in 
  let (lnames, kind) = splay_arity env sigma mind_arity in
  let lnamespar = list_lastn nparams lnames in
  let listdepkind = 
    if listdepkind = [] then 
      let dep = kind <> Prop Null in [(mispec,dep,kind)] 
    else 
      listdepkind 
  in
  let nrec = List.length listdepkind in
  let depPvec = Array.create ntypes (None : (bool * constr) option) in 
  let _ = 
    let rec 
      assign k = function 
	| [] -> ()
        | (mispeci,dep,_)::rest -> 
            (Array.set depPvec mispeci.mis_tyi (Some(dep,Rel k));
             assign (k-1) rest)
    in 
    assign nrec listdepkind  
  in 
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln ltyp ldef = function
	| (mispeci,dep,_)::rest ->
	    let tyi = mispeci.mis_tyi in
	    let mind = DOPN(MutInd (mispeci.mis_sp,tyi),mispeci.mis_args) in
	    let (_,lct) = mis_type_mconstructs mispeci in
	    let nctyi = Array.length lct in (* nb constructeurs du type *) 
	    let realar =  hnf_prod_appvect env sigma "make_branch" 
			    (mis_arity mispeci) 
			    (rel_vect (nrec+nbconstruct) nparams) in
               (* arity in the contexte P1..Prec f1..f_nbconstruct *)
	    let lnames,_ = splay_prod env sigma realar in 
	    let nar = List.length lnames in 
	    let decf = nar+nrec+nbconstruct+nrec in 
	    let dect = nar+nrec+nbconstruct in
	    let vecfi = rel_vect (dect+1-i-nctyi) nctyi in
	    let branches = 
	      array_map3
		(make_rec_branch_arg env sigma 
		   (rel_vect (decf+1) nparams,depPvec,nar+1))
                vecfi lct recargsvec.(tyi) in
	    let j = (match depPvec.(tyi) with 
		       | Some (_,Rel j) -> j 
		       | _ -> assert false) in
	    let deftyi = 
	      it_lambda_name env
		(lambda_create env
		   (appvect (mind,(Array.append (rel_vect decf nparams)
				     (rel_vect 0 nar))),
		    mkMutCaseA (make_default_case_info mispec)
                      (Rel (decf-nrec+j+1)) (Rel 1) branches))
		(lift_context nrec lnames)
	    in
	    let typtyi = 
	      it_prod_name env
		(prod_create env
		   (appvect (mind,(Array.append (rel_vect dect nparams)
				     (rel_vect 0 nar))),
		    (if dep then 
		       appvect (Rel (dect-nrec+j+1), rel_vect 0 (nar+1)) 
		     else 
		       appvect (Rel (dect-nrec+j+1),rel_vect 1 nar))))
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
	  let tyi = mispeci.mis_tyi in
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
	      DOP2(Lambda,p_0,DLAM(Name (id_of_string "f"),onerec (j+1)))
	  in onerec 0
      | [] -> 
	  makefix i listdepkind
    in 
    let rec put_arity i = function 
      | (mispeci,dep,kinds)::rest -> 
	  let mind = DOPN(MutInd (mispeci.mis_sp,mispeci.mis_tyi),
			  mispeci.mis_args) in 
	  let arity = mis_arity mispeci in 
	  let ar =
	    hnf_prod_appvect env sigma "put_arity" arity (rel_vect i nparams)
	  in 
	  let typP = 
	    if dep then 
	      make_arity_dep env sigma (DOP0(Sort kinds)) ar 
		(appvect (mind,rel_vect i nparams))
            else 
	      make_arity_nodep env sigma (DOP0(Sort kinds)) ar 
	  in 
	  DOP2(Lambda,typP,DLAM(Name(id_of_string "P"),put_arity (i+1) rest))
      | [] -> 
	  make_branch 0 listdepkind 
    in 
    let (mispeci,dep,kind) = List.nth listdepkind p in
    if is_recursive (List.map (fun (mispec,_,_) -> mispec.mis_tyi) listdepkind)
      recargsvec.(mispeci.mis_tyi) then 
   	it_lambda_name env (put_arity 0 listdepkind) lnamespar
   else 
     mis_make_case_com (Some dep) env sigma mispeci kind 
  in 
  Array.init nrec make_one_rec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let make_case_com depopt env sigma ity kind =
  let mispec = lookup_mind_specif ity env in 
  mis_make_case_com depopt env sigma mispec kind

let make_case_dep sigma   = make_case_com (Some true) sigma
let make_case_nodep sigma = make_case_com (Some false) sigma 
let make_case_gen sigma   = make_case_com None sigma


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
       let mip = mispeci.mis_mip  in
       let kelim = mis_kelim mispeci in
       if not (List.exists (base_sort_cmp CONV kinds) kelim) then 
	 errorlabstrm "Bad Induction"
	   [<'sTR (if dep then "Dependent" else "Non dependend");
	     'sTR " induction for type "; 
	     print_id mip.mind_typename;
	     'sTR " and sort "; print_sort kinds; 
	     'sTR "is not allowed">])
    listdepkind

let build_indrec env sigma = function 
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
		error 
		  "Induction schemes concern mutually inductive types") 
	   lrecspec) 
      in
      let _ = check_arities listdepkind in 
      mis_make_indrec env sigma listdepkind mispec
  | _ -> assert false


(**********************************************************************)
(* To handle old Case/Match syntax in Pretyping                       *)

(***********************************)
(* To interpret the Match operator *)

let type_mutind_rec env sigma indspec pt p c = 
  let mind = indspec.mind in
  let mispec = lookup_mind_specif indspec.mind env in 
  let recargs = mis_recarg mispec in
  if is_recursive [mispec.mis_tyi] recargs then
    let dep = find_case_dep_nparams env sigma (c,p) (mind, indspec.params) pt in 
    let ntypes = mis_nconstr mispec 
    and tyi = mispec.mis_tyi 
    and nparams = mis_nparams mispec in
    let init_depPvec i = if i=mispec.mis_tyi then Some(dep,p) else None in
    let depPvec = Array.init ntypes init_depPvec in
    let realargs = indspec.realargs in
    let vargs = Array.of_list indspec.params in
    let (constrvec,typeconstrvec) = mis_type_mconstructs mispec in
    let lft = array_map3 (type_rec_branch dep env sigma (vargs,depPvec,0)) 
                constrvec typeconstrvec recargs in
    (lft,
     if dep then applist(p,realargs@[c]) 
     else applist(p,realargs) )
  else 
    type_case_branches env sigma indspec pt p c

let type_rec_branches recursive env sigma ct pt p c =
  try
    let indspec = try_mutind_of env sigma ct in
    if recursive then 
      type_mutind_rec env sigma indspec  pt p c
    else 
      type_case_branches env sigma indspec pt p c
  with Induc -> error"Elimination on a non-inductive type 1"

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

let build_notdep_pred env sigma mispec nparams globargs pred =
  let arity = mis_arity mispec in
  let lamarity = to_lambda nparams arity in
  let inst_arity = 
    whd_beta env sigma (appvect (lamarity,Array.of_list globargs)) in
  let k = nb_prod inst_arity in
  let env,_,npredlist = push_and_liftl k [] inst_arity [insert_lifted pred] in
  let npred = (match npredlist with [npred] -> npred 
		 | _ -> anomaly "push_and_lift should not behave this way") in
  let _,finalpred,_ = lam_and_popl k env (extract_lifted npred) [] 
  in 
  finalpred

let pred_case_ml_fail env sigma isrec (mI,globargs,la) (i,ft) =
  let (_,j),_ = mI in
  let mispec = lookup_mind_specif mI env in
  let nparams = mis_nparams mispec in
  let pred =
    let recargs = (mis_recarg mispec) in
    assert (Array.length recargs <> 0);
    let recargi = recargs.(i-1) in
    let nbrec = if isrec then count_rec_arg j recargi else 0 in
    let nb_arg = List.length (recargs.(i-1)) + nbrec in
    let pred = concl_n env sigma nb_arg ft in
    if noccur_bet 1 nb_arg pred then 
      lift (-nb_arg) pred
    else 
      failwith "Dependent"
  in
  if la = [] then 
    pred
  else (* we try with [_:T1]..[_:Tn](lift n pred) *)
    build_notdep_pred env sigma mispec nparams globargs pred  

let pred_case_ml env sigma isrec (c,ct) lf (i,ft) = 
    pred_case_ml_fail env sigma isrec ct (i,ft)

(* similar to pred_case_ml but does not expect the list lf of braches *)
let pred_case_ml_onebranch env sigma isrec (c,ct) (i,f,ft) = 
    pred_case_ml_fail env sigma isrec ct (i,ft)

(* Used in Program only *)      
let make_case_ml isrec pred c ci lf = 
  if isrec then 
    DOPN(XTRA("REC"),Array.append [|pred;c|] lf)
  else 
    mkMutCaseA ci pred c lf
