
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Term
open Inductive
open Environ
open Reduction
open Typing

let whd_betadeltaiota_empty env = whd_betadeltaiota env Evd.empty

let make_lambda_string s t c = DOP2(Lambda,t,DLAM(Name(id_of_string s),c))

let make_prod_string s t c = DOP2(Prod,t,DLAM(Name(id_of_string s),c))

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

(*********************************************)
(* lc is the list of the constructors of ind *)
(*********************************************)

let mis_make_case_com depopt sigma mispec kinds =
  let sp = mispec.mis_sp in
  let tyi = mispec.mis_tyi in 
  let cl = mispec.mis_args in 
  let nparams = mis_nparams mispec in
  let mip = mispec.mis_mip in
  let mind = DOPN(MutInd(sp,tyi),cl) in
  let kd = mis_kd mispec in
  let kn = mis_kn mispec in
  let t = mis_arity mispec in
  let (lc,lct) = mis_type_mconstructs mispec in
  let lnames,sort = splay_prod sigma t in
  let nconstr = Array.length lc in
  let dep = match depopt with 
    | None -> (sort<>DOP0(Sort(Prop Null)))
    | Some d -> d
  in
  let _ =
    if dep then begin
      if not (List.exists (sort_cmp CONV_X kinds) kd) then 
       	let pm = pTERM mind in
       	let ps = pTERM (DOP0(Sort kinds)) in
       	errorlabstrm "Case analysis"
          [< 'sTR "Dependent case analysis on sort: "; ps; 'fNL;
             'sTR "is not allowed for inductive definition: "; pm >]
    end else if not (List.exists (sort_cmp CONV_X kinds) kn) then 
      let pm = pTERM mind in
      let ps = pTERM (DOP0(Sort kinds)) in
      errorlabstrm "Case analysis"
       	[< 'sTR "Non Dependent case analysis on sort: "; ps; 'fNL;
           'sTR "is not allowed for inductive definition: "; pm >]
  in
  let lnamesar,lnamespar = chop_list (List.length lnames - nparams) lnames in
  let lgar = List.length lnamesar in
  let ar = hnf_prod_appvect sigma "make_case_dep" t (rel_vect 0 nparams) in
  let typP = 
    if dep then 
      make_arity_dep (DOP0(Sort kinds)) ar 
       	(appvect (mind,rel_vect 0 nparams))
    else 
      make_arity_nodep (DOP0(Sort kinds)) ar 
  in 
  let rec add_branch k = 
    if k = nconstr then 
      it_lambda_name 
       	(lambda_create 
           (appvect (mind,
                     (Array.append (rel_vect (nconstr+lgar+1) nparams)
                       	(rel_vect 0 lgar))),
            mkMutCaseA (ci_of_mind mind)
              (Rel (nconstr+lgar+2))
              (Rel 1)
	   (* (appvect (mind,
              (Array.append (rel_vect (nconstr+lgar+2) nparams)
              (rel_vect 1 lgar)))) *)
              (rel_vect (lgar+1) nconstr)))
       	(lift_context (nconstr+1) lnamesar)
    else 
      make_lambda_string "f" 
       	(if dep then 
	   type_one_branch_dep 
             (sigma,nparams,(rel_list (k+1) nparams),Rel (k+1)) lc.(k) lct.(k)
         else 
	  type_one_branch_nodep 
            (sigma,nparams,(rel_list (k+1) nparams),Rel (k+1)) lct.(k))
       	(add_branch (k+1))
  in 
  it_lambda_name (make_lambda_string "P" typP (add_branch 0)) lnamespar
    
let make_case_com depopt sigma mind kinds =
  let ity = mrectype_spec sigma mind in
  let (sp,tyi,cl) = destMutInd ity in
  let mispec = mind_specif_of_mind ity in 
  mis_make_case_com depopt sigma mispec kinds

let make_case_dep sigma   = make_case_com (Some true) sigma
let make_case_nodep sigma = make_case_com (Some false) sigma 
let make_case_gen sigma   = make_case_com None sigma


(* check if the type depends recursively on one of the inductive scheme *)

(* Building the recursive elimination *)


(***********************************************************************
* t is the type of the constructor co and recargs is the information on 
* the recursive calls.                                                  
* build the type of the corresponding branch of the recurrence principle
* assuming f has this type, branch_rec gives also the term 
*   [x1]..[xk](f xi (F xi) ...) to be put in the corresponding branch of 
* the case operation
* FPvect gives for each inductive definition if we want an elimination 
* on it with which predicate and which recursive function. 
************************************************************************)

let simple_prod (n,t,c) = DOP2(Prod,t,DLAM(n,c))
let make_prod_dep dep = if dep then prod_name else simple_prod

let type_rec_branch dep (sigma,vargs,depPvect,decP) co t recargs = 
  let make_prod = make_prod_dep dep in
  let nparams = Array.length vargs in
  let st = hnf_prod_appvect sigma "type_rec_branch" t vargs in
  let process_pos depK pk = 
    let rec prec i p = 
      match whd_betadeltaiota_stack sigma p [] with 
	| (DOP2(Prod,t,DLAM(n,c))),[] -> make_prod (n,t,prec (i+1) c)
     	| (DOPN(MutInd _,_),largs) -> 
	    let (_,realargs) = chop_list nparams largs in 
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
    match whd_betadeltaiota_stack sigma c [] with 
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
		 make_prod (n,t,process_constr (i+1) c_0 rest 
                              (mkAppList (lift 1 co) [Rel 1]))
             | Some(dep',p) -> 
		 let nP = lift (i+1+decP) p in
		 let t_0 = process_pos dep' nP (lift 1 t) in 
		 make_prod_dep (dep or dep')
                   (n,t,mkArrow t_0 (process_constr (i+2) (lift 1 c_0) rest
				       (mkAppList (lift 2 co) [Rel 2]))))
      | (DOPN(MutInd(_,tyi),_),largs) -> 
      	  let nP = match depPvect.(tyi) with 
	    | Some(_,p) -> lift (i+decP) p
	    | _ -> assert false in
      	  let (_,realargs) = chop_list nparams largs in
      	  let base = applist (nP,realargs) in
          if dep then mkAppList base [co] else base
      | _ -> assert false
  in 
  process_constr 0 st recargs (appvect(co,vargs))

let rec_branch_arg (sigma,vargs,fvect,decF) f t recargs = 
  let nparams = Array.length vargs in
  let st = hnf_prod_appvect sigma "type_rec_branch" t vargs in
  let process_pos fk  = 
    let rec prec i p = 
      (match whd_betadeltaiota_stack sigma p [] with 
	 | (DOP2(Prod,t,DLAM(n,c))),[] -> lambda_name (n,t,prec (i+1) c) 
     	 | (DOPN(MutInd _,_),largs) -> 
             let (_,realargs) = chop_list nparams largs
             and arg = appvect (Rel (i+1),rel_vect 0 i) in 
             applist(lift i fk,realargs@[arg])
     	 | _ -> assert false) 
    in
    prec 0 
  in
  let rec process_constr i c f recargs = 
    match whd_betadeltaiota_stack sigma c [] with 
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
		 lambda_name 
		   (n,t,process_constr (i+1) c_0 
		      (applist(whd_beta_stack (lift 1 f) [(Rel 1)])) rest)
             | Some(_,f_0) -> 
		 let nF = lift (i+1+decF) f_0 in
		 let arg = process_pos nF (lift 1 t) in 
                 lambda_name 
		   (n,t,process_constr (i+1) c_0 
		      (applist(whd_beta_stack (lift 1 f) [(Rel 1); arg])) 
		      rest))
      | (DOPN(MutInd(_,tyi),_),largs) -> f
      | _ -> assert false
  in 
  process_constr 0 st f recargs 

let mis_make_indrec sigma listdepkind mispec =
  let nparams = mis_nparams mispec in
  let recargsvec = mis_recargs mispec in
  let ntypes = mis_ntypes mispec in
  let mind_arity = mis_arity mispec in 
  let (lnames, ckind) = splay_prod sigma mind_arity in
  let kind = destSort ckind in
  let lnamespar = lastn nparams lnames in
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
            (Array.set depPvec mispeci.tyi (Some(dep,Rel k));
             assign (k-1) rest)
    in 
    assign nrec listdepkind  
  in 
  let make_one_rec p = 
    let makefix nbconstruct = 
      let rec mrec i ln ltyp ldef = function 
	| (mispeci,dep,_)::rest -> 
	    let tyi = mispeci.tyi in
	    let mind = DOPN(MutInd (mispeci.sp,tyi),mispeci.args) in
	    let (_,lct) = mis_type_mconstructs mispeci in
	    let nctyi = Array.length lct in (* nb constructeurs du type *) 
	    let realar =  hnf_prod_appvect sigma "make_branch" 
			    (mis_arity mispeci) 
			    (rel_vect (nrec+nbconstruct) nparams) in
               (* arity in the contexte P1..Prec f1..f_nbconstruct *)
	    let lnames,_ = splay_prod sigma realar in 
	    let nar = List.length lnames in 
	    let decf = nar+nrec+nbconstruct+nrec in 
	    let dect = nar+nrec+nbconstruct in
	    let vecfi = rel_vect (dect+1-i-nctyi) nctyi in
	    let branches = 
	      map3_vect 
		(rec_branch_arg (sigma,rel_vect (decf+1) nparams,
				 depPvec,nar+1))
                vecfi lct recargsvec.(tyi) in
	    let j = (match depPvec.(tyi) with 
		       | Some (_,Rel j) -> j 
		       | _ -> assert false) in
	    let deftyi = 
	      it_lambda_name 
		(lambda_create 
		   (appvect (mind,(Array.append (rel_vect decf nparams)
				     (rel_vect 0 nar))),
		    mkMutCaseA (ci_of_mind mind)
                      (Rel (decf-nrec+j+1)) (Rel 1) branches))
		(lift_context nrec lnames)
	    in
	    let typtyi = 
	      it_prod_name 
		(prod_create 
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
		(tabulate_list (fun _ -> Name(id_of_string "F")) nrec) fixdef 
	    in 
            let fixspec = Array.append fixtyi [|makefixdef|] in 
	    DOPN(Fix(fixn,p),fixspec)
      in 
      mrec 0 [] [] [] 
    in 
    let rec make_branch i = function 
      | (mispeci,dep,_)::rest -> 
	  let tyi = mispeci.tyi in
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
		type_rec_branch dep (sigma,vargs,depPvec,i+j) co t recarg
	      in 
	      DOP2(Lambda,p_0,DLAM(Name (id_of_string "f"),onerec (j+1)))
	  in onerec 0
      | [] -> 
	  makefix i listdepkind
    in 
    let rec put_arity i = function 
      | ((mispeci,dep,kinds)::rest) -> 
	  let mind = DOPN(MutInd (mispeci.sp,mispeci.tyi),mispeci.args) in 
	  let arity = mis_arity mispeci in 
	  let ar =
	    hnf_prod_appvect sigma "put_arity" arity (rel_vect i nparams)
	  in 
	  let typP = 
	    if dep then 
	      make_arity_dep (DOP0(Sort kinds)) ar 
		(appvect (mind,rel_vect i nparams))
            else 
	      make_arity_nodep (DOP0(Sort kinds)) ar 
	  in 
	  DOP2(Lambda,typP,DLAM(Name(id_of_string "P"),put_arity (i+1) rest))
      | [] -> 
	  make_branch 0 listdepkind 
    in 
    let (mispeci,dep,kind) = List.nth listdepkind p in
    if is_recursive (List.map (fun (mispec,_,_) -> mispec.tyi) listdepkind)
      recargsvec.(mispeci.tyi) then 
   	it_lambda_name (put_arity 0 listdepkind) lnamespar
   else 
     mis_make_case_com (Some dep) sigma mispeci kind 
  in 
  tabulate_vect make_one_rec nrec

let make_indrec sigma listdepkind mind =
  let ity = minductype_spec sigma mind in
  let (sp,tyi,largs) = destMutInd ity in
  let mispec = mind_specif_of_mind ity in  
  mis_make_indrec sigma listdepkind mispec 
    
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

let check_arities listdepkind = 
  List.iter 
    (function (mispeci,dep,kinds) -> 
       let mip = mispeci.mip  in
       if dep then 
	 let kd = mis_kd mispeci in 
	 if List.exists (sort_cmp CONV_X kinds) kd then 
	   ()
	 else 
	   errorlabstrm "Bad Induction"
	     [<'sTR "Dependent induction for type "; 
	       print_id mip.mINDTYPENAME;
	       'sTR " and sort "; pTERM (DOP0(Sort kinds)); 
	       'sTR "is not allowed">]
       else 
	 let kn = mis_kn mispeci in 
	 if List.exists (sort_cmp CONV_X kinds) kn then 
	   ()
         else 
	   errorlabstrm "Bad Induction"
	     [<'sTR "Non dependent induction for type "; 
	       print_id mip.mINDTYPENAME;
	       'sTR " and sort "; pTERM (DOP0(Sort kinds)); 
	       'sTR "is not allowed">])
    listdepkind

let build_indrec sigma = function 
  | ((mind,dep,s)::lrecspec) ->
      let redind = minductype_spec sigma mind in 
      let (sp,tyi,_) = destMutInd redind in 
      let listdepkind = 
    	(mind_specif_of_mind redind, dep,s)::
    	(List.map (function (mind',dep',s') ->
		     let redind' = minductype_spec sigma mind' in
		     let (sp',_,_) = destMutInd redind' in
		     if sp=sp' then 
		       (mind_specif_of_mind redind',dep',s') 
		     else 
		       error 
			 "Induction schemes concern mutually inductive types") 
	   lrecspec) 
      in
      let _ = check_arities listdepkind in 
      make_indrec sigma listdepkind mind
  | _ -> assert false
	

(* In order to interpret the Match operator *)

let type_mutind_rec env sigma ct pt p c = 
  let (mI,largs as mind) = find_minductype sigma ct in
  let mispec = mind_specif_of_mind mI in 
  let recargs =  mis_recarg mispec in
  if is_recursive [mispec.tyi] recargs then
    let dep = find_case_dep_mis env sigma mispec (c,p) mind pt in 
    let ntypes = mis_nconstr mispec 
    and tyi = mispec.tyi 
    and nparams = mis_nparams mispec in
    let depPvec = Array.create ntypes (None : (bool * constr) option) in 
    let _ = Array.set depPvec mispec.tyi (Some(dep,p)) in 
    let (pargs,realargs) = chop_list nparams largs in
    let vargs = Array.of_list pargs in
    let (constrvec,typeconstrvec) = mis_type_mconstructs mispec in
    let lft = map3_vect (type_rec_branch dep (sigma,vargs,depPvec,0)) 
                constrvec typeconstrvec recargs in
    (mI, lft,
     if dep then applist(p,realargs@[c]) 
     else applist(p,realargs) )
  else 
    type_case_branches env sigma ct pt p c

let is_mutind sigma ct =  
  try let _ = find_minductype sigma ct in true with Induc -> false

let type_rec_branches recursive sigma env ct pt p c = 
  match whd_betadeltaiota_stack sigma ct [] with 
    | (DOPN(MutInd _,_),_) -> 
	if recursive then 
	  type_mutind_rec env sigma ct pt p c
        else 
	  type_case_branches env sigma ct pt p c
    | _ -> error"Elimination on a non-inductive type 1"

(* Awful special reduction function which skips abstraction on Xtra in order to 
   be safe for Program ... *)

let stacklamxtra recfun = 
  let rec lamrec sigma p_0 p_1 = match p_0,p_1 with 
    | (stack, (DOP2(Lambda,DOP1(XTRA("COMMENT",[]),_),DLAM(_,c)) as t)) ->
        recfun stack (substl sigma t)
    | ((h::t), (DOP2(Lambda,_,DLAM(_,c)))) -> lamrec (h::sigma) t c
    | (stack, t) -> recfun stack (substl sigma t)
  in 
  lamrec 

let rec whrec x stack =
  match x with   
    | DOP2(Lambda,DOP1(XTRA("COMMENT",[]),c),DLAM(name,t)) ->
    	let t' = applist (whrec t (List.map (lift 1) stack)) in 
	DOP2(Lambda,DOP1(XTRA("COMMENT",[]),c),DLAM(name,t')),[]
    | DOP2(Lambda,c1,DLAM(name,c2)) ->
    	(match stack with
	   | [] -> (DOP2(Lambda,c1,DLAM(name,whd_betaxtra c2)),[])
	   | a1::rest -> stacklamxtra (fun l x -> whrec x l) [a1] rest c2)
    | DOPN(AppL,cl)      -> whrec (hd_vect cl) (app_tl_vect cl stack)
    | DOP2(Cast,c,_)       ->  whrec c stack
    | x -> x,stack

and whd_betaxtra x = applist(whrec x [])

let transform_rec env sigma cl (ct,pt) = 
  let (mI,largs as mind) = find_minductype sigma ct in
  let p = cl.(0)
  and c = cl.(1)
  and lf = Array.sub cl 2 ((Array.length cl) - 2) in
  let mispec = mind_specif_of_mind mI in 
  let recargs =  mis_recarg mispec in
  let expn = Array.length recargs in
  if Array.length lf <> expn then error_number_branches CCI env c ct expn;
  if is_recursive [mispec.tyi] recargs then
    let dep = find_case_dep_mis env sigma mispec (c,p) mind pt in 
    let ntypes = mis_nconstr mispec 
    and tyi = mispec.tyi 
    and nparams = mis_nparams mispec in
    let depFvec = Array.create ntypes (None : (bool * constr) option) in 
    let _ = Array.set depFvec mispec.tyi (Some(dep,Rel 1)) in 
    let (pargs,realargs) = chop_list nparams largs in
    let vargs = Array.of_list pargs in
    let (_,typeconstrvec) = mis_type_mconstructs mispec in
    (* build now the fixpoint *)
    let realar =
      hnf_prod_appvect sigma "make_branch" (mis_arity mispec) vargs in
    let lnames,_ = splay_prod sigma realar in 
    let nar = List.length lnames in
    let branches = 
      map3_vect 
	(fun f t reca -> 
	   whd_betaxtra
             (rec_branch_arg
                (sigma,(Array.map (lift (nar+2)) vargs),depFvec,nar+1)
                f t reca))
        (Array.map (lift (nar+2)) lf) typeconstrvec recargs 
    in 
    let deffix = 
      it_lambda_name 
	(lambda_create 
	   (appvect (mI,Array.append (Array.map (lift (nar+1)) vargs)
                       (rel_vect 0 nar)),
            mkMutCaseA (ci_of_mind mI) 
              (lift (nar+2) p) (Rel 1) branches))
        (lift_context 1 lnames) 
    in
    if noccurn 1 deffix then 
      whd_beta (applist (pop deffix,realargs@[c]))
    else
      let typPfix = 
	it_prod_name  
	  (prod_create (appvect (mI,(Array.append 
				       (Array.map (lift nar) vargs)
				       (rel_vect 0 nar))),
			(if dep then applist (whd_beta_stack (lift (nar+1) p)
                                                (rel_list 0 (nar+1)))
			 else applist (whd_beta_stack (lift (nar+1) p) 
                                         (rel_list 1 nar)))))
          lnames 
      in
      let fix = DOPN(Fix([|nar|],0),
		     [|typPfix;
		       DLAMV(Name(id_of_string "F"),[|deffix|])|])
      in 
      applist (fix,realargs@[c])
  else 
    mkMutCaseA (ci_of_mind mI) p c lf

(*** Building ML like case expressions without types ***)

let concl_n sigma = 
  let rec decrec m c = if m = 0 then c else 
    match whd_betadeltaiota sigma c with
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
    
let norec_branch_scheme sigma typc =
  let rec crec typc = match whd_betadeltaiota sigma typc with 
    | DOP2(Prod,c,DLAM(name,t)) -> DOP2(Prod,c,DLAM(name,crec t))
    | _ -> mkExistential
  in 
  crec typc

let rec_branch_scheme sigma j typc recargs = 
  let rec crec (typc,recargs) = 
    match whd_betadeltaiota sigma typc, recargs with 
      | (DOP2(Prod,c,DLAM(name,t)),(ra::reca)) -> 
          DOP2(Prod,c,
	       match ra with 
		 | Mrec k -> 
                     if k=j then 
		       DLAM(name,mkArrow mkExistential
                              (crec (lift 1 t,reca)))
                     else 
		       DLAM(name,crec (t,reca))
                 | _ -> DLAM(name,crec (t,reca)))
      | (_,_) -> mkExistential
  in 
  crec (typc,recargs) 
    
let branch_scheme sigma isrec i mind = 
  let typc =  type_inst_construct sigma i mind in 
  if isrec then
    let (mI,_) = find_mrectype sigma mind in
    let (_,j,_) = destMutInd mI in
    let mispec = mind_specif_of_mind mI in 
    let recarg = (mis_recarg mispec).(i-1) in
    rec_branch_scheme sigma j typc recarg
  else 
    norec_branch_scheme sigma typc

(* if arity of mispec is (p_bar:P_bar)(a_bar:A_bar)s where p_bar are the
 * K parameters. Then then build_notdep builds the predicate
 * [a_bar:A'_bar](lift k pred) 
 * where A'_bar = A_bar[p_bar <- globargs] *)

let build_notdep_pred mispec nparams globargs pred =
  let arity = mis_arity mispec in
  let lamarity = to_lambda nparams arity in
  let inst_arity = whd_beta (appvect (lamarity,Array.of_list globargs)) in
  let k = nb_prod inst_arity in
  let env,_,npredlist = push_and_liftl k [] inst_arity [insert_lifted pred] in
  let npred = (match npredlist with [npred] -> npred 
		 | _ -> anomaly "push_and_lift should not behave this way") in
  let _,finalpred,_ = lam_and_popl k env (extract_lifted npred) [] 
  in 
  finalpred

let pred_case_ml_fail sigma isrec ct (i,ft) =
  try 
    let (mI,largs) = find_mrectype sigma ct in
    let (_,j,_) = destMutInd mI in
    let mispec = mind_specif_of_mind mI in
    let nparams = mis_nparams mispec in
    let (globargs,la) = chop_list nparams largs in
    let pred = 
      let recargs = (mis_recarg mispec) in
      assert (Array.length recargs <> 0);
      let recargi = recargs.(i-1) in
      let nbrec = if isrec then count_rec_arg j recargi else 0 in
      let nb_arg = List.length (recargs.(i-1)) + nbrec in
      let pred = concl_n sigma nb_arg ft in
      if noccur_bet 1 nb_arg pred then 
	lift (-nb_arg) pred
      else 
	failwith "Dependent"
    in
    if la = [] then 
      pred
    else (* we try with [_:T1]..[_:Tn](lift n pred) *)
      build_notdep_pred mispec nparams globargs pred  
  with Induc -> 
    failwith "Inductive"

let pred_case_ml env sigma isrec (c,ct) lf (i,ft) = 
  try 
    pred_case_ml_fail sigma isrec ct (i,ft)
  with Failure mes -> 
    error_ml_case mes env c ct lf.(i-1) ft

(* similar to pred_case_ml but does not expect the list lf of braches *)
let pred_case_ml_onebranch env sigma isrec (c,ct) (i,f,ft) = 
  try 
    pred_case_ml_fail sigma isrec ct (i,ft)
  with Failure mes -> 
    error_ml_case mes env c ct f ft
      
let make_case_ml isrec pred c ci lf = 
  if isrec then 
    DOPN(XTRA("REC",[]),Array.append [|pred;c|] lf)
  else 
    mkMutCaseA ci pred c lf
