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
open Libnames
open Nameops
open Term
open Termops
open Declarations
open Inductive
open Inductiveops
open Instantiate
open Environ
open Reductionops
open Typeops
open Type_errors
open Indtypes (* pour les erreurs *)
open Declare
open Safe_typing
open Nametab

let make_prod_dep dep env = if dep then prod_name env else mkProd
let mkLambda_string s t c = mkLambda (Name (id_of_string s), t, c)

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

(**********************************************************************)
(* Building case analysis schemes *)
(* Nouvelle version, plus concise mais plus co�teuse � cause de
   lift_constructor et lift_inductive_family qui ne se contentent pas de 
   lifter les param�tres globaux *)

let mis_make_case_com depopt env sigma (ind,mib,mip) kind =
  let lnamespar = mip.mind_params_ctxt in
  let dep = match depopt with 
    | None -> mip.mind_sort <> (Prop Null)
    | Some d -> d
  in
  if not (List.exists ((=) kind) mip.mind_kelim) then
    raise
      (InductiveError
	 (NotAllowedCaseAnalysis
	    (dep,(new_sort_in_family kind),ind)));

  let nbargsprod = mip.mind_nrealargs + 1 in

  (* Pas g�nant car env ne sert pas � typer mais juste � renommer les Anonym *)
  (* mais pas tr�s joli ... (mais manque get_sort_of � ce niveau) *)
  let env' = push_rel_context lnamespar env in

  let indf = make_ind_family(ind, extended_rel_list 0 lnamespar) in
  let constrs = get_constructors env indf in

  let rec add_branch env k = 
    if k = Array.length mip.mind_consnames then
      let nbprod = k+1 in
      let indf = make_ind_family(ind,extended_rel_list nbprod lnamespar) in
      let lnamesar,_ = get_arity env indf in
      let ci = make_default_case_info env ind in
      it_mkLambda_or_LetIn_name env'
       	(lambda_create env'
           (build_dependent_inductive env indf,
            mkCase (ci,
		       mkRel (nbprod+nbargsprod),
		       mkRel 1,
		       rel_vect nbargsprod k)))
       	lnamesar
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      let t = build_branch_type env dep (mkRel (k+1)) cs in
      mkLambda_string "f" t
	(add_branch (push_rel (Anonymous, None, t) env) (k+1))
  in
  let typP = make_arity env' dep indf (new_sort_in_family kind) in
  it_mkLambda_or_LetIn_name env 
    (mkLambda_string "P" typP
       (add_branch (push_rel (Anonymous,None,typP) env') 0)) lnamespar
    
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

let type_rec_branch is_rec dep env sigma (vargs,depPvect,decP) tyi cs recargs = 
  let make_prod = make_prod_dep dep in
  let nparams = List.length vargs in
  let process_pos env depK pk =
    let rec prec env i sign p =
      let p',largs = whd_betadeltaiota_nolet_stack env sigma p in
      match kind_of_term p' with
	| Prod (n,t,c) ->
	    let d = (n,None,t) in
	    make_prod env (n,t,prec (push_rel d env) (i+1) (d::sign) c)
	| LetIn (n,b,t,c) ->
	    let d = (n,Some b,t) in
	    mkLetIn (n,b,t,prec (push_rel d env) (i+1) (d::sign) c)
     	| Ind (_,_) ->
	    let (_,realargs) = list_chop nparams largs in
	    let base = applist (lift i pk,realargs) in
            if depK then 
	      Reduction.beta_appvect
                base [|applist (mkRel (i+1),extended_rel_list 0 sign)|]
            else 
	      base
      	| _ -> assert false 
    in
    prec env 0 []
  in
  let rec process_constr env i c recargs nhyps li =
    if nhyps > 0 then match kind_of_term c with 
      | Prod (n,t,c_0) ->
          let (optionpos,rest) = 
	    match recargs with 
	      | [] -> None,[]
              | ra::rest ->
                  (match dest_recarg ra with 
	            | Mrec j when is_rec -> (depPvect.(j),rest)
	            | Imbr _  -> 
		        Options.if_verbose warning "Ignoring recursive call"; 
		        (None,rest) 
                    | _ -> (None, rest))
	  in 
          (match optionpos with 
	     | None -> 
		 make_prod env
		   (n,t,
		    process_constr (push_rel (n,None,t) env) (i+1) c_0 rest
		      (nhyps-1) (i::li))
             | Some(dep',p) -> 
		 let nP = lift (i+1+decP) p in
		 let t_0 = process_pos env dep' nP (lift 1 t) in 
		 make_prod_dep (dep or dep') env
                   (n,t,
		    mkArrow t_0
		      (process_constr
			 (push_rel (n,None,t)
			    (push_rel (Anonymous,None,t_0) env))
			 (i+2) (lift 1 c_0) rest (nhyps-1) (i::li))))
      | LetIn (n,b,t,c_0) ->
	  mkLetIn (n,b,t,
		   process_constr
		     (push_rel (n,Some b,t) env)
		     (i+1) c_0 recargs (nhyps-1) li)
      | _ -> assert false
    else
      if dep then
	let realargs = List.map (fun k -> mkRel (i-k)) (List.rev li) in
        let params = List.map (lift i) vargs in
        let co = applist (mkConstruct cs.cs_cstr,params@realargs) in
	Reduction.beta_appvect c [|co|]
      else c
  in
  let nhyps = List.length cs.cs_args in
  let nP = match depPvect.(tyi) with 
    | Some(_,p) -> lift (nhyps+decP) p
    | _ -> assert false in
  let base = appvect (nP,cs.cs_concl_realargs) in
  let c = it_mkProd_or_LetIn base cs.cs_args in
  process_constr env 0 c recargs nhyps []

let make_rec_branch_arg env sigma (nparams,fvect,decF) f cstr recargs = 
  let process_pos env fk  =
    let rec prec env i hyps p =
      let p',largs = whd_betadeltaiota_nolet_stack env sigma p in
      match kind_of_term p' with
	| Prod (n,t,c) ->
	    let d = (n,None,t) in
	    lambda_name env (n,t,prec (push_rel d env) (i+1) (d::hyps) c)
	| LetIn (n,b,t,c) ->
	    let d = (n,Some b,t) in
	    mkLetIn (n,b,t,prec (push_rel d env) (i+1) (d::hyps) c)
     	| Ind _ -> 
            let (_,realargs) = list_chop nparams largs
            and arg = appvect (mkRel (i+1),extended_rel_vect 0 hyps) in 
            applist(lift i fk,realargs@[arg])
     	| _ -> assert false
    in
    prec env 0 []
  in
  (* ici, cstrprods est la liste des produits du constructeur instanti� *)
  let rec process_constr env i f = function
    | (n,None,t as d)::cprest, recarg::rest -> 
        let optionpos = 
	  match dest_recarg recarg with 
            | Norec   -> None
            | Imbr _  -> None
            | Mrec i  -> fvect.(i)
	in 
        (match optionpos with 
           | None ->
	       lambda_name env
		 (n,t,process_constr (push_rel d env) (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1)])))
		    (cprest,rest))
           | Some(_,f_0) -> 
	       let nF = lift (i+1+decF) f_0 in
	       let arg = process_pos env nF (lift 1 (body_of_type t)) in 
               lambda_name env
		 (n,t,process_constr (push_rel d env) (i+1)
		    (whd_beta (applist (lift 1 f, [(mkRel 1); arg])))
		    (cprest,rest)))
    | (n,Some c,t as d)::cprest, rest ->
	mkLetIn
	  (n,c,t,
	   process_constr (push_rel d env) (i+1) (lift 1 f)
	     (cprest,rest))
    | [],[] -> f
    | _,[] | [],_ -> anomaly "process_constr"

  in
  process_constr env 0 f (List.rev cstr.cs_args, recargs)

(* Main function *)
let mis_make_indrec env sigma listdepkind (ind,mib,mip) =
  let nparams = mip.mind_nparams in
  let lnamespar = mip.mind_params_ctxt in
  let nrec = List.length listdepkind in
  let depPvec =
    Array.create mib.mind_ntypes (None : (bool * constr) option) in 
  let _ = 
    let rec 
      assign k = function 
	| [] -> ()
        | (indi,mibi,mipi,dep,_)::rest -> 
            (Array.set depPvec (snd indi) (Some(dep,mkRel k));
             assign (k-1) rest)
    in 
    assign nrec listdepkind in 
  let recargsvec =
    Array.map (fun mip -> mip.mind_recargs) mib.mind_packets in
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln ltyp ldef = function
	| (indi,mibi,mipi,dep,_)::rest ->
	    let tyi = snd indi in
	    let nctyi =
              Array.length mipi.mind_consnames in (* nb constructeurs du type *) 

            (* arity in the context of the fixpoint, i.e.
                P1..P_nrec f1..f_nbconstruct *)
	    let args = extended_rel_list (nrec+nbconstruct) lnamespar in
	    let indf = make_ind_family(indi,args) in
	    let lnames,_ = get_arity env indf in

	    let nar = mipi.mind_nrealargs in
	    let decf = nar+nrec+nbconstruct+nrec in 
	    let dect = nar+nrec+nbconstruct in
	    let vecfi = rel_vect (dect+1-i-nctyi) nctyi in

            (* constructors in context of the Cases expr, i.e.
                P1..P_nrec f1..f_nbconstruct F_1..F_nrec a_1..a_nar x:I *)
	    let args' = extended_rel_list (decf+1) lnamespar in
            let indf' = make_ind_family(indi,args') in
	    let constrs = get_constructors env indf' in
	    let branches = 
	      array_map3
		(make_rec_branch_arg env sigma (nparams,depPvec,nar+1))
                vecfi constrs
                (dest_subterms recargsvec.(tyi)) in
	    let j = (match depPvec.(tyi) with 
		       | Some (_,c) when isRel c -> destRel c 
		       | _ -> assert false) in
	    let deftyi = 
	      it_mkLambda_or_LetIn_name env
		(lambda_create env
		   (build_dependent_inductive env
                     (lift_inductive_family nrec indf),
		    mkCase (make_default_case_info env indi,
			       mkRel (dect+j+1), mkRel 1, branches)))
		(Termops.lift_rel_context nrec lnames)
	    in
	    let ind = build_dependent_inductive env indf in
	    let typtyi = 
	      it_mkProd_or_LetIn_name env
		(prod_create env
		   (ind,
		    (if dep then 
		       let ext_lnames = (Anonymous,None,ind)::lnames in
		       let args = extended_rel_list 0 ext_lnames in
		       applist (mkRel (nbconstruct+nar+j+1), args)
		     else
		       let args = extended_rel_list 1 lnames in
		       applist (mkRel (nbconstruct+nar+j+1), args))))
          	lnames
	    in 
	    mrec (i+nctyi) (nar::ln) (typtyi::ltyp) (deftyi::ldef) rest
        | [] -> 
	    let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in 
            let names = Array.create nrec (Name(id_of_string "F")) in
	    mkFix ((fixn,p),(names,fixtyi,fixdef))
      in 
      mrec 0 [] [] [] 
    in 
    let rec make_branch env i = function 
      | (indi,mibi,mipi,dep,_)::rest ->
          let tyi = snd indi in
	  let nconstr = Array.length mipi.mind_consnames in
	  let rec onerec env j = 
	    if j = nconstr then 
	      make_branch env (i+j) rest 
	    else 
	      let recarg = (dest_subterms recargsvec.(tyi)).(j) in
	      let vargs = extended_rel_list (nrec+i+j) lnamespar in
	      let indf = (indi, vargs) in
	      let cs = get_constructor (indi,mibi,mipi,vargs) (j+1) in
	      let p_0 =
		type_rec_branch
                  true dep env sigma (vargs,depPvec,i+j) tyi cs recarg
	      in 
	      mkLambda_string "f" p_0
		(onerec (push_rel (Anonymous,None,p_0) env) (j+1))
	  in onerec env 0
      | [] -> 
	  makefix i listdepkind
    in 
    let rec put_arity env i = function 
      | (indi,_,_,dep,kinds)::rest -> 
	  let indf = make_ind_family (indi,extended_rel_list i lnamespar) in
	  let typP = make_arity env dep indf (new_sort_in_family kinds) in
	  mkLambda_string "P" typP
	    (put_arity (push_rel (Anonymous,None,typP) env) (i+1) rest)
      | [] -> 
	  make_branch env 0 listdepkind 
    in 
    let (indi,mibi,mipi,dep,kind) = List.nth listdepkind p in
    let env' = push_rel_context lnamespar env in
    if mis_is_recursive_subset
      (List.map (fun (indi,_,_,_,_) -> snd indi) listdepkind)
      mipi.mind_recargs
    then 
      it_mkLambda_or_LetIn_name env (put_arity env' 0 listdepkind) lnamespar
    else 
      mis_make_case_com (Some dep) env sigma (indi,mibi,mipi) kind 
  in 
  list_tabulate make_one_rec nrec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let make_case_com depopt env sigma ity kind =
  let (mib,mip) = lookup_mind_specif env ity in 
  mis_make_case_com depopt env sigma (ity,mib,mip) kind

let make_case_dep env   = make_case_com (Some true) env
let make_case_nodep env = make_case_com (Some false) env 
let make_case_gen env   = make_case_com None env


(**********************************************************************)
(* [instanciate_indrec_scheme s rec] replace the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort = 
  let rec drec a = match kind_of_term a with
    | Cast (c,t) -> drec c 
    | Prod (n,t,c) -> mkProd (n, t, drec c)
    | Sort _ -> mkSort sort
    | _ -> assert false
  in 
  drec 

(* [npar] is the number of expected arguments (then excluding letin's) *)
let instanciate_indrec_scheme sort =
  let rec drec npar elim =
    match kind_of_term elim with
      | Lambda (n,t,c) -> 
	  if npar = 0 then 
	    mkLambda (n, change_sort_arity sort t, c)
	  else 
	    mkLambda (n, t, drec (npar-1) c)
      | LetIn (n,b,t,c) -> mkLetIn (n,b,t,drec npar c)
      | _ -> anomaly "instanciate_indrec_scheme: wrong elimination type"
  in
  drec

(* Change the sort in the type of an inductive definition, builds the corresponding eta-expanded term *)
let instanciate_type_indrec_scheme sort npars term =
  let rec drec np elim =
    match kind_of_term elim with
      | Prod (n,t,c) -> 
	  if np = 0 then 
            let t' = change_sort_arity sort t in
            mkProd (n, t', c),
            mkLambda (n, t', mkApp(term,Termops.rel_vect 0 (npars+1)))
	  else 
            let c',term' = drec (np-1) c in
	    mkProd (n, t, c'), mkLambda (n, t, term')
      | LetIn (n,b,t,c) -> let c',term' = drec np c in
           mkLetIn (n,b,t,c'), mkLetIn (n,b,t,term') 
      | _ -> anomaly "instanciate_type_indrec_scheme: wrong elimination type"
  in
  drec npars

(**********************************************************************)
(* Interface to build complex Scheme *)

let check_arities listdepkind = 
  List.iter 
    (function (indi,mibi,mipi,dep,kind) -> 
       let id = mipi.mind_typename  in
       let kelim = mipi.mind_kelim in
       if not (List.exists ((=) kind) kelim) then
	 raise
	   (InductiveError (BadInduction (dep, id, new_sort_in_family kind))))
    listdepkind

let build_mutual_indrec env sigma = function 
  | (mind,mib,mip,dep,s)::lrecspec ->
      let (sp,tyi) = mind in
      let listdepkind = 
    	(mind,mib,mip, dep,s)::
    	(List.map
	   (function (mind',mibi',mipi',dep',s') ->
	      let (sp',_) = mind' in
	      if sp=sp' then 
                let (mibi',mipi') = lookup_mind_specif env mind' in
		(mind',mibi',mipi',dep',s') 
	      else 
		raise (InductiveError NotMutualInScheme))
	   lrecspec)
      in
      let _ = check_arities listdepkind in 
      mis_make_indrec env sigma listdepkind (mind,mib,mip)
  | _ -> anomaly "build_indrec expects a non empty list of inductive types"

let build_indrec env sigma ind =
  let (mib,mip) = lookup_mind_specif env ind in
  let kind = family_of_sort mip.mind_sort in
  let dep = kind <> InProp in
  List.hd (mis_make_indrec env sigma [(ind,mib,mip,dep,kind)] (ind,mib,mip))

(**********************************************************************)
(* To handle old Case/Match syntax in Pretyping                       *)

(***********************************)
(* To interpret Case and Match operators *)

let type_rec_branches recursive env sigma indt pj c = 
  let IndType (indf,realargs) = indt in
  let p = pj.uj_val in
  let (ind,params) = dest_ind_family indf in
  let (mib,mip) = lookup_mind_specif env ind in
  let recargs = mip.mind_recargs in
  let tyi = snd ind in
  let is_rec = recursive && mis_is_recursive_subset [tyi] recargs in
  let dep = is_dependent_elimination env pj.uj_type indf in 
  let init_depPvec i = if i = tyi then Some(dep,p) else None in
  let depPvec = Array.init mib.mind_ntypes init_depPvec in
  let vargs = Array.of_list params in
  let constructors = get_constructors env indf in
  let lft =
    array_map2
      (type_rec_branch recursive dep env sigma (params,depPvec,0) tyi)
      constructors (dest_subterms recargs) in
  (lft,
   if dep then Reduction.beta_appvect p (Array.of_list (realargs@[c])) 
   else Reduction.beta_appvect p (Array.of_list realargs))
(* Non recursive case. Pb: does not deal with unification
    let (p,ra,_) = type_case_branches env (ind,params@realargs) pj c in
    (p,ra)
*)

(*s Eliminations. *)

let type_suff = "_rect"

let non_type_eliminations = [ (InProp,"_ind") ; (InSet,"_rec")]

let elimination_suffix = function
  | InProp -> "_ind"
  | InSet  -> "_rec"
  | InType -> "_rect"

let make_elimination_ident id s = add_suffix id (elimination_suffix s)
  
let declare_one_elimination ind =
  let (mib,mip) = Global.lookup_inductive ind in 
  let mindstr = string_of_id mip.mind_typename in
  let declare na c t =
    let kn = Declare.declare_constant (id_of_string na)
      (ConstantEntry
        { const_entry_body = c;
          const_entry_type = t;
          const_entry_opaque = false }, 
       NeverDischarge) in
    Options.if_verbose ppnl (str na ++ str " is defined"); 
    kn
  in
  let env = Global.env () in
  let sigma = Evd.empty in
  let elim_scheme = build_indrec env sigma ind in
  let npars = mip.mind_nparams in
  let make_elim s = instanciate_indrec_scheme s npars elim_scheme in
  let kelim = mip.mind_kelim in
(* in case the inductive has a type elimination, generates only one induction scheme, 
   the other ones share the same code with the apropriate type *)
   if List.mem InType kelim then
    let cte =
      declare (mindstr^type_suff) (make_elim (new_sort_in_family InType)) None
    in let c = mkConst cte and t = constant_type (Global.env ()) cte
    in List.iter  
	 (fun (sort,suff) -> 
            let (t',c') = instanciate_type_indrec_scheme (new_sort_in_family sort) npars c t
            in let _ = declare (mindstr^suff) c' (Some t')
            in ())
	 non_type_eliminations
   else (* Impredicative or logical inductive definition *)
     List.iter
    (fun (sort,suff) -> 
       if List.mem sort kelim then
	 let _ = declare (mindstr^suff) (make_elim (new_sort_in_family sort)) None in ())
     non_type_eliminations

let declare_eliminations sp =
  let mib = Global.lookup_mind sp in
(*
  let ids = ids_of_named_context mib.mind_hyps in
  if not (list_subset ids (ids_of_named_context (Global.named_context ()))) then    error ("Declarations of elimination scheme outside the section "^
    "of the inductive definition is not implemented");
*)
  if mib.mind_finite then
    for i = 0 to Array.length mib.mind_packets - 1 do
      declare_one_elimination (sp,i)
    done

(* Look up function for the default elimination constant *)

let lookup_eliminator ind_sp s =
  let kn,_ = ind_sp in
  let mp,dp,l = repr_kn kn in
  let id = add_suffix (id_of_label l) (elimination_suffix s) in
  let ref = ConstRef (make_kn mp dp (label_of_id id)) in
  try 
    let _ = full_name ref in
      constr_of_reference ref
  with Not_found ->
    try construct_reference None id
    with Not_found ->
      errorlabstrm "default_elim"
	(str "Cannot find the elimination combinator " ++
           pr_id id ++ spc () ++
	   str "The elimination of the inductive definition " ++
           pr_id id ++ spc () ++ str "on sort " ++ 
           spc () ++ print_sort_family s ++
	   str " is probably not allowed")


(*  let env = Global.env() in
  let path = sp_of_global None (IndRef ind_sp) in
  let dir, base = repr_path path in
  let id = add_suffix base (elimination_suffix s) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  try construct_absolute_reference (Names.make_path dir id)
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
    try construct_reference None id
    with Not_found ->
      errorlabstrm "default_elim"
	(str "Cannot find the elimination combinator " ++
           pr_id id ++ spc () ++
	   str "The elimination of the inductive definition " ++
           pr_id base ++ spc () ++ str "on sort " ++ 
           spc () ++ print_sort_family s ++
	   str " is probably not allowed")
*)
