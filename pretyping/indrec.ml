(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* File initially created by Christine Paulin, 1996 *)

(* This file builds various inductive schemes *)

open Pp
open Errors
open Util
open Names
open Libnames
open Globnames
open Nameops
open Term
open Vars
open Context
open Namegen
open Declarations
open Declareops
open Inductive
open Inductiveops
open Environ
open Reductionops
open Nametab

type dep_flag = bool

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of (*isrec:*) bool * sorts * pinductive
  | NotMutualInScheme of inductive * inductive

exception RecursionSchemeError of recursion_scheme_error

let make_prod_dep dep env = if dep then mkProd_name env else mkProd
let mkLambda_string s t c = mkLambda (Name (Id.of_string s), t, c)

(*******************************************)
(* Building curryfied elimination          *)
(*******************************************)

let is_private mib =
  match mib.mind_private with
  | Some true -> true
  | _ -> false

let check_privacy_block mib =
  if is_private mib then
    errorlabstrm ""(str"case analysis on a private inductive type")
      
(**********************************************************************)
(* Building case analysis schemes *)
(* Christine Paulin, 1996 *)

let mis_make_case_com dep env sigma (ind, u as pind) (mib,mip as specif) kind =
  let lnamespar = Vars.subst_instance_context u mib.mind_params_ctxt in
  let indf = make_ind_family(pind, Termops.extended_rel_list 0 lnamespar) in
  let constrs = get_constructors env indf in
  let projs = get_projections env indf in

  let () = if Option.is_empty projs then check_privacy_block mib in
  let () = 
    if not (Sorts.List.mem kind (elim_sorts specif)) then
      raise
	(RecursionSchemeError
	   (NotAllowedCaseAnalysis (false, fst (Universes.fresh_sort_in_family env kind), pind)))
  in
  let ndepar = mip.mind_nrealdecls + 1 in

  (* Pas génant car env ne sert pas à typer mais juste à renommer les Anonym *)
  (* mais pas très joli ... (mais manque get_sort_of à ce niveau) *)
  let env' = push_rel_context lnamespar env in


  let rec add_branch env k =
    if Int.equal k (Array.length mip.mind_consnames) then
      let nbprod = k+1 in

      let indf' = lift_inductive_family nbprod indf in
      let arsign,_ = get_arity env indf' in
      let depind = build_dependent_inductive env indf' in
      let deparsign = (Anonymous,None,depind)::arsign in

      let ci = make_case_info env (fst pind) RegularStyle in
      let pbody =
        appvect
          (mkRel (ndepar + nbprod),
           if dep then Termops.extended_rel_vect 0 deparsign
           else Termops.extended_rel_vect 1 arsign) in
      let p =
	it_mkLambda_or_LetIn_name env'
	  ((if dep then mkLambda_name env' else mkLambda)
	   (Anonymous,depind,pbody))
          arsign
      in
      let obj = 
	match projs with
	| None -> mkCase (ci, lift ndepar p,  mkRel 1,
			  Termops.rel_vect ndepar k)
	| Some ps -> 
	  let term = 
	    mkApp (mkRel 2, 
		   Array.map 
		   (fun p -> mkProj (Projection.make p true, mkRel 1)) ps) in
	    if dep then
	      let ty = mkApp (mkRel 3, [| mkRel 1 |]) in 
		mkCast (term, DEFAULTcast, ty)
	    else term
      in
	it_mkLambda_or_LetIn_name env' obj deparsign
    else
      let cs = lift_constructor (k+1) constrs.(k) in
      let t = build_branch_type env dep (mkRel (k+1)) cs in
      mkLambda_string "f" t
	(add_branch (push_rel (Anonymous, None, t) env) (k+1))
  in
  let sigma, s = Evd.fresh_sort_in_family ~rigid:Evd.univ_flexible_alg env sigma kind in
  let typP = make_arity env' dep indf s in
  let c = 
    it_mkLambda_or_LetIn_name env
    (mkLambda_string "P" typP
     (add_branch (push_rel (Anonymous,None,typP) env') 0)) lnamespar
  in sigma, c

(* check if the type depends recursively on one of the inductive scheme *)

(**********************************************************************)
(* Building the recursive elimination *)
(* Christine Paulin, 1996 *)

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
	    let realargs = List.skipn nparams largs in
	    let base = applist (lift i pk,realargs) in
            if depK then
	      Reduction.beta_appvect
                base [|applist (mkRel (i+1), Termops.extended_rel_list 0 sign)|]
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
	            | Mrec (_,j) when is_rec -> (depPvect.(j),rest)
	            | Imbr _  ->
		        msg_warning (strbrk "Ignoring recursive call");
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
                 let env' = push_rel (n,None,t) env in
		 let t_0 = process_pos env' dep' nP (lift 1 t) in
		 make_prod_dep (dep || dep') env
                   (n,t,
		    mkArrow t_0
		      (process_constr
			(push_rel (Anonymous,None,t_0) env')
			 (i+2) (lift 1 c_0) rest (nhyps-1) (i::li))))
      | LetIn (n,b,t,c_0) ->
	  mkLetIn (n,b,t,
		   process_constr
		     (push_rel (n,Some b,t) env)
		     (i+1) c_0 recargs (nhyps-1) li)
      | _ -> assert false
    else
      if dep then
	let realargs = List.rev_map (fun k -> mkRel (i-k)) li in
        let params = List.map (lift i) vargs in
        let co = applist (mkConstructU cs.cs_cstr,params@realargs) in
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

let make_rec_branch_arg env sigma (nparrec,fvect,decF) f cstr recargs =
  let process_pos env fk  =
    let rec prec env i hyps p =
      let p',largs = whd_betadeltaiota_nolet_stack env sigma p in
      match kind_of_term p' with
	| Prod (n,t,c) ->
	    let d = (n,None,t) in
	    mkLambda_name env (n,t,prec (push_rel d env) (i+1) (d::hyps) c)
	| LetIn (n,b,t,c) ->
	    let d = (n,Some b,t) in
	    mkLetIn (n,b,t,prec (push_rel d env) (i+1) (d::hyps) c)
     	| Ind _ ->
            let realargs = List.skipn nparrec largs
            and arg = appvect (mkRel (i+1), Termops.extended_rel_vect 0 hyps) in
            applist(lift i fk,realargs@[arg])
     	| _ -> assert false
    in
    prec env 0 []
  in
  (* ici, cstrprods est la liste des produits du constructeur instantié *)
  let rec process_constr env i f = function
    | (n,None,t as d)::cprest, recarg::rest ->
        let optionpos =
	  match dest_recarg recarg with
            | Norec   -> None
            | Imbr _  -> None
            | Mrec (_,i)  -> fvect.(i)
	in
        (match optionpos with
           | None ->
	       mkLambda_name env
		 (n,t,process_constr (push_rel d env) (i+1)
		    (whd_beta Evd.empty (applist (lift 1 f, [(mkRel 1)])))
		    (cprest,rest))
           | Some(_,f_0) ->
	       let nF = lift (i+1+decF) f_0 in
               let env' = push_rel d env in
	       let arg = process_pos env' nF (lift 1 t) in
               mkLambda_name env
		 (n,t,process_constr env' (i+1)
		    (whd_beta Evd.empty (applist (lift 1 f, [(mkRel 1); arg])))
		    (cprest,rest)))
    | (n,Some c,t as d)::cprest, rest ->
	mkLetIn
	  (n,c,t,
	   process_constr (push_rel d env) (i+1) (lift 1 f)
	     (cprest,rest))
    | [],[] -> f
    | _,[] | [],_ -> anomaly (Pp.str "process_constr")

  in
  process_constr env 0 f (List.rev cstr.cs_args, recargs)


(* Cut a context ctx in 2 parts (ctx1,ctx2) with ctx1 containing k
   variables *)
let context_chop k ctx =
  let rec chop_aux acc = function
    | (0, l2) -> (List.rev acc, l2)
    | (n, ((_,Some _,_ as h)::t)) -> chop_aux (h::acc) (n, t)
    | (n, (h::t)) -> chop_aux (h::acc) (pred n, t)
    | (_, []) -> failwith "context_chop"
  in chop_aux [] (k,ctx)

(* Main function *)
let mis_make_indrec env sigma listdepkind mib u =
  let nparams = mib.mind_nparams in
  let nparrec = mib.mind_nparams_rec in
  let evdref = ref sigma in
  let lnonparrec,lnamesparrec =
    context_chop (nparams-nparrec) (Vars.subst_instance_context u mib.mind_params_ctxt) in
  let nrec = List.length listdepkind in
  let depPvec =
    Array.make mib.mind_ntypes (None : (bool * constr) option) in
  let _ =
    let rec
	assign k = function
	  | [] -> ()
          | ((indi,u),mibi,mipi,dep,_)::rest ->
              (Array.set depPvec (snd indi) (Some(dep,mkRel k));
               assign (k-1) rest)
    in
      assign nrec listdepkind in
  let recargsvec =
    Array.map (fun mip -> mip.mind_recargs) mib.mind_packets in
  (* recarg information for non recursive parameters *)
  let rec recargparn l n =
    if Int.equal n 0 then l else recargparn (mk_norec::l) (n-1) in
  let recargpar = recargparn [] (nparams-nparrec) in
  let make_one_rec p =
    let makefix nbconstruct =
      let rec mrec i ln ltyp ldef = function
	| ((indi,u),mibi,mipi,dep,_)::rest ->
	    let tyi = snd indi in
	    let nctyi =
              Array.length mipi.mind_consnames in (* nb constructeurs du type*)

            (* arity in the context of the fixpoint, i.e.
               P1..P_nrec f1..f_nbconstruct *)
	    let args = Termops.extended_rel_list (nrec+nbconstruct) lnamesparrec in
	    let indf = make_ind_family((indi,u),args) in

	    let arsign,_ = get_arity env indf in
	    let depind = build_dependent_inductive env indf in
	    let deparsign = (Anonymous,None,depind)::arsign in

	    let nonrecpar = rel_context_length lnonparrec in
	    let larsign = rel_context_length deparsign in
	    let ndepar = larsign - nonrecpar in
	    let dect = larsign+nrec+nbconstruct in

            (* constructors in context of the Cases expr, i.e.
               P1..P_nrec f1..f_nbconstruct F_1..F_nrec a_1..a_nar x:I *)
	    let args' = Termops.extended_rel_list (dect+nrec) lnamesparrec in
	    let args'' = Termops.extended_rel_list ndepar lnonparrec in
            let indf' = make_ind_family((indi,u),args'@args'') in

	    let branches =
	      let constrs = get_constructors env indf' in
	      let fi = Termops.rel_vect (dect-i-nctyi) nctyi in
	      let vecfi = Array.map
		(fun f -> appvect (f, Termops.extended_rel_vect ndepar lnonparrec))
		fi
	      in
		Array.map3
		  (make_rec_branch_arg env !evdref
		      (nparrec,depPvec,larsign))
                  vecfi constrs (dest_subterms recargsvec.(tyi))
	    in

	    let j = (match depPvec.(tyi) with
	      | Some (_,c) when isRel c -> destRel c
	      | _ -> assert false)
	    in

	    (* Predicate in the context of the case *)

	    let depind' = build_dependent_inductive env indf' in
	    let arsign',_ = get_arity env indf' in
	    let deparsign' = (Anonymous,None,depind')::arsign' in

	    let pargs =
	      let nrpar = Termops.extended_rel_list (2*ndepar) lnonparrec
	      and nrar = if dep then Termops.extended_rel_list 0 deparsign'
		else Termops.extended_rel_list 1 arsign'
	      in nrpar@nrar

	    in

	    (* body of i-th component of the mutual fixpoint *)
	    let deftyi =
	      let ci = make_case_info env indi RegularStyle in
	      let concl = applist (mkRel (dect+j+ndepar),pargs) in
	      let pred =
		it_mkLambda_or_LetIn_name env
		  ((if dep then mkLambda_name env else mkLambda)
		      (Anonymous,depind',concl))
		  arsign'
	      in
	      let obj = 
		let projs = get_projections env indf in
		  match projs with
		  | None -> (mkCase (ci, pred,
				     mkRel 1,
				     branches))
		  | Some ps -> 
		    let branch = branches.(0) in
		    let ctx, br = decompose_lam_assum branch in
		    let n, subst = 
		      List.fold_right (fun (na,b,t) (i, subst) ->
			if b == None then 
			  let t = mkProj (Projection.make ps.(i) true, mkRel 1) in
			    (i + 1, t :: subst)
			else (i, mkRel 0 :: subst))
			ctx (0, [])
		    in
		    let term = substl subst br in
		      term
	      in
		it_mkLambda_or_LetIn_name env obj
		  (Termops.lift_rel_context nrec deparsign)
	    in

	    (* type of i-th component of the mutual fixpoint *)

	    let typtyi =
	      let concl =
		let pargs = if dep then Termops.extended_rel_vect 0 deparsign
		  else Termops.extended_rel_vect 1 arsign
		in appvect (mkRel (nbconstruct+ndepar+nonrecpar+j),pargs)
	      in it_mkProd_or_LetIn_name env
		concl
		deparsign
	    in
	      mrec (i+nctyi) (rel_context_nhyps arsign ::ln) (typtyi::ltyp)
                (deftyi::ldef) rest
        | [] ->
	    let fixn = Array.of_list (List.rev ln) in
            let fixtyi = Array.of_list (List.rev ltyp) in
            let fixdef = Array.of_list (List.rev ldef) in
            let names = Array.make nrec (Name(Id.of_string "F")) in
	      mkFix ((fixn,p),(names,fixtyi,fixdef))
      in
	mrec 0 [] [] []
    in
    let rec make_branch env i = function
      | ((indi,u),mibi,mipi,dep,_)::rest ->
          let tyi = snd indi in
	  let nconstr = Array.length mipi.mind_consnames in
	  let rec onerec env j =
	    if Int.equal j nconstr then
	      make_branch env (i+j) rest
	    else
	      let recarg = (dest_subterms recargsvec.(tyi)).(j) in
	      let recarg = recargpar@recarg in
	      let vargs = Termops.extended_rel_list (nrec+i+j) lnamesparrec in
	      let cs = get_constructor ((indi,u),mibi,mipi,vargs) (j+1) in
	      let p_0 =
		type_rec_branch
                  true dep env !evdref (vargs,depPvec,i+j) tyi cs recarg
	      in
		mkLambda_string "f" p_0
		  (onerec (push_rel (Anonymous,None,p_0) env) (j+1))
	  in onerec env 0
      | [] ->
	  makefix i listdepkind
    in
    let rec put_arity env i = function
      | ((indi,u),_,_,dep,kinds)::rest ->
	  let indf = make_ind_family ((indi,u), Termops.extended_rel_list i lnamesparrec) in
	  let s = 
	    Evarutil.evd_comb1 (Evd.fresh_sort_in_family ~rigid:Evd.univ_flexible_alg env) 
	      evdref kinds 
	  in
	  let typP = make_arity env dep indf s in
	    mkLambda_string "P" typP
	      (put_arity (push_rel (Anonymous,None,typP) env) (i+1) rest)
      | [] ->
	  make_branch env 0 listdepkind
    in

    (* Body on make_one_rec *)
    let ((indi,u),mibi,mipi,dep,kind) = List.nth listdepkind p in

      if (mis_is_recursive_subset
	(List.map (fun ((indi,u),_,_,_,_) -> snd indi) listdepkind)
	mipi.mind_recargs)
      then
	let env' = push_rel_context lnamesparrec env in
	  it_mkLambda_or_LetIn_name env (put_arity env' 0 listdepkind)
	    lnamesparrec
      else
	let evd', c = mis_make_case_com dep env !evdref (indi,u) (mibi,mipi) kind in
	  evdref := evd'; c
  in
    (* Body of mis_make_indrec *)
    !evdref, List.init nrec make_one_rec

(**********************************************************************)
(* This builds elimination predicate for Case tactic *)

let build_case_analysis_scheme env sigma pity dep kind =
  let (mib,mip) = lookup_mind_specif env (fst pity) in
  mis_make_case_com dep env sigma pity (mib,mip) kind

let is_in_prop mip =
  match inductive_sort_family mip with
  | InProp -> true
  | _ -> false

let build_case_analysis_scheme_default env sigma pity kind =
  let (mib,mip) = lookup_mind_specif env (fst pity) in
  let dep = not (is_in_prop mip) in
  mis_make_case_com dep env sigma pity (mib,mip) kind

(**********************************************************************)
(* [modify_sort_scheme s rec] replaces the sort of the scheme
   [rec] by [s] *)

let change_sort_arity sort =
  let rec drec a = match kind_of_term a with
    | Cast (c,_,_) -> drec c
    | Prod (n,t,c) -> let s, c' = drec c in s, mkProd (n, t, c')
    | LetIn (n,b,t,c) -> let s, c' = drec c in s, mkLetIn (n,b,t,c')
    | Sort s -> s, mkSort sort
    | _ -> assert false
  in
    drec

(* Change the sort in the type of an inductive definition, builds the
   corresponding eta-expanded term *)
let weaken_sort_scheme env evd set sort npars term ty =
  let evdref = ref evd in
  let rec drec np elim =
    match kind_of_term elim with
      | Prod (n,t,c) ->
	  if Int.equal np 0 then
            let osort, t' = change_sort_arity sort t in
	      evdref := (if set then Evd.set_eq_sort else Evd.set_leq_sort) env !evdref sort osort;
              mkProd (n, t', c),
              mkLambda (n, t', mkApp(term,Termops.rel_vect 0 (npars+1)))
	  else
            let c',term' = drec (np-1) c in
	    mkProd (n, t, c'), mkLambda (n, t, term')
      | LetIn (n,b,t,c) -> let c',term' = drec np c in
           mkLetIn (n,b,t,c'), mkLetIn (n,b,t,term')
      | _ -> anomaly ~label:"weaken_sort_scheme" (Pp.str "wrong elimination type")
  in
  let ty, term = drec npars ty in
    !evdref, ty, term

(**********************************************************************)
(* Interface to build complex Scheme *)
(* Check inductive types only occurs once
(otherwise we obtain a meaning less scheme) *)

let check_arities env listdepkind =
  let _ = List.fold_left
    (fun ln (((_,ni as mind),u),mibi,mipi,dep,kind) ->
       let kelim = elim_sorts (mibi,mipi) in
       if not (Sorts.List.mem kind kelim) then raise
	 (RecursionSchemeError
	  (NotAllowedCaseAnalysis (true, fst (Universes.fresh_sort_in_family env
					      kind),(mind,u))))
       else if Int.List.mem ni ln then raise
	 (RecursionSchemeError (NotMutualInScheme (mind,mind)))
       else ni::ln)
	    [] listdepkind
  in true

let build_mutual_induction_scheme env sigma = function
  | ((mind,u),dep,s)::lrecspec ->
      let (mib,mip) = lookup_mind_specif env mind in
      let (sp,tyi) = mind in
      let listdepkind =
	((mind,u),mib,mip,dep,s)::
    	(List.map
	   (function ((mind',u'),dep',s') ->
	      let (sp',_) = mind' in
	      if eq_mind sp sp' then
                let (mibi',mipi') = lookup_mind_specif env mind' in
		((mind',u'),mibi',mipi',dep',s')
	      else
		raise (RecursionSchemeError (NotMutualInScheme (mind,mind'))))
	   lrecspec)
      in
      let _ = check_arities env listdepkind in
      mis_make_indrec env sigma listdepkind mib u
  | _ -> anomaly (Pp.str "build_induction_scheme expects a non empty list of inductive types")

let build_induction_scheme env sigma pind dep kind =
  let (mib,mip) = lookup_mind_specif env (fst pind) in
  let sigma, l = mis_make_indrec env sigma [(pind,mib,mip,dep,kind)] mib (snd pind) in
    sigma, List.hd l

(*s Eliminations. *)

let elimination_suffix = function
  | InProp -> "_ind"
  | InSet  -> "_rec"
  | InType -> "_rect"

let case_suffix = "_case"

let make_elimination_ident id s = add_suffix id (elimination_suffix s)

(* Look up function for the default elimination constant *)

let lookup_eliminator ind_sp s =
  let kn,i = ind_sp in
  let mp,dp,l = repr_mind kn in
  let ind_id = (Global.lookup_mind kn).mind_packets.(i).mind_typename in
  let id = add_suffix ind_id (elimination_suffix s) in
  (* Try first to get an eliminator defined in the same section as the *)
  (* inductive type *)
  try
    let cst =Global.constant_of_delta_kn (make_kn mp dp (Label.of_id id)) in
    let _ = Global.lookup_constant cst in
      ConstRef cst
  with Not_found ->
  (* Then try to get a user-defined eliminator in some other places *)
  (* using short name (e.g. for "eq_rec") *)
  try Nametab.locate (qualid_of_ident id)
  with Not_found ->
    errorlabstrm "default_elim"
      (strbrk "Cannot find the elimination combinator " ++
       pr_id id ++ strbrk ", the elimination of the inductive definition " ++
       pr_global_env Id.Set.empty (IndRef ind_sp) ++
       strbrk " on sort " ++ Termops.pr_sort_family s ++
       strbrk " is probably not allowed.")
