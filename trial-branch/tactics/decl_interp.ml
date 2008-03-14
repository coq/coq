(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util
open Names
open Topconstr
open Tacinterp
open Tacmach
open Decl_expr
open Decl_mode
open Pretyping.Default
open Rawterm
open Term
open Pp

(* INTERN *)

let raw_app (loc,hd,args) = if args =[] then hd else RApp(loc,hd,args) 

let intern_justification_items globs = 
  Option.map (List.map (intern_constr globs))

let intern_justification_method globs = 
  Option.map (intern_tactic globs)

let intern_statement intern_it globs st =
  {st_label=st.st_label;
   st_it=intern_it globs st.st_it}
    
let intern_no_bind intern_it globs x =
  globs,intern_it globs x

let intern_constr_or_thesis globs = function
    Thesis n -> Thesis n
  | This c -> This (intern_constr globs c)

let add_var id globs= 
  let l1,l2=globs.ltacvars in
    {globs with ltacvars= (id::l1),(id::l2)}

let add_name nam globs=
 match nam with 
     Anonymous -> globs
   | Name id -> add_var id globs

let intern_hyp iconstr globs = function 
    Hvar (loc,(id,topt)) -> add_var id globs,
      Hvar (loc,(id,Option.map (intern_constr globs) topt))
  | Hprop st -> add_name st.st_label globs,
      Hprop (intern_statement iconstr globs st)

let intern_hyps iconstr globs hyps = 
  snd (list_fold_map (intern_hyp iconstr) globs hyps)

let intern_cut intern_it globs cut=
  let nglobs,nstat=intern_it globs cut.cut_stat in
    {cut_stat=nstat;
     cut_by=intern_justification_items nglobs cut.cut_by;
     cut_using=intern_justification_method nglobs cut.cut_using}

let intern_casee globs = function 
    Real c -> Real (intern_constr globs c)
  | Virtual cut -> Virtual 
      (intern_cut (intern_no_bind (intern_statement intern_constr)) globs cut) 

let intern_hyp_list args globs =
  let intern_one globs (loc,(id,opttyp)) =
    (add_var id globs),
    (loc,(id,Option.map (intern_constr globs) opttyp)) in
  list_fold_map intern_one globs args 

let intern_suffices_clause globs (hyps,c) = 
  let nglobs,nhyps = list_fold_map (intern_hyp intern_constr) globs hyps in
    nglobs,(nhyps,intern_constr_or_thesis nglobs c) 

let intern_fundecl args body globs= 
  let nglobs,nargs = intern_hyp_list args globs in
    nargs,intern_constr nglobs body
          
let rec add_vars_of_simple_pattern globs = function
    CPatAlias (loc,p,id) ->
      add_vars_of_simple_pattern (add_var id globs) p
(*      Stdpp.raise_with_loc loc 
	(UserError ("simple_pattern",str "\"as\" is not allowed here"))*)
  | CPatOr (loc, _)->
      Stdpp.raise_with_loc loc 
	(UserError ("simple_pattern",str "\"(_ | _)\" is not allowed here"))
  | CPatDelimiters (_,_,p) ->
      add_vars_of_simple_pattern globs p
  | CPatCstr (_,_,pl) | CPatNotation(_,_,pl) ->
      List.fold_left add_vars_of_simple_pattern globs pl
  | CPatAtom (_,Some (Libnames.Ident (_,id))) -> add_var id globs
  |  _  -> globs 

let rec intern_bare_proof_instr globs = function
    Pthus i -> Pthus (intern_bare_proof_instr globs i)
  | Pthen i -> Pthen (intern_bare_proof_instr globs i)
  | Phence i -> Phence (intern_bare_proof_instr globs i)
  | Pcut c -> Pcut 
      (intern_cut 
	 (intern_no_bind (intern_statement intern_constr_or_thesis)) globs c)
  | Psuffices c -> 
      Psuffices (intern_cut intern_suffices_clause globs c)
  | Prew (s,c) -> Prew 
      (s,intern_cut 
	 (intern_no_bind  (intern_statement intern_constr)) globs c) 
  | Psuppose hyps -> Psuppose (intern_hyps intern_constr globs hyps)
  | Pcase (params,pat,hyps) -> 
      let nglobs,nparams = intern_hyp_list params globs in
      let nnglobs= add_vars_of_simple_pattern nglobs pat in
      let nhyps = intern_hyps intern_constr_or_thesis nnglobs hyps in
	Pcase (nparams,pat,nhyps) 
  | Ptake witl -> Ptake (List.map (intern_constr globs) witl)
  | Pconsider (c,hyps) -> Pconsider (intern_constr globs c,
				      intern_hyps intern_constr globs hyps)
  | Pper (et,c) -> Pper (et,intern_casee globs c)
  | Pend bt -> Pend bt
  | Pescape -> Pescape
  | Passume hyps -> Passume (intern_hyps intern_constr globs hyps)
  | Pgiven hyps -> Pgiven (intern_hyps intern_constr globs hyps)
  | Plet hyps -> Plet (intern_hyps intern_constr globs hyps)
  | Pclaim st -> Pclaim (intern_statement intern_constr globs st)
  | Pfocus st -> Pfocus (intern_statement intern_constr globs st)
  | Pdefine (id,args,body) -> 
      let nargs,nbody = intern_fundecl args body globs in
	Pdefine (id,nargs,nbody)
  | Pcast (id,typ) ->
      Pcast (id,intern_constr globs typ)

let rec intern_proof_instr globs instr=
  {emph = instr.emph;
   instr = intern_bare_proof_instr globs instr.instr}

(* INTERP *)

let interp_justification_items sigma env =
    Option.map (List.map (fun c ->understand sigma env (fst c)))

let interp_constr check_sort sigma env c = 
  if check_sort then 
    understand_type sigma env (fst c) 
  else 
    understand sigma env (fst c)

let special_whd env =
  let infos=Closure.create_clos_infos Closure.betadeltaiota env in
    (fun t -> Closure.whd_val infos (Closure.inject t))

let _eq = Libnames.constr_of_global (Coqlib.glob_eq)

let decompose_eq env id =
  let typ = Environ.named_type id env in
  let whd = special_whd env typ in
    match kind_of_term whd with
	App (f,args)->
	  if eq_constr f _eq && (Array.length args)=3 
	  then args.(0)
	  else error "previous step is not an equality"
      | _ -> error "previous step is not an equality"

let get_eq_typ info env =
  let typ = decompose_eq env (get_last env) in  
    typ

let interp_constr_in_type typ sigma env c =
  understand sigma env (fst c) ~expected_type:typ

let interp_statement interp_it sigma env st =
  {st_label=st.st_label;
   st_it=interp_it sigma env st.st_it}
	
let interp_constr_or_thesis check_sort sigma env = function
    Thesis n -> Thesis n
  | This c -> This (interp_constr check_sort sigma env c)

let type_tester_var body typ = 
  raw_app(dummy_loc,
       RLambda(dummy_loc,Anonymous,Explicit,typ,
	       RSort (dummy_loc,RProp Null)),body)

let abstract_one_hyp inject h raw = 
  match h with 
      Hvar (loc,(id,None)) ->  
	RProd (dummy_loc,Name id, Explicit, RHole (loc,Evd.BinderType (Name id)), raw)
    | Hvar (loc,(id,Some typ)) ->  
	RProd (dummy_loc,Name id, Explicit, fst typ, raw)
    | Hprop st -> 
	RProd (dummy_loc,st.st_label, Explicit, inject st.st_it, raw)

let rawconstr_of_hyps inject hyps head = 
  List.fold_right (abstract_one_hyp inject) hyps head

let raw_prop = RSort (dummy_loc,RProp Null)
  
let rec match_hyps blend names constr = function 
    [] -> [],substl names constr
  | hyp::q -> 
      let (name,typ,body)=destProd constr in
      let st= {st_label=name;st_it=substl names typ} in
      let qnames=
	match name with
	    Anonymous -> mkMeta 0 :: names
	  | Name id -> mkVar id :: names in
      let qhyp = match hyp with
	  Hprop st' -> Hprop (blend st st')
	| Hvar _ -> Hvar st in
      let rhyps,head = match_hyps blend qnames body q in
	qhyp::rhyps,head

let interp_hyps_gen inject blend sigma env hyps head = 
  let constr=understand sigma env (rawconstr_of_hyps inject hyps head) in
    match_hyps blend [] constr hyps

let interp_hyps sigma env hyps = fst (interp_hyps_gen fst (fun x _ -> x) sigma env hyps raw_prop)

let dummy_prefix= id_of_string "__"

let rec deanonymize ids = 
  function 
      PatVar (loc,Anonymous) -> 
	let (found,known) = !ids in
	let new_id=Nameops.next_ident_away dummy_prefix known in
	let _= ids:= (loc,new_id) :: found , new_id :: known in
	  PatVar (loc,Name new_id)
    | PatVar (loc,Name id) as pat -> 
	let (found,known) = !ids in
	let _= ids:= (loc,id) :: found , known in
	  pat
    | PatCstr(loc,cstr,lpat,nam) -> 
	PatCstr(loc,cstr,List.map (deanonymize ids) lpat,nam)

let rec raw_of_pat =
  function 
      PatVar (loc,Anonymous) -> anomaly "Anonymous pattern variable" 
    | PatVar (loc,Name id) -> 
	  RVar (loc,id)
    | PatCstr(loc,((ind,_) as cstr),lpat,_) -> 
	let mind= fst (Global.lookup_inductive ind) in
	let rec add_params n q =
	  if n<=0 then q else
	    add_params (pred n) (RHole(dummy_loc,
				       Evd.TomatchTypeParameter(ind,n))::q) in
	    let args = List.map raw_of_pat lpat in 
	      raw_app(loc,RRef(dummy_loc,Libnames.ConstructRef cstr),
		   add_params mind.Declarations.mind_nparams args) 
			 
let prod_one_hyp = function
    (loc,(id,None)) ->
      (fun raw ->  
	 RProd (dummy_loc,Name id, Explicit,
		RHole (loc,Evd.BinderType (Name id)), raw))
  | (loc,(id,Some typ)) -> 
      (fun raw ->  
	 RProd (dummy_loc,Name id, Explicit, fst typ, raw))

let prod_one_id (loc,id) raw =
  RProd (dummy_loc,Name id, Explicit,
	 RHole (loc,Evd.BinderType (Name id)), raw)

let let_in_one_alias (id,pat) raw =
  RLetIn (dummy_loc,Name id, raw_of_pat pat, raw)

let rec bind_primary_aliases map pat =
  match pat with 
      PatVar (_,_) -> map
    | PatCstr(loc,_,lpat,nam) ->
	let map1 =
	  match nam with 
	      Anonymous -> map
	    | Name id -> (id,pat)::map 
	in
	  List.fold_left bind_primary_aliases map1 lpat

let bind_secondary_aliases map subst =
  List.fold_left (fun map (ids,idp) -> (ids,List.assoc idp map)::map) map subst

let bind_aliases patvars subst patt =
  let map = bind_primary_aliases [] patt in
  let map1 = bind_secondary_aliases map subst in
  List.rev map1

let interp_pattern env pat_expr = 
  let patvars,pats = Constrintern.intern_pattern env pat_expr in
    match pats with 
	[] -> anomaly "empty pattern list"
      | [subst,patt] ->
	  (patvars,bind_aliases patvars subst patt,patt)
      | _  -> anomaly "undetected disjunctive pattern"

let rec match_args dest names constr = function 
    [] -> [],names,substl names constr
  | _::q -> 
      let (name,typ,body)=dest constr in
      let st={st_label=name;st_it=substl names typ} in
      let qnames=
	match name with
	    Anonymous -> assert  false
	  | Name id -> mkVar id :: names in
      let args,bnames,body = match_args dest qnames body q in
	st::args,bnames,body

let rec match_aliases names constr = function 
    [] -> [],names,substl names constr
  | _::q -> 
      let (name,c,typ,body)=destLetIn constr in
      let st={st_label=name;st_it=(substl names c,substl names typ)} in
      let qnames=
	match name with
	    Anonymous -> assert false
	  | Name id -> mkVar id :: names in
      let args,bnames,body = match_aliases qnames body q in
	st::args,bnames,body

let detype_ground c = Detyping.detype false [] [] c

let interp_cases info sigma env params (pat:cases_pattern_expr) hyps =
  let et,pinfo =
    match info.pm_stack with
	Per(et,pi,_,_)::_ -> et,pi
      | _ -> error "No proof per cases/induction/inversion in progress." in
  let mib,oib=Global.lookup_inductive  pinfo.per_ind in
  let num_params = pinfo.per_nparams in
  let _ = 
    let expected = mib.Declarations.mind_nparams - num_params in
      if List.length params <> expected then
	errorlabstrm "suppose it is" 
	  (str "Wrong number of extra arguments : " ++ 
	     (if expected = 0 then str "none" else int expected) ++ 
	     str "expected") in
  let app_ind =
    let rind = RRef (dummy_loc,Libnames.IndRef pinfo.per_ind) in
    let rparams = List.map detype_ground pinfo.per_params in 
    let rparams_rec = 
      List.map 
	(fun (loc,(id,_)) -> 
	   RVar (loc,id)) params in 
    let dum_args= 
      list_tabulate (fun _ -> RHole (dummy_loc,Evd.QuestionMark false))
	oib.Declarations.mind_nrealargs in
      raw_app(dummy_loc,rind,rparams@rparams_rec@dum_args) in
  let pat_vars,aliases,patt = interp_pattern env pat in
  let inject = function
      Thesis (Plain) -> Rawterm.RSort(dummy_loc,RProp Null)
    | Thesis (For rec_occ) ->
	if not (List.mem rec_occ pat_vars) then 
	  errorlabstrm "suppose it is" 
	    (str "Variable " ++ Nameops.pr_id rec_occ ++ 
	       str " does not occur in pattern.");
	Rawterm.RSort(dummy_loc,RProp Null)
    | This (c,_) -> c in
  let term1 = rawconstr_of_hyps inject hyps raw_prop in
  let loc_ids,npatt =
    let rids=ref ([],pat_vars) in
    let npatt= deanonymize rids patt in 
      List.rev (fst !rids),npatt in
  let term2 =
    RLetIn(dummy_loc,Anonymous,
	   RCast(dummy_loc,raw_of_pat npatt,
		 CastConv (DEFAULTcast,app_ind)),term1) in
  let term3=List.fold_right let_in_one_alias aliases term2 in  
  let term4=List.fold_right prod_one_id loc_ids term3 in
  let term5=List.fold_right prod_one_hyp params term4 in
  let constr = understand  sigma env term5 in
  let tparams,nam4,rest4 = match_args destProd [] constr params in
  let tpatvars,nam3,rest3 = match_args destProd nam4 rest4 loc_ids in
  let taliases,nam2,rest2 = match_aliases nam3 rest3 aliases in
  let (_,pat_pat,pat_typ,rest1) = destLetIn rest2 in
  let blend st st' =
    match st'.st_it with 
	Thesis nam -> {st_it=Thesis nam;st_label=st'.st_label} 
      | This _ -> {st_it = This st.st_it;st_label=st.st_label} in
  let thyps = fst (match_hyps blend nam2 (Termops.pop rest1) hyps) in
    tparams,{pat_vars=tpatvars;
	     pat_aliases=taliases;
	     pat_constr=pat_pat;
	     pat_typ=pat_typ;
	     pat_pat=patt;
	     pat_expr=pat},thyps

let interp_cut interp_it sigma env cut=
  let nenv,nstat = interp_it sigma env cut.cut_stat in
    {cut with 
       cut_stat=nstat;
       cut_by=interp_justification_items sigma nenv cut.cut_by}

let interp_no_bind interp_it sigma env x =
  env,interp_it sigma env x

let interp_suffices_clause sigma env (hyps,cot)=
  let (locvars,_) as res =
    match cot with
	This (c,_) -> 
	  let nhyps,nc = interp_hyps_gen fst (fun x _ -> x) sigma env hyps c in
	  nhyps,This nc
      | Thesis Plain as th  -> interp_hyps sigma env hyps,th
      | Thesis (For n) -> error "\"thesis for\" is not applicable here" in
  let push_one hyp env0 =
    match hyp with
	(Hprop st | Hvar st) ->
	  match st.st_label with
	      Name id -> Environ.push_named (id,None,st.st_it) env0
	    | _ -> env in
  let nenv = List.fold_right push_one locvars env in 
    nenv,res 
	  
let interp_casee sigma env = function 
    Real c -> Real (understand sigma env (fst c))
  | Virtual cut -> Virtual (interp_cut (interp_no_bind (interp_statement (interp_constr true))) sigma env cut) 

let abstract_one_arg = function
    (loc,(id,None)) ->
      (fun raw ->  
	 RLambda (dummy_loc,Name id, Explicit, 
		RHole (loc,Evd.BinderType (Name id)), raw))
  | (loc,(id,Some typ)) -> 
      (fun raw ->  
	 RLambda (dummy_loc,Name id, Explicit, fst typ, raw))

let rawconstr_of_fun args body = 
  List.fold_right abstract_one_arg args (fst body)

let interp_fun sigma env args body = 
  let constr=understand sigma env (rawconstr_of_fun args body) in
    match_args destLambda [] constr args

let rec interp_bare_proof_instr info (sigma:Evd.evar_map) (env:Environ.env) = function
    Pthus i -> Pthus (interp_bare_proof_instr info sigma env i)
  | Pthen i -> Pthen (interp_bare_proof_instr info sigma env i)
  | Phence i -> Phence (interp_bare_proof_instr info sigma env i)
  | Pcut c -> Pcut (interp_cut 
		      (interp_no_bind (interp_statement 
					 (interp_constr_or_thesis true))) 
		      sigma env c) 
  | Psuffices c ->  
      Psuffices (interp_cut interp_suffices_clause sigma env c)
  | Prew (s,c) -> Prew (s,interp_cut 
			  (interp_no_bind (interp_statement 
			     (interp_constr_in_type (get_eq_typ info env))))
			  sigma env c) 

  | Psuppose hyps -> Psuppose (interp_hyps sigma env hyps)
  | Pcase (params,pat,hyps) -> 
      let tparams,tpat,thyps = interp_cases info sigma env params pat hyps in 
	Pcase (tparams,tpat,thyps)
  | Ptake witl -> 
      Ptake (List.map (fun c -> understand sigma env (fst c)) witl)
  | Pconsider (c,hyps) -> Pconsider (interp_constr false sigma env c,
				     interp_hyps sigma env hyps)
  | Pper (et,c) -> Pper (et,interp_casee sigma env c)
  | Pend bt -> Pend bt
  | Pescape -> Pescape
  | Passume hyps -> Passume (interp_hyps sigma env hyps)
  | Pgiven hyps -> Pgiven (interp_hyps sigma env hyps)
  | Plet hyps -> Plet (interp_hyps sigma env hyps)
  | Pclaim st -> Pclaim (interp_statement (interp_constr true) sigma env st)
  | Pfocus st -> Pfocus (interp_statement (interp_constr true) sigma env st)
  | Pdefine (id,args,body) -> 
      let nargs,_,nbody = interp_fun sigma env args body in
	Pdefine (id,nargs,nbody)
  | Pcast (id,typ) -> 
      Pcast(id,interp_constr true sigma env typ)

let rec interp_proof_instr info sigma env instr=
  {emph = instr.emph;
   instr = interp_bare_proof_instr info sigma env instr.instr}
 


