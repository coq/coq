
(* $Id$ *)

open Pp
open Util
open Names
open Generic
open Sign
open Evd
open Term
open Reduction
open Environ
open Type_errors
open Typeops
open Classops
open List
open Recordops 
open Evarutil
open Pretype_errors
open Rawterm
open Evarconv
open Coercion


(***********************************************************************)
(* This concerns Cases *)
open Inductive
open Instantiate

(* Pour le vieux "match" que Program utilise encore, vieille histoire ... *)

(* Awful special reduction function which skips abstraction on Xtra in
   order to be safe for Program ... *)

let stacklamxtra recfun = 
  let rec lamrec sigma p_0 p_1 = match p_0,p_1 with 
    | (stack, (DOP2(Lambda,DOP1(XTRA "COMMENT",_),DLAM(_,c)) as t)) ->
        recfun stack (substl sigma t)
    | ((h::t), (DOP2(Lambda,_,DLAM(_,c)))) -> lamrec (h::sigma) t c
    | (stack, t) -> recfun stack (substl sigma t)
  in 
  lamrec 

let rec whrec x stack =
  match x with   
    | DOP2(Lambda,DOP1(XTRA "COMMENT",c),DLAM(name,t)) ->
    	let t' = applist (whrec t (List.map (lift 1) stack)) in 
	DOP2(Lambda,DOP1(XTRA "COMMENT",c),DLAM(name,t')),[]
    | DOP2(Lambda,c1,DLAM(name,c2)) ->
    	(match stack with
	   | [] -> (DOP2(Lambda,c1,DLAM(name,whd_betaxtra c2)),[])
	   | a1::rest -> stacklamxtra (fun l x -> whrec x l) [a1] rest c2)
    | DOPN(AppL,cl) -> whrec (array_hd cl) (array_app_tl cl stack)
    | DOP2(Cast,c,_) ->  whrec c stack
    | x -> x,stack

and whd_betaxtra x = applist(whrec x [])

let lift_context n l = 
  let k = List.length l in 
  list_map_i (fun i (name,c) -> (name,liftn n (k-i) c)) 0 l

let transform_rec loc env sigma (p,c,lf) (indt,pt) = 
  let (indf,realargs) = dest_ind_type indt in
  let (mispec,params) = dest_ind_family indf in
  let mI = mkMutInd (mis_inductive mispec) in
  let recargs = mis_recarg mispec in
  let tyi = mis_index mispec in
  if Array.length lf <> mis_nconstr mispec then 
    error_number_branches_loc loc CCI env c
      (mkAppliedInd indt) (mis_nconstr mispec);
  if mis_is_recursive_subset [tyi] mispec then
    let dep = find_case_dep_nparams env sigma (c,p) indf pt in 
    let init_depFvec i = if i = tyi then Some(dep,Rel 1) else None in
    let depFvec = Array.init (mis_ntypes mispec) init_depFvec in
    let constrs = get_constructors indf in
    (* build now the fixpoint *)
    let lnames,_ = get_arity indf in
    let nar = List.length lnames in
    let nparams = mis_nparams mispec in
    let ci = make_default_case_info mispec in
    let branches = 
      array_map3
	(fun f t reca -> 
	   whd_betaxtra
             (Indrec.make_rec_branch_arg env sigma
                (nparams,depFvec,nar+1)
                f t reca))
        (Array.map (lift (nar+2)) lf) constrs recargs 
    in 
    let deffix = 
      it_lambda_name env
	(lambda_create env
	   (applist (mI,List.append (List.map (lift (nar+1)) params)
                       (rel_list 0 nar)),
            mkMutCaseA ci (lift (nar+2) p) (Rel 1) branches))
        (lift_context 1 lnames) 
    in
    if noccurn 1 deffix then 
      whd_beta (applist (pop deffix,realargs@[c]))
    else
      let typPfix = 
	it_prod_name env
	  (prod_create env
	     (applist (mI,(List.append 
			     (List.map (lift nar) params)
			     (rel_list 0 nar))),
	      (if dep then 
		 applist (whd_beta_stack (lift (nar+1) p) (rel_list 0 (nar+1)))
	       else 
		 applist (whd_beta_stack (lift (nar+1) p) (rel_list 1 nar)))))
          lnames 
      in
      let fix = DOPN(Fix([|nar|],0),
		     [|typPfix;
		       DLAMV(Name(id_of_string "F"),[|deffix|])|])
      in 
      applist (fix,realargs@[c])
  else
    let ci = make_default_case_info mispec in
    mkMutCaseA ci p c lf

(***********************************************************************)

(*
let ctxt_of_ids ids =
  Array.map
    (function
       | RRef (_,RVar id) -> VAR id
       | _ -> error "pretyping: arbitrary subst of ref not implemented")
    ids
*)
let ctxt_of_ids cl = cl

let mt_evd = Evd.empty

let vect_lift_type = Array.mapi (fun i t -> typed_app (lift i) t)

let j_nf_ise sigma {uj_val=v;uj_type=t} =
  {uj_val=nf_ise1 sigma v;uj_type=typed_app (nf_ise1 sigma) t}

let jv_nf_ise sigma = Array.map (j_nf_ise sigma)

(* Utilisé pour inférer le prédicat des Cases *)
(* Semble exagérement fort *)
(* Faudra préférer une unification entre les types de toutes les clauses *)
(* et autoriser des ? à rester dans le résultat de l'unification *)

let evar_type_fixpoint env isevars lna lar vdefj =
  let lt = Array.length vdefj in 
    if Array.length lar = lt then 
      for i = 0 to lt-1 do 
        if not (the_conv_x_leq env isevars
		  (body_of_type (vdefj.(i)).uj_type)
		  (lift lt (body_of_type lar.(i)))) then
          error_ill_typed_rec_body CCI env i lna 
	    (jv_nf_ise !isevars vdefj) 
	    (Array.map (typed_app (nf_ise1 !isevars)) lar)
      done


(* Inutile ?
let cast_rel isevars env cj tj =
    if the_conv_x_leq isevars env cj.uj_type tj.uj_val then
        {uj_val=j_val_only cj;
         uj_type=tj.uj_val;
         uj_kind = hnf_constr !isevars tj.uj_type}
   else error_actual_type CCI env (j_nf_ise !isevars cj) (j_nf_ise !isevars tj)

*)
let let_path = make_path ["Core"] (id_of_string "let") CCI

let wrong_number_of_cases_message loc env isevars (c,ct) expn = 
  let c = nf_ise1 !isevars c and ct = nf_ise1 !isevars ct in
  error_number_branches_loc loc CCI env c ct expn

let check_branches_message loc env isevars c (explft,lft) = 
  for i = 0 to Array.length explft - 1 do
    if not (the_conv_x_leq env isevars lft.(i) explft.(i)) then 
      let c = nf_ise1 !isevars c
      and lfi = nf_betaiota env !isevars (nf_ise1 !isevars lft.(i)) in
      error_ill_formed_branch_loc loc CCI env c i lfi 
	(nf_betaiota env !isevars explft.(i))
  done

(*
let evar_type_case isevars env ct pt lft p c =
  let (mind,bty,rslty) = type_case_branches env !isevars ct pt p c
  in check_branches_message isevars env (c,ct) (bty,lft); (mind,rslty)
*)

let pretype_var loc env lvar id = 
  try
    List.assoc id lvar
  with
    Not_found ->
      (try
         match lookup_id id (context env) with
           | RELNAME (n,typ) ->
	     { uj_val  = Rel n;
	       uj_type = typed_app (lift n) typ }
           | GLOBNAME (id,typ) ->
	     { uj_val  = VAR id;
	       uj_type = typ }
      with Not_found ->
        error_var_not_found_loc loc CCI id);;

(*************************************************************************)
(* Main pretyping function                                               *)

let trad_metamap = ref []
let trad_nocheck = ref false

let pretype_ref pretype loc isevars env lvar = function
| RVar id -> pretype_var loc env lvar id

| RConst (sp,ctxt) ->
    let cst = (sp,Array.map pretype ctxt) in
    make_judge (mkConst cst) (type_of_constant env !isevars cst)

| RAbst sp -> failwith "Pretype: abst doit disparaître"
(*
  if sp = let_path then
      (match Array.to_list cl with
       [m;DLAM(na,b)] ->
       let mj = pretype empty_tycon isevars env m in
	 (try 
	    let mj = inh_ass_of_j isevars env mj in
	    let mb = body_of_type mj in
	    let bj =
	     pretype empty_tycon (push_rel (na,mj) env) isevars b in
	   {uj_val = DOPN(Abst sp,[|mb;DLAM(na,bj.uj_val)|]);
            uj_type = sAPP (DLAM(na,bj.uj_type)) mb;
            uj_kind = pop bj.uj_kind }
	 with UserError _ -> 
	   pretype vtcon isevars env (abst_value cstr)) 
      | _ -> errorlabstrm "Trad.constr_of_com" [< 'sTR"Malformed ``let''" >])
   else if evaluable_abst cstr then
     pretype vtcon isevars env (abst_value cstr)
   else error "Cannot typecheck an unevaluable abstraction"
*)
| REVar (sp,ctxt) -> error " Not able to type terms with dependent subgoals"
(* Not able to type goal existential yet
    let cstr = mkConst (sp,ctxt_of_ids ids) in
    make_judge cstr (type_of_existential env !isevars cstr)
*)
| RInd (ind_sp,ctxt) ->
    let ind = (ind_sp,Array.map pretype ctxt) in
    make_judge (mkMutInd ind) (type_of_inductive env !isevars ind)
 
| RConstruct (cstr_sp,ctxt) ->
    let cstr = (cstr_sp,Array.map pretype ctxt) in
    let typ = type_of_constructor env !isevars cstr in
    { uj_val=mkMutConstruct cstr; uj_type=typ }

let pretype_sort = function
  | RProp c -> judge_of_prop_contents c
  | RType ->
      { uj_val = dummy_sort;
	uj_type = make_typed dummy_sort (Type Univ.dummy_univ) }

(* pretype tycon isevars env constr tries to solve the *)
(* existential variables in constr in environment env with the *)
(* constraint tycon (see Tradevar). *)
(* Invariant : Prod and Lambda types are casted !! *)
let rec pretype tycon env isevars lvar lmeta cstr =
match cstr with   (* Où teste-t-on que le résultat doit satisfaire tycon ? *)

| RRef (loc,ref) -> 
    pretype_ref
      (fun c -> (pretype empty_tycon env isevars lvar lmeta c).uj_val)
      loc isevars env lvar ref

| RMeta (loc,n) ->
    (try
       List.assoc n lmeta
     with
        Not_found ->
          let metaty =
            try List.assoc n !trad_metamap
            with Not_found ->
	    (* Tester si la référence est castée *)
	      user_err_loc (loc,"pretype",
	        [< 'sTR "Metavariable "; 'iNT n; 'sTR" is unbound" >])
	  in
          { uj_val=DOP0 (Meta n); uj_type = outcast_type metaty })

| RHole loc ->
  if !compter then nbimpl:=!nbimpl+1;
  (match tycon with
  | Some ty ->
      let c = new_isevar isevars env ty CCI in
      {uj_val=c;uj_type=make_typed ty (Type Univ.dummy_univ)}
  | None ->
      (match loc with
	   None -> anomaly "There is an implicit argument I cannot solve"
	 | Some loc -> 
	     user_err_loc
	       (loc,"pretype",
		[< 'sTR "Cannot infer a term for this placeholder" >])))

| RRec (loc,fixkind,lfi,lar,vdef) ->
  let larj = Array.map (pretype_type empty_valcon env isevars lvar lmeta) lar in
  let lara = Array.map (assumption_of_judgment env !isevars) larj in
  let nbfix = Array.length lfi in
  let lfi = List.map (fun id -> Name id) (Array.to_list lfi) in
  let newenv =
    array_fold_left2 (fun env id ar -> (push_rel (id,ar) env))
      env (Array.of_list (List.rev lfi)) (vect_lift_type lara) in
  let vdefj =
    Array.mapi 
      (fun i def -> (* we lift nbfix times the type in tycon, because of
                     * the nbfix variables pushed to newenv *)
        pretype (mk_tycon (lift nbfix (larj.(i).uj_val))) newenv isevars lvar
          lmeta def) vdef in
  (evar_type_fixpoint env isevars lfi lara vdefj;
   let larav = Array.map body_of_type lara in
   match fixkind with
     | RFix (vn,i as vni) ->
	 let fix = (vni,(larav,List.rev lfi,Array.map j_val_only vdefj)) in
	 check_fix env !isevars fix;
	 make_judge (mkFix fix) lara.(i)
     | RCofix i -> 
	 let cofix = (i,(larav,List.rev lfi,Array.map j_val_only vdefj)) in
	 check_cofix env !isevars cofix;
	 make_judge (mkCoFix cofix) lara.(i))

| RSort (loc,s) -> pretype_sort s

| RApp (loc,f,args) -> 
    let j = pretype empty_tycon env isevars lvar lmeta f in
    let j = inh_app_fun env isevars j in
    let apply_one_arg (tycon,jl) c =
      let (dom,rng) = split_tycon loc env isevars tycon in
      let cj = pretype dom env isevars lvar lmeta c in
      let rng_tycon = option_app (subst1 cj.uj_val) rng in
      (rng_tycon,cj::jl)  in
    let jl = List.rev (snd (List.fold_left apply_one_arg
			      (mk_tycon (body_of_type j.uj_type),[]) args)) in
    inh_apply_rel_list !trad_nocheck loc env isevars jl j tycon

| RBinder(loc,BLambda,name,c1,c2)      ->
    let (dom,rng) = split_tycon loc env isevars tycon in
    let dom_valcon = valcon_of_tycon dom in
    let j = pretype_type dom_valcon env isevars lvar lmeta c1 in
    let assum = assumption_of_type_judgment (inh_ass_of_j env isevars j) in
    let var = (name,assum) in
    let j' = pretype rng (push_rel var env) isevars lvar lmeta c2 
    in 
    fst (abs_rel env !isevars name assum j')

| RBinder(loc,BProd,name,c1,c2)        ->
    let j = pretype empty_tycon env isevars lvar lmeta c1 in
    let assum = inh_ass_of_j env isevars j in
    let var = (name,assumption_of_type_judgment assum) in
    let j' = pretype empty_tycon (push_rel var env) isevars lvar lmeta c2 in
    (try fst (gen_rel env !isevars name assum j')
     with TypeError _ as e -> Stdpp.raise_with_loc loc e)

| ROldCase (loc,isrec,po,c,lf) ->
  let cj = pretype empty_tycon env isevars lvar lmeta c in
  let (IndType (indf,realargs) as indt) = 
    try find_rectype env !isevars (body_of_type cj.uj_type)
    with Induc -> error_case_not_inductive CCI env
	(nf_ise1 !isevars cj.uj_val) (nf_ise1 !isevars (body_of_type cj.uj_type)) in
  let pj = match po with
    | Some p -> pretype empty_tycon env isevars lvar lmeta p
    | None -> 
	try match tycon with
	    Some pred -> 
	      let predj = Retyping.get_judgment_of env !isevars pred in
	      inh_tosort env isevars predj
	  | None -> error "notype"
	with UserError _ -> (* get type information from type of branches *)
	  let expbr = Cases.branch_scheme env isevars isrec indf in
	  let rec findtype i =
	    if i >= Array.length lf
	    then error_cant_find_case_type_loc loc env cj.uj_val
	    else
	      try
		let expti = expbr.(i) in
		let fj =
                  pretype (mk_tycon expti) env isevars lvar lmeta lf.(i) in
		let efjt = nf_ise1 !isevars (body_of_type fj.uj_type) in 
		let pred = 
		  Cases.pred_case_ml_onebranch env !isevars isrec indt
		    (i,fj.uj_val,efjt) in
		if has_ise !isevars pred then findtype (i+1)
		else 
		  let pty = Retyping.get_type_of env !isevars pred in
		  { uj_val=pred; 
		    uj_type = Retyping.get_assumption_of env !isevars pty }
	      with UserError _ -> findtype (i+1) in
	    findtype 0 in

  let evalct = find_rectype env !isevars (body_of_type cj.uj_type) (*Pour normaliser evars*)
  and evalPt = nf_ise1 !isevars (body_of_type pj.uj_type) in

  let (bty,rsty) =
    Indrec.type_rec_branches isrec env !isevars evalct evalPt pj.uj_val cj.uj_val in
  if Array.length bty <> Array.length lf then
    wrong_number_of_cases_message loc env isevars 
      (cj.uj_val,nf_ise1 !isevars (body_of_type cj.uj_type))
      (Array.length bty)
  else
    let lfj =
      array_map2
        (fun tyc f -> pretype (mk_tycon tyc) env isevars lvar lmeta f) bty
          lf in
    let lfv = (Array.map (fun j -> j.uj_val) lfj) in
    let lft = (Array.map (fun j -> body_of_type j.uj_type) lfj) in
    check_branches_message loc env isevars cj.uj_val (bty,lft);
    let v =
      if isrec
      then 
	transform_rec loc env !isevars(pj.uj_val,cj.uj_val,lfv) (evalct,evalPt)
      else
	let mis,_ = dest_ind_family indf in
	let ci = make_default_case_info mis in
	mkMutCaseA ci pj.uj_val cj.uj_val (Array.map (fun j-> j.uj_val) lfj)
    in
    let s = destSort (snd (splay_prod env !isevars evalPt)) in
    {uj_val = v;
     uj_type = make_typed rsty s }

| RCases (loc,prinfo,po,tml,eqns) ->
    Cases.compile_cases loc
      ((fun vtyc env -> pretype vtyc env isevars lvar lmeta),isevars)
      tycon env (* loc *) (po,tml,eqns)

| RCast(loc,c,t) ->
  let tj = pretype_type (valcon_of_tycon tycon) env isevars lvar lmeta t in
  let tj = type_judgment env !isevars tj in
  let cj = pretype (mk_tycon tj.utj_val) env isevars lvar lmeta c in
  inh_conv_coerce_to loc env isevars cj (assumption_of_type_judgment tj)

and pretype_type valcon env isevars lvar lmeta = function
| RHole loc ->
  if !compter then nbimpl:=!nbimpl+1;
    (match valcon with
       | Some v -> Retyping.get_judgment_of env !isevars v
       | None ->
	   let ty = dummy_sort in
	   let c = new_isevar isevars env ty CCI in
	   { uj_val = c ; uj_type = make_typed ty (Type Univ.dummy_univ) })
| c ->
  let j = pretype empty_tycon env isevars lvar lmeta c in
  let tj = inh_tosort env isevars j in
  match valcon with
    | None -> tj
    | Some v ->
	if the_conv_x_leq env isevars v tj.uj_val
	then
	  { uj_val = nf_ise1 !isevars tj.uj_val;
	    uj_type = tj.uj_type }
	else error "This type should be another one !"


let unsafe_fmachine tycon nocheck isevars metamap env lvar lmeta constr =
  trad_metamap := metamap;
  trad_nocheck := nocheck;
  reset_problems ();
  pretype tycon env isevars lvar lmeta constr

let unsafe_fmachine_type valcon nocheck isevars metamap env lvar lmeta constr =
  trad_metamap := metamap;
  trad_nocheck := nocheck;
  reset_problems ();
  pretype_type valcon env isevars lvar lmeta constr

(* [fail_evar] says how to process unresolved evars:
 *   true -> raise an error message
 *   false -> convert them into new Metas (casted with their type)
 *)
let process_evars fail_evar env sigma =
  (if fail_evar then
     try whd_ise env sigma
     with Uninstantiated_evar n ->
          errorlabstrm "whd_ise"
            [< 'sTR"There is an unknown subterm I cannot solve" >]
   else whd_ise1_metas env sigma)


let j_apply f env sigma j =
  let under_outer_cast f env sigma = function
    | DOP2 (Cast,b,t) -> DOP2 (Cast,f env sigma b,f env sigma t)
    | c -> f env sigma c in
  { uj_val=strong (under_outer_cast f) env sigma j.uj_val;
    uj_type= typed_app (strong f env sigma) j.uj_type }

(* TODO: comment faire remonter l'information si le typage a resolu des
       variables du sigma original. il faudrait que la fonction de typage
       retourne aussi le nouveau sigma...
*)

let ise_resolve_casted_gen sigma env lvar lmeta typ c =
  let isevars = ref sigma in
  let j = unsafe_fmachine (mk_tycon typ) false isevars [] env lvar lmeta c in
  (j_apply (fun _ -> process_evars true) env !isevars j).uj_val

let ise_resolve_casted sigma env typ c =
  ise_resolve_casted_gen sigma env [] [] typ c

(* Raw calls to the inference machine of Trad: boolean says if we must fail
   on unresolved evars, or replace them by Metas; the unsafe_judgment list
   allows us to extend env with some bindings *)
let ise_resolve fail_evar sigma metamap env lvar lmeta c =
  let isevars = ref sigma in
  let j = unsafe_fmachine empty_tycon false isevars metamap env lvar lmeta c in
  j_apply (fun _ -> process_evars fail_evar) env !isevars j

let ise_resolve_type fail_evar sigma metamap env c =
  let isevars = ref sigma in
  let j = unsafe_fmachine_type empty_valcon false isevars metamap env [] [] c in
  let tj = assumption_of_type_judgment (inh_ass_of_j env isevars j) in
  typed_app (strong (fun _ -> process_evars fail_evar) env !isevars) tj

let ise_resolve_nocheck sigma metamap env c =
  let isevars = ref sigma in
  let j = unsafe_fmachine empty_tycon true isevars metamap env [] [] c in
  j_apply (fun _ -> process_evars true) env !isevars j

let ise_resolve1 is_ass sigma env c =
  if is_ass then 
    body_of_type (ise_resolve_type true sigma [] env c)
  else 
    (ise_resolve true sigma [] env [] [] c).uj_val

let ise_resolve2 sigma env lmeta lvar c =
  (ise_resolve true sigma [] env lmeta lvar c).uj_val;;

(* Keeping universe constraints *)
(*
let fconstruct_type_with_univ_sp sigma sign sp c =
  with_universes
    (Mach.fexecute_type sigma sign) (sp,initial_universes,c) 


let fconstruct_with_univ_sp sigma sign sp c =
  with_universes
    (Mach.fexecute sigma sign) (sp,initial_universes,c) 


let infconstruct_type_with_univ_sp sigma (sign,fsign) sp c =
  with_universes
    (Mach.infexecute_type sigma (sign,fsign)) (sp,initial_universes,c) 


let infconstruct_with_univ_sp sigma (sign,fsign) sp c =
  with_universes
    (Mach.infexecute sigma (sign,fsign)) (sp,initial_universes,c) 
*)
