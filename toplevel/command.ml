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
open Options
open Term
open Termops
open Declarations
open Entries
open Inductive
open Environ
open Reduction
open Tacred
open Declare
open Nametab
open Names
open Libnames
open Nameops
open Topconstr
open Library
open Libobject
open Constrintern
open Proof_type
open Tacmach
open Safe_typing
open Nametab
open Typeops
open Indtypes
open Vernacexpr
open Decl_kinds
open Pretyping
open Symbols

let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,a,b))
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,a,b))

let rec abstract_rawconstr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,abstract_rawconstr c bl)
  | LocalRawAssum (idl,t)::bl ->
      List.fold_right (fun x b -> mkLambdaC([x],t,b)) idl
        (abstract_rawconstr c bl)

let rec generalize_rawconstr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,generalize_rawconstr c bl)
  | LocalRawAssum (idl,t)::bl ->
      List.fold_right (fun x b -> mkProdC([x],t,b)) idl
        (generalize_rawconstr c bl)

let rec destSubCast c = match kind_of_term c with
  | Lambda (x,t,c) -> 
      let (b,u) = destSubCast c in mkLambda (x,t,b), mkProd (x,t,u)
  | LetIn (x,b,t,c) ->
      let (d,u) = destSubCast c in mkLetIn (x,b,t,d), mkLetIn (x,b,t,u)
  | Cast (b,u) -> (b,u)
  | _ -> assert false

let rec adjust_conclusion a cs = function
  | CProdN (loc,bl,c) -> CProdN (loc,bl,adjust_conclusion a cs c)
  | CLetIn (loc,b,t,c) -> CLetIn (loc,b,t,adjust_conclusion a cs c)
  | CHole loc ->
      let (nar,name,params) = a in
      if nar <> 0 then
	user_err_loc (loc,"",
	  str "Cannot infer the non constant arguments of the conclusion of "
	  ++ pr_id cs);
      let args = List.map (fun id -> CRef(Ident(loc,id))) params in
      CAppExpl (loc,(None,Ident(loc,name)),List.rev args)
  | c -> c

(* Commands of the interface *)

(* 1| Constant definitions *)

let definition_message id =
  if_verbose message ((string_of_id id) ^ " is defined")

let constant_entry_of_com (bl,com,comtypopt,opacity) =
  let sigma = Evd.empty in
  let env = Global.env() in
  match comtypopt with
      None -> 
	let b = abstract_rawconstr com bl in
	let j = judgment_of_rawconstr sigma env b in
	{ const_entry_body = j.uj_val;
	  const_entry_type = Some (Evarutil.refresh_universes j.uj_type);
          const_entry_opaque = opacity }
    | Some comtyp ->
	(* We use a cast to avoid troubles with evars in comtyp *)
	(* that can only be resolved knowing com *)
	let b = abstract_rawconstr (mkCastC (com,comtyp)) bl in
	let (body,typ) = destSubCast (interp_constr sigma env b) in
	{ const_entry_body = body;
	  const_entry_type = Some typ;
          const_entry_opaque = opacity }

let rec length_of_raw_binders = function
  | [] -> 0
  | LocalRawDef _::bl -> 1 + length_of_raw_binders bl
  | LocalRawAssum (idl,_)::bl -> List.length idl + length_of_raw_binders bl

let rec under_binders env f n c =
  if n = 0 then f env Evd.empty c else
    match kind_of_term c with
      | Lambda (x,t,c) ->
        mkLambda (x,t,under_binders (push_rel (x,None,t) env) f (n-1) c)
      | LetIn (x,b,t,c) ->
        mkLetIn (x,b,t,under_binders (push_rel (x,Some b,t) env) f (n-1) c)
      | _ -> assert false

let red_constant_entry bl ce = function
  | None -> ce
  | Some red ->
      let body = ce.const_entry_body in
      { ce with const_entry_body = 
      under_binders (Global.env()) (reduction_of_redexp red)
        (length_of_raw_binders bl)
        body }

let declare_global_definition ident ce local =
  let (_,kn) = declare_constant ident (DefinitionEntry ce,IsDefinition) in
  if local = Local then
    msg_warning (pr_id ident ++ str" is declared as a global definition");
  definition_message ident;
  ConstRef kn

let declare_definition ident (local,_) bl red_option c typopt hook =
  let ce = constant_entry_of_com (bl,c,typopt,false) in
  let ce' = red_constant_entry bl ce red_option in
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let c =
          SectionLocalDef(ce'.const_entry_body,ce'.const_entry_type,false) in
        let _ = declare_variable ident (Lib.cwd(), c, IsDefinition) in
        definition_message ident;
        if Pfedit.refining () then 
          msgerrnl (str"Warning: Local definition " ++ pr_id ident ++ 
          str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        declare_global_definition ident ce' local in
  hook local r

let syntax_definition ident c local onlyparse =
  let c = snd (interp_aconstr [] [] c) in
  let onlyparse = !Options.v7_only or onlyparse in
  Syntax_def.declare_syntactic_definition local ident onlyparse c

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let assumption_message id =
  if_verbose message ((string_of_id id) ^ " is assumed")

let declare_one_assumption is_coe (local,kind) c (_,ident) =
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let r = 
          declare_variable ident 
            (Lib.cwd(), SectionLocalAssum c, IsAssumption kind) in
        assumption_message ident;
        if is_verbose () & Pfedit.refining () then 
          msgerrnl (str"Warning: Variable " ++ pr_id ident ++ 
          str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        let (_,kn) =
          declare_constant ident (ParameterEntry c, IsAssumption kind) in
        assumption_message ident;
        if local=Local & Options.is_verbose () then
          msg_warning (pr_id ident ++ str" is declared as a parameter" ++
          str" because it is at a global level");
        ConstRef kn in
  if is_coe then Class.try_add_new_coercion r local

let declare_assumption idl is_coe k bl c =
  let c = generalize_rawconstr c bl in
  let c = interp_type Evd.empty (Global.env()) c in
  List.iter (declare_one_assumption is_coe k c) idl

(* 3a| Elimination schemes for mutual inductive definitions *)

open Indrec

let non_type_eliminations = 
  [ (InProp,elimination_suffix InProp);
    (InSet,elimination_suffix InSet) ]

let declare_one_elimination ind =
  let (mib,mip) = Global.lookup_inductive ind in 
  let mindstr = string_of_id mip.mind_typename in
  let declare s c t =
    let id = id_of_string s in
    let kn = Declare.declare_internal_constant id
      (DefinitionEntry
        { const_entry_body = c;
          const_entry_type = t;
          const_entry_opaque = false }, 
       Decl_kinds.IsDefinition) in
    definition_message id;
    kn
  in
  let env = Global.env () in
  let sigma = Evd.empty in
  let elim_scheme = Indrec.build_indrec env sigma ind in
  let npars = mip.mind_nparams in
  let make_elim s = Indrec.instanciate_indrec_scheme s npars elim_scheme in
  let kelim = mip.mind_kelim in
  (* in case the inductive has a type elimination, generates only one
     induction scheme, the other ones share the same code with the
     apropriate type *)
  if List.mem InType kelim then
    let elim = make_elim (new_sort_in_family InType) in
    let cte = declare (mindstr^(Indrec.elimination_suffix InType)) elim None in
    let c = mkConst (snd cte) and t = constant_type (Global.env()) (snd cte) in
    List.iter (fun (sort,suff) -> 
      let (t',c') = 
	Indrec.instanciate_type_indrec_scheme (new_sort_in_family sort)
	  npars c t in
      let _ = declare (mindstr^suff) c' (Some t') in ())
      non_type_eliminations
   else (* Impredicative or logical inductive definition *)
     List.iter
    (fun (sort,suff) -> 
       if List.mem sort kelim then
	 let elim = make_elim (new_sort_in_family sort) in
	 let _ = declare (mindstr^suff) elim None in ())
       non_type_eliminations

let declare_eliminations sp =
  let mib = Global.lookup_mind sp in
  if mib.mind_finite then
    for i = 0 to Array.length mib.mind_packets - 1 do
      declare_one_elimination (sp,i)
    done

(* 3b| Mutual Inductive definitions *)

let minductive_message = function 
  | []  -> error "no inductive definition"
  | [x] -> (pr_id x ++ str " is defined")
  | l   -> hov 0  (prlist_with_sep pr_coma pr_id l ++
		     spc () ++ str "are defined")

let recursive_message v =
  match Array.length v with
    | 0 -> error "no recursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is recursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
		    spc () ++ str "are recursively defined")

let corecursive_message v =
  match Array.length v with
    | 0 -> error "no corecursive definition"
    | 1 -> (Printer.pr_global v.(0) ++ str " is corecursively defined")
    | _ -> hov 0 (prvect_with_sep pr_coma Printer.pr_global v ++
                    spc () ++ str "are corecursively defined")

let interp_mutual lparams lnamearconstrs finite = 
  let allnames = 
    List.fold_left (fun acc (id,_,_,l) -> id::(List.map fst l)@acc)
      [] lnamearconstrs in
  if not (list_distinct allnames) then
    error "Two inductive objects have the same name";
  let nparams = local_binders_length lparams
  and sigma = Evd.empty 
  and env0 = Global.env() in
  let env_params, params =
    List.fold_left
      (fun (env, params) d -> match d with
	| LocalRawAssum ([_,na],(CHole _ as t)) ->
	    let t = interp_binder sigma env na t in
	    let d = (na,None,t) in
	    (push_rel d env, d::params)
	| LocalRawAssum (nal,t) ->
	    let t = interp_type sigma env t in
	    let ctx = list_map_i (fun i (_,na) -> (na,None,lift i t)) 0 nal in
	    let ctx = List.rev ctx in
	    (push_rel_context ctx env, ctx@params)
	| LocalRawDef ((_,na),c) ->
	    let c = judgment_of_rawconstr sigma env c in
	    let d = (na, Some c.uj_val, c.uj_type) in
	    (push_rel d env,d::params))
      (env0,[]) lparams
  in
  (* Builds the params of the inductive entry *)
  let params' =
    List.map (fun (na,b,t) ->
		let id = match na with
		  | Name id -> id
		  | Anonymous -> anomaly "Unnamed inductive variable" in 
		match b with
		  | None -> (id, LocalAssum t)
		  | Some b -> (id, LocalDef b)) params
  in
  let paramassums = 
    List.fold_right (fun d l -> match d with
	(id,LocalAssum _) -> id::l | (_,LocalDef _) -> l) params' [] in
  let indnames =
    List.map (fun (id,_,_,_)-> id) lnamearconstrs @ paramassums in
  let nparamassums = List.length paramassums in
  let (ind_env,ind_impls,arityl) =
    List.fold_left
      (fun (env, ind_impls, arl) (recname, _, arityc, _) ->
         let arity = interp_type sigma env_params arityc in
	 let fullarity = it_mkProd_or_LetIn arity params in
	 let env' = Termops.push_rel_assum (Name recname,fullarity) env in
	 let argsc = compute_arguments_scope fullarity in
	 let ind_impls' = 
	   if Impargs.is_implicit_args() then
	     let impl = Impargs.compute_implicits false env_params fullarity in
	     let paramimpl,_ = list_chop nparamassums impl in
	     let l = List.fold_right
	       (fun imp l -> if Impargs.is_status_implicit imp then
		 Impargs.name_of_implicit imp::l else l) paramimpl [] in
	     (recname,(l,impl,argsc))::ind_impls
	   else
	     (recname,([],[],argsc))::ind_impls in
	 (env', ind_impls', (arity::arl)))
      (env0, [], []) lnamearconstrs
  in
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let lparargs = 
    List.flatten
      (List.map (function (id,LocalAssum _) -> [id] | _ -> []) params') in
  let notations = 
    List.fold_right (fun (_,ntnopt,_,_) l -> option_cons ntnopt l) 
      lnamearconstrs [] in
  let fs = States.freeze() in
  (* Declare the notations for the inductive types pushed in local context*)
  try
  List.iter (fun (df,c,scope) -> (* No scope for tmp notation *)
    Metasyntax.add_notation_interpretation df ind_impls c None) notations;
  let ind_env_params = push_rel_context params ind_env in

  let mispecvec = 
    List.map2
      (fun ar (name,_,_,lname_constr) ->
	 let constrnames, bodies = List.split lname_constr in
         (* Compute the conclusions of constructor types *)
	 (* for inductive given in ML syntax *)
	 let nar = 
	   List.length (fst (Reductionops.splay_arity env_params Evd.empty ar))
	 in
	 let bodies =
	   List.map2 (adjust_conclusion (nar,name,lparargs))
	     constrnames bodies
	 in

         (* Interpret the constructor types *)
         let constrs =
	   List.map 
	     (interp_type_with_implicits sigma ind_env_params
	       (paramassums,ind_impls))
	     bodies
	 in

         (* Build the inductive entry *)
	 { mind_entry_params = params';
	   mind_entry_typename = name;
	   mind_entry_arity = ar;
	   mind_entry_consnames = constrnames;
	   mind_entry_lc = constrs })
      (List.rev arityl) lnamearconstrs
  in
  States.unfreeze fs;
  notations, { mind_entry_finite = finite; mind_entry_inds = mispecvec }
  with e -> States.unfreeze fs; raise e

let declare_mutual_with_eliminations isrecord mie =
  let lrecnames =
    List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_,kn) = declare_mind isrecord mie in
  if_verbose ppnl (minductive_message lrecnames);
  declare_eliminations kn;
  kn

(* Very syntactical equality *)
let eq_la d1 d2 = match d1,d2 with
  | LocalRawAssum (nal,ast), LocalRawAssum (nal',ast') ->
      List.for_all2 (fun (_,na) (_,na') -> na = na') nal nal'
      & (try let _ = Constrextern.check_same_type ast ast' in true with _ -> false)
  | LocalRawDef ((_,id),ast), LocalRawDef ((_,id'),ast') ->
      id=id' & (try let _ = Constrextern.check_same_type ast ast' in true with _ -> false)
  | _ -> false

let extract_coe lc =
  List.fold_right
    (fun (addcoe,((_,(id:identifier)),t)) (l1,l2) ->
      ((if addcoe then id::l1 else l1), (id,t)::l2)) lc ([],[])

let extract_coe_la_lc = function
  | []            -> anomaly "Vernacentries: empty list of inductive types"
  | ((_,id),ntn,la,ar,lc)::rest ->
      let rec check = function 
	| []             -> [],[]
  	| ((_,id),ntn,la',ar,lc)::rest ->
            if (List.length la = List.length la') && 
               (List.for_all2 eq_la la la')
	    then
	      let mcoes, mspec = check rest in
	      let coes, lc' = extract_coe lc in
	      (coes::mcoes,(id,ntn,ar,lc')::mspec)
	    else 
	      error ("Parameters should be syntactically the same "^
		     "for each inductive type")
      in
      let mcoes, mspec = check rest in
      let coes, lc' = extract_coe lc in
      (coes,la,(id,ntn,ar,lc'):: mspec)

let build_mutual lind finite =
  let ((coes:identifier list),lparams,lnamearconstructs) = extract_coe_la_lc lind in
  let notations,mie = interp_mutual lparams lnamearconstructs finite in
  let kn = declare_mutual_with_eliminations false mie in
  (* Declare the notations now bound to the inductive types *)
  List.iter (fun (df,c,scope) ->
    Metasyntax.add_notation_interpretation df [] c scope) notations;
  List.iter
    (fun id -> 
      Class.try_add_new_coercion (locate (make_short_qualid id)) Global) coes

(* try to find non recursive definitions *)

let list_chop_hd i l = match list_chop i l with
  | (l1,x::l2) -> (l1,x,l2)
  | _ -> assert false

let collect_non_rec env = 
  let rec searchrec lnonrec lnamerec ldefrec larrec nrec = 
    try
      let i = 
        list_try_find_i
          (fun i f ->
             if List.for_all (fun def -> not (occur_var env f def)) ldefrec
             then i else failwith "try_find_i")
          0 lnamerec 
      in
      let (lf1,f,lf2) = list_chop_hd i lnamerec in
      let (ldef1,def,ldef2) = list_chop_hd i ldefrec in
      let (lar1,ar,lar2) = list_chop_hd i larrec in
      let newlnv = 
	try 
	  match list_chop i nrec with 
            | (lnv1,_::lnv2) -> (lnv1@lnv2)
	    | _ -> [] (* nrec=[] for cofixpoints *)
        with Failure "list_chop" -> []
      in 
      searchrec ((f,def,ar)::lnonrec) 
	(lf1@lf2) (ldef1@ldef2) (lar1@lar2) newlnv
    with Failure "try_find_i" -> 
      (List.rev lnonrec,
       (Array.of_list lnamerec, Array.of_list ldefrec,
        Array.of_list larrec, Array.of_list nrec))
  in 
  searchrec [] 

let build_recursive (lnameargsardef:(fixpoint_expr *decl_notation) list)  =
  let lrecnames = List.map (fun ((f,_,_,_,_),_) -> f) lnameargsardef 
  and sigma = Evd.empty
  and env0 = Global.env()
  and nv = Array.of_list (List.map (fun ((_,n,_,_,_),_) -> n) lnameargsardef) in
  (* Build the recursive context and notations for the recursive types *)
  let (rec_sign,rec_impls,arityl) = 
    List.fold_left 
      (fun (env,impls,arl) ((recname,_,bl,arityc,_),_) -> 
        let arityc = generalize_rawconstr arityc bl in
        let arity = interp_type sigma env0 arityc in
	let impl = 
	  if Impargs.is_implicit_args()
	  then Impargs.compute_implicits false env0 arity
	  else [] in
	let impls' =(recname,([],impl,compute_arguments_scope arity))::impls in
        (Environ.push_named (recname,None,arity) env, impls', arity::arl))
      (env0,[],[]) lnameargsardef in
  let arityl = List.rev arityl in
  let notations = 
    List.fold_right (fun (_,ntnopt) l -> option_cons ntnopt l) 
      lnameargsardef [] in

  let recdef =

    (* Declare local notations *)
    let fs = States.freeze() in
    let def = 
      try
	List.iter (fun (df,c,scope) -> (* No scope for tmp notation *)
	 Metasyntax.add_notation_interpretation df rec_impls c None) notations;
	List.map2
	  (fun ((_,_,bl,_,def),_) arity ->
            let def = abstract_rawconstr def bl in
            interp_casted_constr_with_implicits 
	      sigma rec_sign rec_impls def arity)
          lnameargsardef arityl
      with e ->
	States.unfreeze fs; raise e in
    States.unfreeze fs; def 
  in

  let (lnonrec,(namerec,defrec,arrec,nvrec)) = 
    collect_non_rec env0 lrecnames recdef arityl (Array.to_list nv) in
  let recvec = 
    Array.map (subst_vars (List.rev (Array.to_list namerec))) defrec in
  let recdecls = (Array.map (fun id -> Name id) namerec, arrec, recvec) in
  let rec declare i fi =
    let ce = 
      { const_entry_body = mkFix ((nvrec,i),recdecls);
        const_entry_type = Some arrec.(i);
        const_entry_opaque = false } in
    let (_,kn) = declare_constant fi (DefinitionEntry ce, IsDefinition) in
    (ConstRef kn)
  in 
  (* declare the recursive definitions *)
  let lrefrec = Array.mapi declare namerec in
  if_verbose ppnl (recursive_message lrefrec);
  (* The others are declared as normal definitions *)
  let var_subst id = (id, global_reference id) in
  let _ = 
    List.fold_left
      (fun subst (f,def,t) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = Some t;
                    const_entry_opaque = false } in
	 let _ = declare_constant f (DefinitionEntry ce, IsDefinition) in
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst (Array.to_list namerec))
      lnonrec 
  in
  List.iter (fun (df,c,scope) ->
    Metasyntax.add_notation_interpretation df [] c scope) notations

let build_corecursive lnameardef = 
  let lrecnames = List.map (fun (f,_,_,_) -> f) lnameardef
  and sigma = Evd.empty
  and env0 = Global.env() in
  let fs = States.freeze() in
  let (rec_sign,arityl) = 
    try 
      List.fold_left 
        (fun (env,arl) (recname,bl,arityc,_) -> 
           let arityc = generalize_rawconstr arityc bl in
           let arj = type_judgment_of_rawconstr Evd.empty env0 arityc in
	   let arity = arj.utj_val in
           let _ = declare_variable recname
	     (Lib.cwd(),SectionLocalAssum arj.utj_val,IsAssumption Definitional) in
           (Environ.push_named (recname,None,arity) env, (arity::arl)))
        (env0,[]) lnameardef
    with e -> 
      States.unfreeze fs; raise e in 
  let arityl = List.rev arityl in
  let recdef =
    try 
      List.map (fun (_,bl,arityc,def) ->
        let arityc = generalize_rawconstr arityc bl in
        let def = abstract_rawconstr def bl in
	let arity = interp_constr sigma rec_sign arityc in
                  interp_casted_constr sigma rec_sign def arity)
        lnameardef
    with e -> 
      States.unfreeze fs; raise e 
  in
  States.unfreeze fs;
  let (lnonrec,(namerec,defrec,arrec,_)) = 
    collect_non_rec env0 lrecnames recdef arityl [] in
  let recvec = 
    Array.map (subst_vars (List.rev (Array.to_list namerec))) defrec in
  let recdecls = (Array.map (fun id -> Name id) namerec, arrec, recvec) in
  let rec declare i fi =
    let ce = 
      { const_entry_body = mkCoFix (i, recdecls);
        const_entry_type = Some (arrec.(i));
        const_entry_opaque = false } 
    in
    let _,kn = declare_constant fi (DefinitionEntry ce, IsDefinition) in
    (ConstRef kn)
  in 
  let lrefrec = Array.mapi declare namerec in
  if_verbose ppnl (corecursive_message lrefrec);
  let var_subst id = (id, global_reference id) in
  let _ = 
    List.fold_left
      (fun subst (f,def,t) ->
	 let ce = { const_entry_body = replace_vars subst def;
		    const_entry_type = Some t;
                    const_entry_opaque = false } in
	 let _ = declare_constant f (DefinitionEntry ce,IsDefinition) in
      	 warning ((string_of_id f)^" is non-recursively defined");
      	 (var_subst f) :: subst)
      (List.map var_subst (Array.to_list namerec))
      lnonrec 
  in ()

let build_scheme lnamedepindsort = 
  let lrecnames = List.map (fun ((_,f),_,_,_) -> f) lnamedepindsort
  and sigma = Evd.empty
  and env0 = Global.env() in
  let lrecspec =
    List.map
      (fun (_,dep,indid,sort) ->
        let ind = Nametab.global_inductive indid in
        let (mib,mip) = Global.lookup_inductive ind in
         (ind,mib,mip,dep,interp_elimination_sort sort)) 
      lnamedepindsort
  in
  let listdecl = Indrec.build_mutual_indrec env0 sigma lrecspec in 
  let rec declare decl fi lrecref =
    let decltype = Retyping.get_type_of env0 Evd.empty decl in
    let decltype = Evarutil.refresh_universes decltype in
    let ce = { const_entry_body = decl;
               const_entry_type = Some decltype;
               const_entry_opaque = false } in
    let _,kn = declare_constant fi (DefinitionEntry ce, IsDefinition) in
    ConstRef kn :: lrecref
  in 
  let lrecref = List.fold_right2 declare listdecl lrecnames [] in
  if_verbose ppnl (recursive_message (Array.of_list lrecref))

let start_proof id kind c hook =
  let sign = Global.named_context () in
  let sign = clear_proofs sign in
  Pfedit.start_proof id kind sign c hook

let start_proof_com sopt kind (bl,t) hook =
  let id = match sopt with
    | Some id ->
        (* We check existence here: it's a bit late at Qed time *)
        if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
          errorlabstrm "start_proof" (pr_id id ++ str " already exists");
        id
    | None ->
	next_global_ident_away false (id_of_string "Unnamed_thm")
 	  (Pfedit.get_all_proof_names ())
  in
  let env = Global.env () in
  let c = interp_type Evd.empty env (generalize_rawconstr t bl) in
  let _ = Typeops.infer_type env c in
  start_proof id kind c hook

let save id const kind hook =
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let l,r = match kind with
    | IsLocal when Lib.sections_are_opened () ->
	let c = SectionLocalDef (pft, tpo, opacity) in
	let _ = declare_variable id (Lib.cwd(), c, IsDefinition) in
	(Local, VarRef id)
    | IsLocal ->
        let k = IsDefinition in
        let _,kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn)
    | IsGlobal k ->
        let k = theorem_kind_of_goal_kind k in
        let _,kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn) in
  hook l r;
  Pfedit.delete_current_proof ();
  definition_message id

let save_named opacity =
  let id,(const,persistence,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  save id const persistence hook

let check_anonymity id save_ident =
  if atompart_of_id id <> "Unnamed_thm" then
    error "This command can only be used for unnamed theorem"
(*
    message("Overriding name "^(string_of_id id)^" and using "^save_ident)
*)

let save_anonymous opacity save_ident =
  let id,(const,persistence,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const persistence hook

let save_anonymous_with_strength kind opacity save_ident =
  let id,(const,_,hook) = Pfedit.cook_proof () in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save save_ident const (IsGlobal (Proof kind)) hook

let admit () =
  let (id,k,typ,hook) = Pfedit.current_proof_statement () in
(* Contraire aux besoins d'interactivité...
  if k <> IsGlobal (Proof Conjecture) then
    error "Only statements declared as conjecture can be admitted";
*)
  let (_,kn) = declare_constant id (ParameterEntry typ, IsConjecture) in
  hook Global (ConstRef kn);
  Pfedit.delete_current_proof ();
  assumption_message id

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e -> 
    (Evd.empty, Global.env())
