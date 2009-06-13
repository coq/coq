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
open Flags
open Term
open Termops
open Declarations
open Entries
open Inductive
open Environ
open Reduction
open Redexpr
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
open Impargs
open Typeops
open Reductionops
open Indtypes
open Vernacexpr
open Decl_kinds
open Pretyping
open Evarutil
open Evarconv
open Notation
open Goptions
open Mod_subst
open Evd
open Decls

let mkLambdaCit = List.fold_right (fun (x,a) b -> mkLambdaC(x,default_binder_kind,a,b))
let mkProdCit = List.fold_right (fun (x,a) b -> mkProdC(x,default_binder_kind,a,b))

let rec abstract_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,abstract_constr_expr c bl)
  | LocalRawAssum (idl,k,t)::bl ->
      List.fold_right (fun x b -> mkLambdaC([x],k,t,b)) idl
        (abstract_constr_expr c bl)

let rec generalize_constr_expr c = function
  | [] -> c
  | LocalRawDef (x,b)::bl -> mkLetInC(x,b,generalize_constr_expr c bl)
  | LocalRawAssum (idl,k,t)::bl ->
      List.fold_right (fun x b -> mkProdC([x],k,t,b)) idl
        (generalize_constr_expr c bl)

let rec under_binders env f n c =
  if n = 0 then f env Evd.empty c else
    match kind_of_term c with
      | Lambda (x,t,c) ->
	  mkLambda (x,t,under_binders (push_rel (x,None,t) env) f (n-1) c)
      | LetIn (x,b,t,c) ->
	  mkLetIn (x,b,t,under_binders (push_rel (x,Some b,t) env) f (n-1) c)
      | _ -> assert false

let rec destSubCast c = match kind_of_term c with
  | Lambda (x,t,c) -> 
      let (b,u) = destSubCast c in mkLambda (x,t,b), mkProd (x,t,u)
  | LetIn (x,b,t,c) ->
      let (d,u) = destSubCast c in mkLetIn (x,b,t,d), mkLetIn (x,b,t,u)
  | Cast (b,_, u) -> (b,u)
  | _ -> assert false

let rec complete_conclusion a cs = function
  | CProdN (loc,bl,c) -> CProdN (loc,bl,complete_conclusion a cs c)
  | CLetIn (loc,b,t,c) -> CLetIn (loc,b,t,complete_conclusion a cs c)
  | CHole (loc, k) ->
      let (has_no_args,name,params) = a in
      if not has_no_args then
	user_err_loc (loc,"",
	  strbrk"Cannot infer the non constant arguments of the conclusion of "
	  ++ pr_id cs ++ str ".");
      let args = List.map (fun id -> CRef(Ident(loc,id))) params in
      CAppExpl (loc,(None,Ident(loc,name)),List.rev args)
  | c -> c

(* Commands of the interface *)

(* 1| Constant definitions *)

let definition_message id =
  if_verbose message ((string_of_id id) ^ " is defined")

let constant_entry_of_com (bl,com,comtypopt,opacity,boxed) =
  let env = Global.env() in
    match comtypopt with
      None -> 
	let b = abstract_constr_expr com bl in
	let b, imps = interp_constr_evars_impls env b in
	  imps,
	{ const_entry_body = b;
	  const_entry_type = None;
          const_entry_opaque = opacity;
	  const_entry_boxed = boxed }
    | Some comtyp ->
	(* We use a cast to avoid troubles with evars in comtyp *)
	(* that can only be resolved knowing com *)
	let b = abstract_constr_expr (mkCastC (com, Rawterm.CastConv (DEFAULTcast,comtyp))) bl in
	let b, imps = interp_constr_evars_impls env b in
	let (body,typ) = destSubCast b in
	  imps,
	{ const_entry_body = body;
	  const_entry_type = Some typ;
          const_entry_opaque = opacity;
	  const_entry_boxed = boxed }

let red_constant_entry bl ce = function
  | None -> ce
  | Some red ->
      let body = ce.const_entry_body in
      { ce with const_entry_body = 
	under_binders (Global.env()) (fst (reduction_of_red_expr red))
	  (local_binders_length bl)
	  body }

let declare_global_definition ident ce local imps =
  let kn = declare_constant ident (DefinitionEntry ce,IsDefinition Definition) in
  let gr = ConstRef kn in
    maybe_declare_manual_implicits false gr imps;
    if local = Local && Flags.is_verbose() then
      msg_warning (pr_id ident ++ str" is declared as a global definition");
    definition_message ident;
    gr

let declare_definition_hook = ref ignore
let set_declare_definition_hook = (:=) declare_definition_hook
let get_declare_definition_hook () = !declare_definition_hook

let declare_definition ident (local,boxed,dok) bl red_option c typopt hook =
  let imps, ce = constant_entry_of_com (bl,c,typopt,false,boxed) in
  let ce' = red_constant_entry bl ce red_option in
  !declare_definition_hook ce';
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let c =
          SectionLocalDef(ce'.const_entry_body,ce'.const_entry_type,false) in
        let _ = declare_variable ident (Lib.cwd(),c,IsDefinition Definition) in
        definition_message ident;
        if Pfedit.refining () then 
          Flags.if_verbose msg_warning 
	    (str"Local definition " ++ pr_id ident ++ 
             str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        declare_global_definition ident ce' local imps in
  hook local r

let syntax_definition ident (vars,c) local onlyparse =
  let ((vars,_),pat) = interp_aconstr [] (vars,[]) c in
  let onlyparse = onlyparse or Metasyntax.is_not_printable pat in
  Syntax_def.declare_syntactic_definition local ident onlyparse (vars,pat)

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let assumption_message id =
  if_verbose message ((string_of_id id) ^ " is assumed")

let declare_one_assumption is_coe (local,kind) c imps impl keep nl (_,ident) =
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let _ = 
          declare_variable ident 
            (Lib.cwd(), SectionLocalAssum (c,impl,keep), IsAssumption kind) in
        assumption_message ident;
        if is_verbose () & Pfedit.refining () then 
          msgerrnl (str"Warning: Variable " ++ pr_id ident ++ 
          str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        let kn =
          declare_constant ident (ParameterEntry (c,nl), IsAssumption kind) in
	let gr = ConstRef kn in
	  maybe_declare_manual_implicits false gr imps;
        assumption_message ident;
        if local=Local & Flags.is_verbose () then
          msg_warning (pr_id ident ++ str" is declared as a parameter" ++
          str" because it is at a global level");
        gr in
  if is_coe then Class.try_add_new_coercion r local

let declare_assumption_hook = ref ignore
let set_declare_assumption_hook = (:=) declare_assumption_hook

let declare_assumption idl is_coe k bl c impl keep nl =
  if not (Pfedit.refining ()) then 
    let c = generalize_constr_expr c bl in
    let env = Global.env () in
    let c', imps = interp_type_evars_impls env c in
      !declare_assumption_hook c';
      List.iter (declare_one_assumption is_coe k c' imps impl keep nl) idl
  else
    errorlabstrm "Command.Assumption"
	(str "Cannot declare an assumption while in proof editing mode.")

(* 3a| Elimination schemes for mutual inductive definitions *)

open Indrec
open Inductiveops


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
          const_entry_opaque = false;
	  const_entry_boxed = Flags.boxed_definitions() }, 
       Decl_kinds.IsDefinition Definition) in
    definition_message id;
    kn
  in
  let env = Global.env () in
  let sigma = Evd.empty in
  let elim_scheme = Indrec.build_indrec env sigma ind in
  let npars = 
    (* if a constructor of [ind] contains a recursive call, the scheme
       is generalized only wrt recursively uniform parameters *)
    if (Inductiveops.mis_is_recursive_subset [snd ind] mip.mind_recargs) 
    then 
      mib.mind_nparams_rec
    else 
      mib.mind_nparams in
  let make_elim s = Indrec.instantiate_indrec_scheme s npars elim_scheme in
  let kelim = elim_sorts (mib,mip) in
    (* in case the inductive has a type elimination, generates only one
       induction scheme, the other ones share the same code with the
       apropriate type *)
  if List.mem InType kelim then
    let elim = make_elim (new_sort_in_family InType) in
    let cte = declare (mindstr^(Indrec.elimination_suffix InType)) elim None in
    let c = mkConst cte in
    let t = type_of_constant (Global.env()) cte in
    List.iter (fun (sort,suff) -> 
      let (t',c') = 
	Indrec.instantiate_type_indrec_scheme (new_sort_in_family sort)
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

(* bool eq declaration flag && eq dec declaration flag *)
let eq_flag = ref false 
let _ =
  declare_bool_option
    { optsync  = true;
      optname  = "automatic declaration of boolean equality";
      optkey   = (SecondaryTable ("Equality","Scheme"));
      optread  = (fun () -> !eq_flag) ;
      optwrite = (fun b -> eq_flag := b) }

(* boolean equality *)
let (inScheme,outScheme) =  
  declare_object {(default_object "EQSCHEME") with 
                    cache_function = Ind_tables.cache_scheme; 
                    load_function = (fun _ -> Ind_tables.cache_scheme); 
                    subst_function = Auto_ind_decl.subst_in_constr; 
                    export_function = Ind_tables.export_scheme } 

let declare_eq_scheme sp = 
  let mib = Global.lookup_mind sp in
  let nb_ind = Array.length mib.mind_packets in
  let eq_array = Auto_ind_decl.make_eq_scheme sp in
  try
    for i=0 to (nb_ind-1) do
    let cpack = Array.get mib.mind_packets i in
    let nam = id_of_string ((string_of_id cpack.mind_typename)^"_beq")
    in
      let cst_entry = {const_entry_body = eq_array.(i);
                       const_entry_type = None;
                       const_entry_opaque = false;
                       const_entry_boxed = Flags.boxed_definitions() } 
      in
      let cst_decl =  (DefinitionEntry cst_entry),(IsDefinition Definition)
      in
        let cst = Declare.declare_constant nam cst_decl in
          Lib.add_anonymous_leaf (inScheme ((sp,i),mkConst cst));
          definition_message nam
    done
  with Not_found -> 
    error "Your type contains Parameters without a boolean equality."

(* decidability of eq *)


let (inBoolLeib,outBoolLeib) =
  declare_object {(default_object "BOOLLIEB") with
                    cache_function = Ind_tables.cache_bl;
                    load_function = (fun _ -> Ind_tables.cache_bl);
                    subst_function = Auto_ind_decl.subst_in_constr;
                    export_function = Ind_tables.export_bool_leib }

let (inLeibBool,outLeibBool) =
  declare_object {(default_object "LIEBBOOL") with
                    cache_function = Ind_tables.cache_lb;
                    load_function = (fun _ -> Ind_tables.cache_lb);
                    subst_function = Auto_ind_decl.subst_in_constr;
                    export_function = Ind_tables.export_leib_bool }

let (inDec,outDec) =
  declare_object {(default_object "EQDEC") with
                    cache_function = Ind_tables.cache_dec;
                    load_function = (fun _ -> Ind_tables.cache_dec);
                    subst_function = Auto_ind_decl.subst_in_constr;
                    export_function = Ind_tables.export_dec_proof }

let start_hook = ref ignore
let set_start_hook = (:=) start_hook

let start_proof id kind c ?init_tac ?(compute_guard=false) hook =
  let sign = Global.named_context () in
  let sign = clear_proofs sign in
  !start_hook c;
  Pfedit.start_proof id kind sign c ?init_tac ~compute_guard hook

let adjust_guardness_conditions const =
  (* Try all combinations... not optimal *)
  match kind_of_term const.const_entry_body with
  | Fix ((nv,0),(_,_,fixdefs as fixdecls)) ->
      let possible_indexes =
	List.map (fun c ->
	  interval 0 (List.length (fst (Sign.decompose_lam_assum c))))
	  (Array.to_list fixdefs) in
      let indexes = search_guard dummy_loc (Global.env()) possible_indexes fixdecls in 
      { const with const_entry_body = mkFix ((indexes,0),fixdecls) }
  | c -> const

let save id const do_guard (locality,kind) hook =
  let const = if do_guard then adjust_guardness_conditions const else const in
  let {const_entry_body = pft;
       const_entry_type = tpo;
       const_entry_opaque = opacity } = const in
  let k = logical_kind_of_goal_kind kind in
  let l,r = match locality with
    | Local when Lib.sections_are_opened () ->
	let c = SectionLocalDef (pft, tpo, opacity) in
	let _ = declare_variable id (Lib.cwd(), c, k) in
	(Local, VarRef id)
    | Local | Global ->
        let kn = declare_constant id (DefinitionEntry const, k) in
	(Global, ConstRef kn) in
  Pfedit.delete_current_proof ();
  definition_message id;
  hook l r

let save_hook = ref ignore
let set_save_hook f = save_hook := f

let save_named opacity =
  let id,(const,do_guard,persistence,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  save id const do_guard persistence hook

let make_eq_decidability ind = 
    (* fetching data *)
    let mib = Global.lookup_mind (fst ind) in
    let nparams = mib.mind_nparams in
    let nparrec = mib.mind_nparams_rec in
    let lnonparrec,lnamesparrec = 
      context_chop (nparams-nparrec) mib.mind_params_ctxt in
    let proof_name = (string_of_id(
          Array.get mib.mind_packets (snd ind)).mind_typename)^"_eq_dec" in
    let bl_name  =(string_of_id(
          Array.get mib.mind_packets (snd ind)).mind_typename)^"_dec_bl" in
    let lb_name  =(string_of_id(
          Array.get mib.mind_packets (snd ind)).mind_typename)^"_dec_lb" in
  (* main calls*)
    if Ind_tables.check_bl_proof ind
    then (message (bl_name^" is already declared."))
    else (
      start_proof (id_of_string bl_name)
         (Global,Proof Theorem)
         (Auto_ind_decl.compute_bl_goal ind lnamesparrec nparrec)  
            (fun _ _ -> ());
      Auto_ind_decl.compute_bl_tact ind lnamesparrec nparrec;
      save_named true; 
      Lib.add_anonymous_leaf 
        (inBoolLeib (ind,mkConst (Lib.make_con (id_of_string bl_name))))
(*        definition_message (id_of_string bl_name) *)
    );
    if Ind_tables.check_lb_proof ind 
    then (message (lb_name^" is already declared."))
    else (
      start_proof (id_of_string lb_name)
        (Global,Proof Theorem) 
        (Auto_ind_decl.compute_lb_goal ind lnamesparrec nparrec)
        ( fun _ _ -> ());
      Auto_ind_decl.compute_lb_tact ind lnamesparrec nparrec;
      save_named true;
      Lib.add_anonymous_leaf 
        (inLeibBool (ind,mkConst (Lib.make_con (id_of_string lb_name))))
(*      definition_message (id_of_string lb_name) *)
    );
    if Ind_tables.check_dec_proof ind
    then (message (proof_name^" is already declared."))
    else (
      start_proof (id_of_string proof_name)
        (Global,Proof Theorem) 
        (Auto_ind_decl.compute_dec_goal ind lnamesparrec nparrec)
        ( fun _ _ -> ());
      Auto_ind_decl.compute_dec_tact ind lnamesparrec nparrec;
      save_named true;
      Lib.add_anonymous_leaf 
        (inDec (ind,mkConst (Lib.make_con (id_of_string proof_name))))
(*      definition_message (id_of_string proof_name) *)
  )

(* end of automated definition on ind*)

let declare_eliminations sp =
  let mib = Global.lookup_mind sp in
  if mib.mind_finite then begin
    if (!eq_flag) then (declare_eq_scheme sp);
    for i = 0 to Array.length mib.mind_packets - 1 do
      declare_one_elimination (sp,i);
      try
        if (!eq_flag) then (make_eq_decidability (sp,i))
      with _ -> 
          Pfedit.delete_current_proof();
          message "Error while computing decidability scheme. Please report."
    done;
  end

(* 3b| Mutual inductive definitions *)

let compute_interning_datas env ty l nal typl impll =
  let mk_interning_data na typ impls =
    let idl, impl =
      let impl = 
	compute_implicits_with_manual env typ (is_implicit_args ()) impls
      in 
      let sub_impl,_ = list_chop (List.length l) impl in
      let sub_impl' = List.filter is_status_implicit sub_impl in
	(List.map name_of_implicit sub_impl', impl)
    in
      (na, (ty, idl, impl, compute_arguments_scope typ)) in
  (l, list_map3 mk_interning_data nal typl impll)

let declare_interning_data (_,impls) (df,c,scope) =
  silently (Metasyntax.add_notation_interpretation df impls c) scope

let push_named_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_named (id,None,t) env)
    env idl tl

let push_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_rel (Name id,None,t) env)
    env idl tl

type inductive_expr = {
  ind_name : identifier;
  ind_arity : constr_expr;
  ind_lc : (identifier * constr_expr) list
}

let minductive_message = function
  | []  -> error "No inductive definition."
  | [x] -> (pr_id x ++ str " is defined")
  | l   -> hov 0  (prlist_with_sep pr_coma pr_id l ++
		     spc () ++ str "are defined")

let check_all_names_different indl =
  let ind_names = List.map (fun ind -> ind.ind_name) indl in
  let cstr_names = list_map_append (fun ind -> List.map fst ind.ind_lc) indl in
  let l = list_duplicates ind_names in
  if l <> [] then raise (InductiveError (SameNamesTypes (List.hd l)));
  let l = list_duplicates cstr_names in
  if l <> [] then raise (InductiveError (SameNamesConstructors (List.hd l)));
  let l = list_intersect ind_names cstr_names in
  if l <> [] then raise (InductiveError (SameNamesOverlap l))

let mk_mltype_data evdref env assums arity indname =
  let is_ml_type = is_sort env (evars_of !evdref) arity in
  (is_ml_type,indname,assums)

let prepare_param = function
  | (na,None,t) -> out_name na, LocalAssum t 
  | (na,Some b,_) -> out_name na, LocalDef b

let interp_ind_arity evdref env ind =
  interp_type_evars evdref env ind.ind_arity

let interp_cstrs evdref env impls mldata arity ind =
  let cnames,ctyps = List.split ind.ind_lc in
  (* Complete conclusions of constructor types if given in ML-style syntax *)
  let ctyps' = List.map2 (complete_conclusion mldata) cnames ctyps in
  (* Interpret the constructor types *)
  let ctyps'', cimpls = List.split (List.map (interp_type_evars_impls ~evdref env ~impls) ctyps') in
    (cnames, ctyps'', cimpls)

let interp_mutual paramsl indl notations finite = 
  check_all_names_different indl;
  let env0 = Global.env() in
  let evdref = ref (Evd.create_evar_defs Evd.empty) in
  let (env_params, ctx_params), userimpls = 
    interp_context_evars ~fail_anonymous:false evdref env0 paramsl 
  in
  let indnames = List.map (fun ind -> ind.ind_name) indl in

  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter(fun (_,b,_) -> b=None) ctx_params in
  let params = List.map (fun (na,_,_) -> out_name na) assums in

  (* Interpret the arities *)
  let arities = List.map (interp_ind_arity evdref env_params) indl in
  let fullarities = List.map (fun c -> it_mkProd_or_LetIn c ctx_params) arities in
  let env_ar = push_types env0 indnames fullarities in
  let env_ar_params = push_rel_context ctx_params env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun _ -> userimpls) fullarities in
  let impls = compute_interning_datas env0 Inductive params indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data evdref env_params params) arities indnames in

  let constructors =
    States.with_state_protection (fun () -> 
     (* Temporary declaration of notations and scopes *)
     List.iter (declare_interning_data impls) notations;
     (* Interpret the constructor types *)
     list_map3 (interp_cstrs evdref env_ar_params impls) mldatas arities indl)
     () in

  (* Instantiate evars and check all are resolved *)
  let evd,_ = consider_remaining_unif_problems env_params !evdref in
  let evd = Typeclasses.resolve_typeclasses ~onlyargs:false ~fail:true env_params evd in
  let sigma = evars_of evd in
  let constructors = List.map (fun (idl,cl,impsl) -> (idl,List.map (nf_evar sigma) cl,impsl)) constructors in
  let ctx_params = Sign.map_rel_context (nf_evar sigma) ctx_params in
  let arities = List.map (nf_evar sigma) arities in
  List.iter (check_evars env_params Evd.empty evd) arities;
  Sign.iter_rel_context (check_evars env0 Evd.empty evd) ctx_params;
  List.iter (fun (_,ctyps,_) ->
    List.iter (check_evars env_ar_params Evd.empty evd) ctyps)
    constructors;
  
  (* Build the inductive entries *)
  let entries = list_map3 (fun ind arity (cnames,ctypes,cimpls) -> {
    mind_entry_typename = ind.ind_name;
    mind_entry_arity = arity;
    mind_entry_consnames = cnames;
    mind_entry_lc = ctypes
  }) indl arities constructors in
  let impls = 
    let len = List.length ctx_params in
      List.map (fun (_,_,impls) ->
	userimpls, List.map (fun impls -> 
	  userimpls @ (lift_implicits len impls)) impls) constructors
  in
  (* Build the mutual inductive entry *)
  { mind_entry_params = List.map prepare_param ctx_params;
    mind_entry_record = false; 
    mind_entry_finite = finite; 
    mind_entry_inds = entries }, 
    impls

let eq_constr_expr c1 c2 =
  try let _ = Constrextern.check_same_type c1 c2 in true with _ -> false

(* Very syntactical equality *)
let eq_local_binder d1 d2 = match d1,d2 with
  | LocalRawAssum (nal1,k1,c1), LocalRawAssum (nal2,k2,c2) ->
      List.length nal1 = List.length nal2 && k1 = k2 &&
      List.for_all2 (fun (_,na1) (_,na2) -> na1 = na2) nal1 nal2 &&
      eq_constr_expr c1 c2
  | LocalRawDef ((_,id1),c1), LocalRawDef ((_,id2),c2) ->
      id1 = id2 && eq_constr_expr c1 c2
  | _ ->
      false

let eq_local_binders bl1 bl2 =
  List.length bl1 = List.length bl2 && List.for_all2 eq_local_binder bl1 bl2

let extract_coercions indl =
  let mkqid (_,((_,id),_)) = make_short_qualid id in
  let extract lc = List.filter (fun (iscoe,_) -> iscoe) lc in
  List.map mkqid (List.flatten(List.map (fun (_,_,_,lc) -> extract lc) indl))

let extract_params indl =
  let paramsl = List.map (fun (_,params,_,_) -> params) indl in
  match paramsl with
  | [] -> anomaly "empty list of inductive types"
  | params::paramsl ->
      if not (List.for_all (eq_local_binders params) paramsl) then error 
	"Parameters should be syntactically the same for each inductive type.";
      params

let prepare_inductive ntnl indl =
  let indl =
    List.map (fun ((_,indname),_,ar,lc) -> { 
      ind_name = indname;
      ind_arity = Option.cata (fun x -> x) (CSort (dummy_loc, Rawterm.RType None)) ar;
      ind_lc = List.map (fun (_,((_,id),t)) -> (id,t)) lc
    }) indl in
  List.fold_right Option.List.cons ntnl [], indl


let elim_flag = ref true
let _ =
  declare_bool_option 
    { optsync  = true;
      optname  = "automatic declaration of eliminations";
      optkey   = (SecondaryTable ("Elimination","Schemes"));
      optread  = (fun () -> !elim_flag) ;
      optwrite = (fun b -> elim_flag := b) }

let declare_mutual_with_eliminations isrecord mie impls =
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_,kn) = declare_mind isrecord mie in    
    list_iter_i (fun i (indimpls, constrimpls) -> 
      let ind = (kn,i) in
	maybe_declare_manual_implicits false (IndRef ind) indimpls;
	list_iter_i
	  (fun j impls -> 
	    maybe_declare_manual_implicits false (ConstructRef (ind, succ j)) impls)
	  constrimpls)
      impls;
    if_verbose ppnl (minductive_message names);
    if !elim_flag then declare_eliminations kn;
    kn

let build_mutual l finite =
  let indl,ntnl = List.split l in
  let paramsl = extract_params indl in
  let coes = extract_coercions indl in
  let notations,indl = prepare_inductive ntnl indl in
  let mie,impls = interp_mutual paramsl indl notations finite in
  (* Declare the mutual inductive block with its eliminations *)
  ignore (declare_mutual_with_eliminations false mie impls);
  (* Declare the possible notations of inductive types *)
  List.iter (declare_interning_data ([],[])) notations;
  (* Declare the coercions *)
  List.iter (fun qid -> Class.try_add_new_coercion (locate qid) Global) coes

(* 3c| Fixpoints and co-fixpoints *)

let pr_rank = function 
  | 0 -> str "1st"
  | 1 -> str "2nd"
  | 2 -> str "3rd"
  | n -> str ((string_of_int (n+1))^"th")

let recursive_message indexes = function
  | [] -> anomaly "no recursive definition"
  | [id] -> pr_id id ++ str " is recursively defined" ++
      (match indexes with 
	 | Some [|i|] -> str " (decreasing on "++pr_rank i++str " argument)"
 	 | _ -> mt ())
  | l -> hov 0 (prlist_with_sep pr_coma pr_id l ++
		  spc () ++ str "are recursively defined" ++
		  match indexes with 
		    | Some a -> spc () ++ str "(decreasing respectively on " ++
			prlist_with_sep pr_coma pr_rank (Array.to_list a) ++
			str " arguments)"
		    | None -> mt ())

let corecursive_message _ = function
  | [] -> error "No corecursive definition."
  | [id] -> pr_id id ++ str " is corecursively defined"
  | l -> hov 0 (prlist_with_sep pr_coma pr_id l ++
                    spc () ++ str "are corecursively defined")

let recursive_message isfix = 
  if isfix=Fixpoint then recursive_message else corecursive_message

(* An (unoptimized) function that maps preorders to partial orders...

   Input:  a list of associations (x,[y1;...;yn]), all yi distincts
           and different of x, meaning x<=y1, ..., x<=yn

   Output: a list of associations (x,Inr [y1;...;yn]), collecting all
           distincts yi greater than x, _or_, (x, Inl y) meaning that
           x is in the same class as y (in which case, x occurs
           nowhere else in the association map)

   partial_order : ('a * 'a list) list -> ('a * ('a,'a list) union) list
*)

let rec partial_order = function
  | [] -> []
  | (x,xge)::rest ->
    let rec browse res xge' = function
    | [] ->
	let res = List.map (function
	  | (z, Inr zge) when List.mem x zge -> (z, Inr (list_union zge xge'))
	  | r -> r) res in
	(x,Inr xge')::res
    | y::xge -> 
      let rec link y = 
	try match List.assoc y res with
	| Inl z -> link z
	| Inr yge -> 
	  if List.mem x yge then
	    let res = List.remove_assoc y res in
	    let res = List.map (function
	      | (z, Inl t) ->
		  if t = y then (z, Inl x) else (z, Inl t)
	      | (z, Inr zge) ->
		  if List.mem y zge then
		    (z, Inr (list_add_set x (list_remove y zge)))
		  else
		    (z, Inr zge)) res in
	    browse ((y,Inl x)::res) xge' (list_union xge (list_remove x yge))
	  else
	    browse res (list_add_set y (list_union xge' yge)) xge
	with Not_found -> browse res (list_add_set y xge') xge
      in link y
    in browse (partial_order rest) [] xge 

let non_full_mutual_message x xge y yge kind rest =
  let reason = 
    if List.mem x yge then 
      string_of_id y^" depends on "^string_of_id x^" but not conversely"
    else if List.mem y xge then 
      string_of_id x^" depends on "^string_of_id y^" but not conversely"
    else
      string_of_id y^" and "^string_of_id x^" are not mutually dependent" in
  let e = if rest <> [] then "e.g.: "^reason else reason in
  let k = if kind=Fixpoint then "fixpoint" else "cofixpoint" in
  let w =
    if kind=Fixpoint then "Well-foundedness check may fail unexpectedly.\n"
    else "" in
  "Not a fully mutually defined "^k^"\n("^e^").\n"^w

let check_mutuality env kind fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) -> 
      (id, List.filter (fun id' -> id<>id' & occur_var env id' def) names))
      fixl in
  let po = partial_order preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
	if_verbose warning (non_full_mutual_message x xge y yge kind rest)
    | _ -> ()

type fixpoint_kind =
  | IsFixpoint of (identifier located option * recursion_order_expr) list
  | IsCoFixpoint

type fixpoint_expr = {
  fix_name : identifier;
  fix_binders : local_binder list;
  fix_body : constr_expr;
  fix_type : constr_expr
}

let interp_fix_context evdref env fix =
  interp_context_evars evdref env fix.fix_binders

let interp_fix_ccl evdref (env,_) fix =
  interp_type_evars evdref env fix.fix_type

let interp_fix_body evdref env_rec impls (_,ctx) fix ccl =
  let env = push_rel_context ctx env_rec in
  let body = interp_casted_constr_evars evdref env ~impls fix.fix_body ccl in
  it_mkLambda_or_LetIn body ctx

let build_fix_type (_,ctx) ccl = it_mkProd_or_LetIn ccl ctx

let declare_fix boxed kind f def t imps =
  let ce = {
    const_entry_body = def;
    const_entry_type = Some t;
    const_entry_opaque = false;
    const_entry_boxed = boxed
  } in
  let kn = declare_constant f (DefinitionEntry ce,IsDefinition kind) in
  let gr = ConstRef kn in
    maybe_declare_manual_implicits false gr imps;
    gr
      
let prepare_recursive_declaration fixnames fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map (fun id -> Name id) fixnames in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

(* Jump over let-bindings. *)

let rel_index n ctx = 
  list_index0 (Name n) (List.rev_map pi1 (List.filter (fun x -> pi2 x = None) ctx))

let rec unfold f b =
  match f b with
    | Some (x, b') -> x :: unfold f b'
    | None -> []

let compute_possible_guardness_evidences (n,_) (_, fixctx) fixtype =
  match n with 
  | Some (loc, n) -> [rel_index n fixctx]
  | None -> 
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally 
         doesn't seem to worth the effort (except for huge mutual 
	 fixpoints ?) *)
      let len = List.length fixctx in
	unfold (function x when x = len -> None 
	  | n -> Some (n, succ n)) 0

let interp_recursive fixkind l boxed =
  let env = Global.env() in
  let fixl, ntnl = List.split l in
  let kind = if fixkind <> IsCoFixpoint then Fixpoint else CoFixpoint in
  let fixnames = List.map (fun fix -> fix.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let evdref = ref (Evd.create_evar_defs Evd.empty) in
  let fixctxs, fiximps =
    List.split (List.map (interp_fix_context evdref env) fixl) in
  let fixccls = List.map2 (interp_fix_ccl evdref) fixctxs fixl in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let fixtypes = List.map (nf_evar (evars_of !evdref)) fixtypes in
  let env_rec = push_named_types env fixnames fixtypes in

  (* Get interpretation metadatas *)
  let impls = compute_interning_datas env Recursive [] fixnames fixtypes fiximps in
  let notations = List.fold_right Option.List.cons ntnl [] in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs = 
    States.with_state_protection (fun () -> 
      List.iter (declare_interning_data impls) notations;
      list_map3 (interp_fix_body evdref env_rec impls) fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd,_ = consider_remaining_unif_problems env_rec !evdref in
  let fixdefs = List.map (nf_evar (evars_of evd)) fixdefs in
  let fixtypes = List.map (nf_evar (evars_of evd)) fixtypes in
  let evd = Typeclasses.resolve_typeclasses ~onlyargs:false ~fail:true env evd in
  List.iter (check_evars env_rec Evd.empty evd) fixdefs;
  List.iter (check_evars env Evd.empty evd) fixtypes;
  check_mutuality env kind (List.combine fixnames fixdefs);

  (* Build the fix declaration block *)
  let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
  let indexes, fixdecls = 
    match fixkind with
    | IsFixpoint wfl ->
	let possible_indexes = 
	  list_map3 compute_possible_guardness_evidences wfl fixctxs fixtypes in
	let indexes = search_guard dummy_loc env possible_indexes fixdecls in 
	Some indexes, list_map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 l
    | IsCoFixpoint ->
	None, list_map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 l
  in

  (* Declare the recursive definitions *)
  ignore (list_map4 (declare_fix boxed kind) fixnames fixdecls fixtypes fiximps);
  if_verbose ppnl (recursive_message kind indexes fixnames);

  (* Declare notations *)
  List.iter (declare_interning_data ([],[])) notations

let build_recursive l b =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
  let fixl = List.map (fun (((_,id),_,bl,typ,def),ntn) -> 
    ({fix_name = id; fix_binders = bl; fix_body = def; fix_type = typ},ntn))
    l in
  interp_recursive (IsFixpoint g) fixl b

let build_corecursive l b =
  let fixl = List.map (fun (((_,id),bl,typ,def),ntn) -> 
    ({fix_name = id; fix_binders = bl; fix_body = def; fix_type = typ},ntn))
    l in
  interp_recursive IsCoFixpoint fixl b

(* 3d| Schemes *)
let rec split_scheme l = 
 let env = Global.env() in
 match l with
  | [] -> [],[]
  | (Some id,t)::q -> let l1,l2 = split_scheme q in 
    ( match t with
      | InductionScheme (x,y,z) -> ((id,x,y,z)::l1),l2
      | EqualityScheme  x -> l1,(x::l2)
    )
(*
 if no name has been provided, we build one from the types of the ind
requested 
*)
  | (None,t)::q ->
       let l1,l2 = split_scheme q in
    ( match t with
      | InductionScheme (x,y,z) ->
             let ind = mkInd (Nametab.inductive_of_reference y) in
             let sort_of_ind = family_of_sort (Typing.sort_of env Evd.empty ind)
in
             let z' = family_of_sort (interp_sort z) in
             let suffix = (
                match sort_of_ind with
                | InProp ->
                    if x then (match z' with
                       | InProp -> "_ind_nodep"
                       | InSet -> "_rec_nodep"
                       | InType -> "_rect_nodep")
                    else ( match z' with
                       | InProp -> "_ind"
                       | InSet -> "_rec"
                       | InType -> "_rect" )
                | _ ->
                    if x then (match z' with
                       | InProp -> "_ind"
                       | InSet -> "_rec"
                       | InType -> "_rect" )
                    else (match z' with
                       | InProp -> "_ind_nodep"
                       | InSet  -> "_rec_nodep"
                       | InType -> "_rect_nodep")
                ) in
            let newid = (string_of_id (Pcoq.coerce_global_to_id y))^suffix in
            let newref = (dummy_loc,id_of_string newid) in
          ((newref,x,y,z)::l1),l2
      | EqualityScheme  x -> l1,(x::l2)
    )


let build_induction_scheme lnamedepindsort = 
  let lrecnames = List.map (fun ((_,f),_,_,_) -> f) lnamedepindsort
  and sigma = Evd.empty
  and env0 = Global.env() in
  let lrecspec =
    List.map
      (fun (_,dep,indid,sort) ->
        let ind = Nametab.inductive_of_reference indid in
        let (mib,mip) = Global.lookup_inductive ind in
         (ind,mib,mip,dep,interp_elimination_sort sort)) 
      lnamedepindsort
  in
  let listdecl = Indrec.build_mutual_indrec env0 sigma lrecspec in 
  let rec declare decl fi lrecref =
    let decltype = Retyping.get_type_of env0 Evd.empty decl in
    let decltype = refresh_universes decltype in
    let ce = { const_entry_body = decl;
               const_entry_type = Some decltype;
               const_entry_opaque = false;
	       const_entry_boxed = Flags.boxed_definitions() } in
    let kn = declare_constant fi (DefinitionEntry ce, IsDefinition Scheme) in
    ConstRef kn :: lrecref
  in 
  let _ = List.fold_right2 declare listdecl lrecnames [] in
  if_verbose ppnl (recursive_message Fixpoint None lrecnames)

let build_scheme l = 
  let ischeme,escheme = split_scheme l in
(* we want 1 kind of scheme at a time so we check if the user
tried to declare different schemes at once *)
    if (ischeme <> []) && (escheme <> []) 
    then
      error "Do not declare equality and induction scheme at the same time."
    else (
      if ischeme <> [] then build_induction_scheme ischeme;
      List.iter ( fun indname -> 
        let ind = Nametab.inductive_of_reference indname
        in declare_eq_scheme (fst ind);
        try
           make_eq_decidability ind 
        with _ -> 
          Pfedit.delete_current_proof();
          message "Error while computing decidability scheme. Please report."
      ) escheme
    )
	
let list_split_rev_at index l = 
  let rec aux i acc = function
      hd :: tl when i = index -> acc, tl
    | hd :: tl -> aux (succ i) (hd :: acc) tl
    | [] -> failwith "list_split_at: Invalid argument"
  in aux 0 [] l

let fold_left' f = function 
    [] -> raise (Invalid_argument "fold_right'")
  | hd :: tl -> List.fold_left f hd tl
      
let build_combined_scheme name schemes =
  let env = Global.env () in
(*   let nschemes = List.length schemes in *)
  let find_inductive ty =
    let (ctx, arity) = decompose_prod ty in
    let (_, last) = List.hd ctx in
      match kind_of_term last with
	| App (ind, args) -> 
	    let ind = destInd ind in
	    let (_,spec) = Inductive.lookup_mind_specif env ind in
	      ctx, ind, spec.mind_nrealargs
	| _ -> ctx, destInd last, 0
  in
  let defs =  
    List.map (fun x -> 
		let refe = Ident x in
		let qualid = qualid_of_reference refe in
		let cst = try Nametab.locate_constant (snd qualid) 
                  with Not_found -> error ((string_of_qualid (snd qualid))^" is not declared.")
                in
		let ty = Typeops.type_of_constant env cst in
		  qualid, cst, ty)
      schemes
  in
  let (qid, c, t) = List.hd defs in
  let ctx, ind, nargs = find_inductive t in
  (* Number of clauses, including the predicates quantification *)
  let prods = nb_prod t - (nargs + 1) in
  let coqand = Coqlib.build_coq_and () and coqconj = Coqlib.build_coq_conj () in
  let relargs = rel_vect 0 prods in
  let concls = List.rev_map 
    (fun (_, cst, t) -> 
      mkApp(mkConst cst, relargs),
      snd (decompose_prod_n prods t)) defs in
  let concl_bod, concl_typ = 
    fold_left'
      (fun (accb, acct) (cst, x) -> 
	mkApp (coqconj, [| x; acct; cst; accb |]),
	mkApp (coqand, [| x; acct |])) concls
  in
  let ctx, _ = 
    list_split_rev_at prods 
      (List.rev_map (fun (x, y) -> x, None, y) ctx) in
  let typ = it_mkProd_wo_LetIn concl_typ ctx in
  let body = it_mkLambda_or_LetIn concl_bod ctx in
  let ce = { const_entry_body = body;
             const_entry_type = Some typ;
             const_entry_opaque = false;
	     const_entry_boxed = Flags.boxed_definitions() } in
  let _ = declare_constant (snd name) (DefinitionEntry ce, IsDefinition Scheme) in
    if_verbose ppnl (recursive_message Fixpoint None [snd name])
(* 4| Goal declaration *)

(* 4.1| Support for mutually proved theorems *)

let retrieve_first_recthm = function
  | VarRef id -> 
      (pi2 (Global.lookup_named id),variable_opacity id)
  | ConstRef cst -> 
      let {const_body=body;const_opaque=opaq} =	Global.lookup_constant cst in
      (Option.map Declarations.force body,opaq)
  | _ -> assert false

let default_thm_id = id_of_string "Unnamed_thm"

let compute_proof_name = function
  | Some (loc,id) ->
      (* We check existence here: it's a bit late at Qed time *)
      if Nametab.exists_cci (Lib.make_path id) or is_section_variable id then
        user_err_loc (loc,"",pr_id id ++ str " already exists.");
      id
  | None ->
      let rec next avoid id =
        let id = next_global_ident_away false id avoid in
        if Nametab.exists_cci (Lib.make_path id) then next (id::avoid) id 
        else id
      in
      next (Pfedit.get_all_proof_names ()) default_thm_id

let save_remaining_recthms (local,kind) body opaq i (id,(t_i,imps)) =
  match body with
  | None ->
      (match local with
      | Local ->
          let impl=false in (* copy values from Vernacentries *)
          let k = IsAssumption Conjectural in
          let c = SectionLocalAssum (t_i,impl,[]) in
	  let _ = declare_variable id (Lib.cwd(),c,k) in
          (Local,VarRef id,imps)
      | Global ->
          let k = IsAssumption Conjectural in
          let kn = declare_constant id (ParameterEntry (t_i,false), k) in
          (Global,ConstRef kn,imps))
  | Some body ->
      let k = logical_kind_of_goal_kind kind in
      let body_i = match kind_of_term body with
        | Fix ((nv,0),decls) -> mkFix ((nv,i),decls)
        | CoFix (0,decls) -> mkCoFix (i,decls)
        | _ -> anomaly "Not a proof by induction" in
      match local with
      | Local ->
	  let c = SectionLocalDef (body_i, Some t_i, opaq) in
	  let _ = declare_variable id (Lib.cwd(), c, k) in
          (Local,VarRef id,imps)
      | Global -> 
          let const =
            { const_entry_body = body_i;
              const_entry_type = Some t_i;
              const_entry_opaque = opaq;
              const_entry_boxed = false (* copy of what cook_proof does *)} in
          let kn = declare_constant id (DefinitionEntry const, k) in
          (Global,ConstRef kn,imps)

let look_for_mutual_statements thms =
  if List.tl thms <> [] then
    (* More than one statement: we look for a common inductive hyp or a *)
    (* common coinductive conclusion *)
    let n = List.length thms in
    let inds = List.map (fun (id,(t,_) as x) -> 
      let (hyps,ccl) = Sign.decompose_prod_assum t in
      let whnf_hyp_hds = fold_map_rel_context
        (fun env c -> fst (whd_betadeltaiota_stack env Evd.empty c))
	(Global.env()) hyps in
      let ind_hyps =
        List.flatten (list_map_i (fun i (_,b,t) ->
          match kind_of_term t with
          | Ind (kn,_ as ind) when
                let mind = Global.lookup_mind kn in
                mind.mind_finite & b = None ->
              [ind,x,i]
          | _ ->
              []) 1 (List.rev whnf_hyp_hds)) in
      let ind_ccl =
        let cclenv = push_rel_context hyps (Global.env()) in
        let whnf_ccl,_ = whd_betadeltaiota_stack cclenv Evd.empty ccl in
        match kind_of_term whnf_ccl with
        | Ind (kn,_ as ind) when
              let mind = Global.lookup_mind kn in
              mind.mind_ntypes = n & not mind.mind_finite ->
            [ind,x,0]
        | _ ->
            [] in
      ind_hyps,ind_ccl) thms in
    let inds_hyps,ind_ccls = List.split inds in
    let of_same_mutind ((kn,_),_,_) = function ((kn',_),_,_) -> kn = kn' in
    (* Check if all conclusions are coinductive in the same type *)
    (* (degenerated cartesian product since there is at most one coind ccl) *)
    let same_indccl =
      list_cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks 
	then Some (hyp::oks) else None) [] ind_ccls in
    let ordered_same_indccl =
      List.filter (list_for_all_i (fun i ((kn,j),_,_) -> i=j) 0) same_indccl in
    (* Check if some hypotheses are inductive in the same type *)
    let common_same_indhyp =
      list_cartesians_filter (fun hyp oks ->
	if List.for_all (of_same_mutind hyp) oks
	then Some (hyp::oks) else None) [] inds_hyps in
    let ordered_inds,finite =
      match ordered_same_indccl, common_same_indhyp with
      | indccl::rest, _ ->
	  assert (rest=[]);
          (* One occ. of common coind ccls and no common inductive hyps *)
	  if common_same_indhyp <> [] then 
	    if_verbose warning "Assuming mutual coinductive statements.";
	  flush_all ();
          indccl, true
      | [], _::_ ->
	  if same_indccl <> [] &&
	     list_distinct (List.map pi1 (List.hd same_indccl)) then
	    if_verbose warn (strbrk "Coinductive statements do not follow the order of definition, assume the proof to be by induction."); flush_all ();
	  (* assume the largest indices as possible *)
	  list_last common_same_indhyp, false
      | _, [] ->
	  error
            ("Cannot find common (mutual) inductive premises or coinductive" ^
             " conclusions in the statements.")
    in
    let nl,thms = List.split (List.map (fun (_,x,i) -> (i,x)) ordered_inds) in
    let rec_tac =
      if finite then
        match List.map (fun (id,(t,_)) -> (id,t)) thms with
        | (id,_)::l -> Hiddentac.h_mutual_cofix true id l
        | _ -> assert false
      else
	(* nl is dummy: it will be recomputed at Qed-time *)
        match List.map2 (fun (id,(t,_)) n -> (id,n,t)) thms nl with
        | (id,n,_)::l -> Hiddentac.h_mutual_fix true id n l
        | _ -> assert false in
    Some rec_tac,thms
  else
    None, thms

(* 4.2| General support for goals *)

let start_proof_com kind thms hook =
  let thms = List.map (fun (sopt,(bl,t)) ->
    (compute_proof_name sopt,
     interp_type_evars_impls (Global.env()) (generalize_constr_expr t bl)))
    thms in
  let rec_tac,thms = look_for_mutual_statements thms in
  match thms with
  | [] -> anomaly "No proof to start"
  | (id,(t,imps))::other_thms ->
      let hook strength ref =
        let other_thms_data =
          if other_thms = [] then [] else
            (* there are several theorems defined mutually *)
            let body,opaq = retrieve_first_recthm ref in
            list_map_i (save_remaining_recthms kind body opaq) 1 other_thms in
        let thms_data = (strength,ref,imps)::other_thms_data in
        List.iter (fun (strength,ref,imps) ->
	  maybe_declare_manual_implicits false ref imps;
	  hook strength ref) thms_data in
      start_proof id kind t ?init_tac:rec_tac
	~compute_guard:(rec_tac<>None) hook

let check_anonymity id save_ident =
  if atompart_of_id id <> "Unnamed_thm" then
    error "This command can only be used for unnamed theorem."
(*
    message("Overriding name "^(string_of_id id)^" and using "^save_ident)
*)

let save_anonymous opacity save_ident =
  let id,(const,do_guard,persistence,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  save save_ident const do_guard persistence hook

let save_anonymous_with_strength kind opacity save_ident =
  let id,(const,do_guard,_,hook) = Pfedit.cook_proof !save_hook in
  let const = { const with const_entry_opaque = opacity } in
  check_anonymity id save_ident;
  (* we consider that non opaque behaves as local for discharge *)
  save save_ident const do_guard (Global, Proof kind) hook

let admit () =
  let (id,k,typ,hook) = Pfedit.current_proof_statement () in
(* Contraire aux besoins d'interactivité...
  if k <> IsGlobal (Proof Conjecture) then
    error "Only statements declared as conjecture can be admitted";
*)
  let kn =
    declare_constant id (ParameterEntry (typ,false), IsAssumption Conjectural) in
  Pfedit.delete_current_proof ();
  assumption_message id;
  hook Global (ConstRef kn)

let get_current_context () =
  try Pfedit.get_current_goal_context ()
  with e when Logic.catchable_exception e -> 
    (Evd.empty, Global.env())


