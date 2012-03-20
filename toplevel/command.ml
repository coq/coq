(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Flags
open Term
open Termops
open Entries
open Environ
open Redexpr
open Declare
open Names
open Libnames
open Nameops
open Topconstr
open Constrintern
open Nametab
open Impargs
open Reductionops
open Indtypes
open Decl_kinds
open Pretyping
open Evarutil
open Evarconv
open Notation
open Indschemes

let rec under_binders env f n c =
  if n = 0 then f env Evd.empty c else
    match kind_of_term c with
      | Lambda (x,t,c) ->
	  mkLambda (x,t,under_binders (push_rel (x,None,t) env) f (n-1) c)
      | LetIn (x,b,t,c) ->
	  mkLetIn (x,b,t,under_binders (push_rel (x,Some b,t) env) f (n-1) c)
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

let red_constant_entry n ce = function
  | None -> ce
  | Some red ->
      let body = ce.const_entry_body in
      { ce with const_entry_body =
        under_binders (Global.env()) (fst (reduction_of_red_expr red)) n body }

let interp_definition bl red_option c ctypopt =
  let env = Global.env() in
  let evdref = ref Evd.empty in
  let impls, ((env_bl, ctx), imps1) = interp_context_evars evdref env bl in
  let nb_args = List.length ctx in
  let imps,ce =
    match ctypopt with
      None ->
	let c, imps2 = interp_constr_evars_impls ~impls ~evdref ~fail_evar:false env_bl c in
	let body = nf_evar !evdref (it_mkLambda_or_LetIn c ctx) in
	imps1@(Impargs.lift_implicits nb_args imps2),
	{ const_entry_body = body;
          const_entry_secctx = None;
	  const_entry_type = None;
          const_entry_opaque = false }
    | Some ctyp ->
	let ty, impsty = interp_type_evars_impls ~impls ~evdref ~fail_evar:false env_bl ctyp in
	let c, imps2 = interp_casted_constr_evars_impls ~impls ~evdref ~fail_evar:false env_bl c ty in
	let body = nf_evar !evdref (it_mkLambda_or_LetIn c ctx) in
	let typ = nf_evar !evdref (it_mkProd_or_LetIn ty ctx) in
	imps1@(Impargs.lift_implicits nb_args imps2),
	{ const_entry_body = body;
          const_entry_secctx = None;
	  const_entry_type = Some typ;
          const_entry_opaque = false }
  in
  red_constant_entry (rel_context_length ctx) ce red_option, !evdref, imps

let check_definition (ce, evd, imps) =
  let env = Global.env () in
    check_evars env Evd.empty evd ce.const_entry_body;
    Option.iter (check_evars env Evd.empty evd) ce.const_entry_type;
    ce

let declare_global_definition ident ce local k imps =
  let kn = declare_constant ident (DefinitionEntry ce,IsDefinition k) in
  let gr = ConstRef kn in
    maybe_declare_manual_implicits false gr imps;
    if local = Local && Flags.is_verbose() then
      msg_warning (pr_id ident ++ str" is declared as a global definition");
    definition_message ident;
    Autoinstance.search_declaration (ConstRef kn);
    gr

let declare_definition_hook = ref ignore
let set_declare_definition_hook = (:=) declare_definition_hook
let get_declare_definition_hook () = !declare_definition_hook

let declare_definition ident (local,k) ce imps hook =
  !declare_definition_hook ce;
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let c =
          SectionLocalDef(ce.const_entry_body ,ce.const_entry_type,false) in
        let _ = declare_variable ident (Lib.cwd(),c,IsDefinition k) in
        definition_message ident;
        if Pfedit.refining () then
          Flags.if_warn msg_warning
	    (str"Local definition " ++ pr_id ident ++
             str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        declare_global_definition ident ce local k imps in
  hook local r

let _ = Obligations.declare_definition_ref := declare_definition

let do_definition ident k bl red_option c ctypopt hook =
  let (ce, evd, imps as def) = interp_definition bl red_option c ctypopt in
    if Flags.is_program_mode () then
      let env = Global.env () in
      let c = ce.const_entry_body in
      let typ = match ce.const_entry_type with 
	| Some t -> t
	| None -> Retyping.get_type_of env evd c
      in 
      Obligations.check_evars env evd;
      let obls, _, c, cty = 
	Obligations.eterm_obligations env ident evd 0 c typ
      in
	ignore(Obligations.add_definition ident ~term:c cty ~implicits:imps ~kind:k ~hook obls)
    else let ce = check_definition def in
      declare_definition ident k ce imps hook

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let declare_assumption is_coe (local,kind) c imps impl nl (_,ident) =
  let r = match local with
    | Local when Lib.sections_are_opened () ->
        let _ =
          declare_variable ident
            (Lib.cwd(), SectionLocalAssum (c,impl), IsAssumption kind) in
        assumption_message ident;
        if is_verbose () & Pfedit.refining () then
          msgerrnl (str"Warning: Variable " ++ pr_id ident ++
          str" is not visible from current goals");
	let r = VarRef ident in
	  Typeclasses.declare_instance None true r; r
    | (Global|Local) ->
        let kn =
          declare_constant ident 
            (ParameterEntry (None,c,nl), IsAssumption kind) in
	let gr = ConstRef kn in
	  maybe_declare_manual_implicits false gr imps;
        assumption_message ident;
        if local=Local & Flags.is_verbose () then
          msg_warning (pr_id ident ++ str" is declared as a parameter" ++
          str" because it is at a global level");
	Autoinstance.search_declaration (ConstRef kn);
	Typeclasses.declare_instance None false gr;
        gr 
  in
    if is_coe then Class.try_add_new_coercion r local

let declare_assumptions_hook = ref ignore
let set_declare_assumptions_hook = (:=) declare_assumptions_hook

let interp_assumption bl c =
  let c = prod_constr_expr c bl in
  let env = Global.env () in
  interp_type_evars_impls env c

let declare_assumptions idl is_coe k c imps impl_is_on nl =
  !declare_assumptions_hook c;
  List.iter (declare_assumption is_coe k c imps impl_is_on nl) idl

(* 3a| Elimination schemes for mutual inductive definitions *)

(* 3b| Mutual inductive definitions *)

let push_named_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_named (id,None,t) env)
    env idl tl

let push_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_rel (Name id,None,t) env)
    env idl tl

type structured_one_inductive_expr = {
  ind_name : identifier;
  ind_arity : constr_expr;
  ind_lc : (identifier * constr_expr) list
}

type structured_inductive_expr =
  local_binder list * structured_one_inductive_expr list

let minductive_message = function
  | []  -> error "No inductive definition."
  | [x] -> (pr_id x ++ str " is defined")
  | l   -> hov 0  (prlist_with_sep pr_comma pr_id l ++
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
  let is_ml_type = is_sort env !evdref arity in
  (is_ml_type,indname,assums)

let prepare_param = function
  | (na,None,t) -> out_name na, LocalAssum t
  | (na,Some b,_) -> out_name na, LocalDef b

let interp_ind_arity evdref env ind =
  interp_type_evars_impls ~evdref env ind.ind_arity

let interp_cstrs evdref env impls mldata arity ind =
  let cnames,ctyps = List.split ind.ind_lc in
  (* Complete conclusions of constructor types if given in ML-style syntax *)
  let ctyps' = List.map2 (complete_conclusion mldata) cnames ctyps in
  (* Interpret the constructor types *)
  let ctyps'', cimpls = List.split (List.map (interp_type_evars_impls ~evdref env ~impls) ctyps') in
    (cnames, ctyps'', cimpls)

let interp_mutual_inductive (paramsl,indl) notations finite =
  check_all_names_different indl;
  let env0 = Global.env() in
  let evdref = ref Evd.empty in
  let _, ((env_params, ctx_params), userimpls) =
    interp_context_evars evdref env0 paramsl
  in
  let indnames = List.map (fun ind -> ind.ind_name) indl in

  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter(fun (_,b,_) -> b=None) ctx_params in
  let params = List.map (fun (na,_,_) -> out_name na) assums in

  (* Interpret the arities *)
  let arities = List.map (interp_ind_arity evdref env_params) indl in
  let fullarities = List.map (fun (c, _) -> it_mkProd_or_LetIn c ctx_params) arities in
  let env_ar = push_types env0 indnames fullarities in
  let env_ar_params = push_rel_context ctx_params env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun (_, impls) -> userimpls @ lift_implicits (rel_context_nhyps ctx_params) impls) arities in
  let arities = List.map fst arities in
  let impls = compute_internalization_env env0 (Inductive params) indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data evdref env_params params) arities indnames in

  let constructors =
    Metasyntax.with_syntax_protection (fun () ->
     (* Temporary declaration of notations and scopes *)
     List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
     (* Interpret the constructor types *)
     list_map3 (interp_cstrs evdref env_ar_params impls) mldatas arities indl)
     () in

  (* Instantiate evars and check all are resolved *)
  let evd = consider_remaining_unif_problems env_params !evdref in
  let evd = Typeclasses.resolve_typeclasses ~with_goals:false ~fail:true env_params evd in
  let sigma = evd in
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
    let len = rel_context_nhyps ctx_params in
      List.map2 (fun indimpls (_,_,cimpls) ->
	indimpls, List.map (fun impls ->
	  userimpls @ (lift_implicits len impls)) cimpls) indimpls constructors
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
  let mkqid (_,((_,id),_)) = qualid_of_ident id in
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

let extract_inductive indl =
  List.map (fun ((_,indname),_,ar,lc) -> {
    ind_name = indname;
    ind_arity = Option.cata (fun x -> x) (CSort (dummy_loc, Glob_term.GType None)) ar;
    ind_lc = List.map (fun (_,((_,id),t)) -> (id,t)) lc
  }) indl

let extract_mutual_inductive_declaration_components indl =
  let indl,ntnl = List.split indl in
  let params = extract_params indl in
  let coes = extract_coercions indl in
  let indl = extract_inductive indl in
  (params,indl), coes, List.flatten ntnl

let declare_mutual_inductive_with_eliminations isrecord mie impls =
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_,kn) = declare_mind isrecord mie in
  let mind = Global.mind_of_delta_kn kn in
  list_iter_i (fun i (indimpls, constrimpls) ->
		   let ind = (mind,i) in
		     Autoinstance.search_declaration (IndRef ind);
		     maybe_declare_manual_implicits false (IndRef ind) indimpls;
		     list_iter_i
		       (fun j impls ->
(*	    Autoinstance.search_declaration (ConstructRef (ind,j));*)
			  maybe_declare_manual_implicits false (ConstructRef (ind, succ j)) impls)
		       constrimpls)
      impls;
  if_verbose ppnl (minductive_message names);
  declare_default_schemes mind;
  mind

open Vernacexpr

type one_inductive_impls =
  Impargs.manual_explicitation list (* for inds *)*
  Impargs.manual_explicitation list list (* for constrs *)

type one_inductive_expr =
  lident * local_binder list * constr_expr option * constructor_expr list

let do_mutual_inductive indl finite =
  let indl,coes,ntns = extract_mutual_inductive_declaration_components indl in
  (* Interpret the types *)
  let mie,impls = interp_mutual_inductive indl ntns finite in
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (declare_mutual_inductive_with_eliminations UserVerbose mie impls);
  (* Declare the possible notations of inductive types *)
  List.iter Metasyntax.add_notation_interpretation ntns;
  (* Declare the coercions *)
  List.iter (fun qid -> Class.try_add_new_coercion (locate qid) Global) coes

(* 3c| Fixpoints and co-fixpoints *)

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

let non_full_mutual_message x xge y yge isfix rest =
  let reason =
    if List.mem x yge then
      string_of_id y^" depends on "^string_of_id x^" but not conversely"
    else if List.mem y xge then
      string_of_id x^" depends on "^string_of_id y^" but not conversely"
    else
      string_of_id y^" and "^string_of_id x^" are not mutually dependent" in
  let e = if rest <> [] then "e.g.: "^reason else reason in
  let k = if isfix then "fixpoint" else "cofixpoint" in
  let w =
    if isfix
    then strbrk "Well-foundedness check may fail unexpectedly." ++ fnl()
    else mt () in
  strbrk ("Not a fully mutually defined "^k) ++ fnl () ++
  strbrk ("("^e^").") ++ fnl () ++ w

let check_mutuality env isfix fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) ->
      (id, List.filter (fun id' -> id<>id' & occur_var env id' def) names))
      fixl in
  let po = partial_order preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
	if_warn msg_warning (non_full_mutual_message x xge y yge isfix rest)
    | _ -> ()

type structured_fixpoint_expr = {
  fix_name : identifier;
  fix_annot : identifier located option;
  fix_binders : local_binder list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

let interp_fix_context evdref env isfix fix =
  let before, after = if isfix then split_at_annot fix.fix_binders fix.fix_annot else [], fix.fix_binders in
  let impl_env, ((env', ctx), imps) = interp_context_evars evdref env before in
  let _, ((env'', ctx'), imps') = interp_context_evars ~impl_env evdref env' after in
  let annot = Option.map (fun _ -> List.length (assums_of_rel_context ctx)) fix.fix_annot in
    ((env'', ctx' @ ctx), imps @ imps', annot)
      
let interp_fix_ccl evdref (env,_) fix =
  interp_type_evars evdref env fix.fix_type

let interp_fix_body evdref env_rec impls (_,ctx) fix ccl =
  Option.map (fun body ->
    let env = push_rel_context ctx env_rec in
    let body = interp_casted_constr_evars evdref env ~impls body ccl in
    it_mkLambda_or_LetIn body ctx) fix.fix_body

let build_fix_type (_,ctx) ccl = it_mkProd_or_LetIn ccl ctx

let declare_fix kind f def t imps =
  let ce = {
    const_entry_body = def;
    const_entry_secctx = None;
    const_entry_type = Some t;
    const_entry_opaque = false }
  in
  let kn = declare_constant f (DefinitionEntry ce,IsDefinition kind) in
  let gr = ConstRef kn in
  Autoinstance.search_declaration (ConstRef kn);
  maybe_declare_manual_implicits false gr imps;
  gr

let _ = Obligations.declare_fix_ref := declare_fix

let prepare_recursive_declaration fixnames fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map (fun id -> Name id) fixnames in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

(* Jump over let-bindings. *)

let compute_possible_guardness_evidences (ids,_,na) =
  match na with
  | Some i -> [i]
  | None ->
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
	 fixpoints ?) *)
      interval 0 (List.length ids - 1)

type recursive_preentry =
  identifier list * constr option list * types list

(* Wellfounded definition *)

open Coqlib

let contrib_name = "Program"
let subtac_dir = [contrib_name]
let fixsub_module = subtac_dir @ ["Wf"]
let utils_module = subtac_dir @ ["Utils"]
let tactics_module = subtac_dir @ ["Tactics"]

let init_reference dir s () = Coqlib.gen_reference "Command" dir s
let init_constant dir s () = Coqlib.gen_constant "Command" dir s
let make_ref l s = init_reference l s
let fix_proto = init_constant tactics_module "fix_proto"
let fix_sub_ref = make_ref fixsub_module "Fix_sub"
let measure_on_R_ref = make_ref fixsub_module "MR"
let well_founded = init_constant ["Init"; "Wf"] "well_founded"
let mkSubset name typ prop =
  mkApp ((delayed_force build_sigma).typ,
	 [| typ; mkLambda (name, typ, prop) |])
let sigT = Lazy.lazy_from_fun build_sigma_type

let make_qref s = Qualid (dummy_loc, qualid_of_string s)
let lt_ref = make_qref "Init.Peano.lt"

let rec telescope = function
  | [] -> assert false
  | [(n, None, t)] -> t, [n, Some (mkRel 1), t], mkRel 1
  | (n, None, t) :: tl ->
      let ty, tys, (k, constr) =
	List.fold_left
	  (fun (ty, tys, (k, constr)) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let sigty = mkApp ((Lazy.force sigT).typ, [|t; pred|]) in
	    let intro = mkApp ((Lazy.force sigT).intro, [|lift k t; lift k pred; mkRel k; constr|]) in
	      (sigty, pred :: tys, (succ k, intro)))
	  (t, [], (2, mkRel 1)) tl
      in
      let (last, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, subst) ->
	  let proj1 = applistc (Lazy.force sigT).proj1 [t; pred; prev] in
	  let proj2 = applistc (Lazy.force sigT).proj2 [t; pred; prev] in
	    (lift 1 proj2, (n, Some proj1, t) :: subst))
	(List.rev tys) tl (mkRel 1, [])
      in ty, ((n, Some last, t) :: subst), constr

  | (n, Some b, t) :: tl -> let ty, subst, term = telescope tl in
      ty, ((n, Some b, t) :: subst), lift 1 term

let nf_evar_context isevars ctx =
  List.map (fun (n, b, t) ->
    (n, Option.map (Evarutil.nf_evar isevars) b, Evarutil.nf_evar isevars t)) ctx

let build_wellfounded (recname,n,bl,arityc,body) r measure notation =
  Coqlib.check_required_library ["Coq";"Program";"Wf"];
  let sigma = Evd.empty in
  let isevars = ref (Evd.create_evar_defs sigma) in
  let env = Global.env() in
  let _, ((env', binders_rel), impls) = interp_context_evars isevars env bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let top_arity = interp_type_evars isevars top_env arityc in
  let full_arity = it_mkProd_or_LetIn top_arity binders_rel in
  let argtyp, letbinders, make = telescope binders_rel in
  let argname = id_of_string "recarg" in
  let arg = (Name argname, None, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let rel, _ = interp_constr_evars_impls ~evdref:isevars env r in
  let relty = Typing.type_of env !isevars rel in
  let relargty =
    let error () =
      user_err_loc (constr_loc r,
		    "Command.build_wellfounded",
		    Printer.pr_constr_env env rel ++ str " is not an homogeneous binary relation.")
    in
      try
	let ctx, ar = Reductionops.splay_prod_n env !isevars 2 relty in
	  match ctx, kind_of_term ar with
	  | [(_, None, t); (_, None, u)], Sort (Prop Null)
	      when Reductionops.is_conv env !isevars t u -> t
	  | _, _ -> error ()
      with _ -> error ()
  in
  let measure = interp_casted_constr_evars isevars binders_env measure relargty in
  let wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let comb = constr_of_global (delayed_force measure_on_R_ref) in
    let wf_rel = mkApp (comb, [| argtyp; relargty; rel; measure |]) in
    let wf_rel_fun x y =
      mkApp (rel, [| subst1 x measure_body;
 		     subst1 y measure_body |])
    in wf_rel, wf_rel_fun, measure
  in
  let wf_proof = mkApp (delayed_force well_founded, [| argtyp ; wf_rel |]) in
  let argid' = id_of_string (string_of_id argname ^ "'") in
  let wfarg len = (Name argid', None,
  		   mkSubset (Name argid') argtyp
		    (wf_rel_fun (mkRel 1) (mkRel (len + 1))))
  in
  let intern_bl = wfarg 1 :: [arg] in
  let _intern_env = push_rel_context intern_bl env in
  let proj = (delayed_force build_sigma).Coqlib.proj1 in
  let wfargpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel 3)) in
  let projection = (* in wfarg :: arg :: before *)
    mkApp (proj, [| argtyp ; wfargpred ; mkRel 1 |])
  in
  let top_arity_let = it_mkLambda_or_LetIn top_arity letbinders in
  let intern_arity = substl [projection] top_arity_let in
  (* substitute the projection of wfarg for something,
     now intern_arity is in wfarg :: arg *)
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfarg 1] in
  let intern_fun_binder = (Name (add_suffix recname "'"), None, intern_fun_arity_prod) in
  let curry_fun =
    let wfpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let arg = mkApp ((delayed_force build_sigma).intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = (Name (id_of_string "recproof"), None, rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
      (Name recname, Some body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = Termops.lift_rel_context 1 letbinders in
  let intern_body =
    let ctx = (Name recname, None, pi3 curry_fun) :: binders_rel in
    let (r, l, impls, scopes) =
      Constrintern.compute_internalization_data env
	Constrintern.Recursive full_arity impls 
    in
    let newimpls = Idmap.singleton recname
      (r, l, impls @ [(Some (id_of_string "recproof", Impargs.Manual, (true, false)))],
       scopes @ [None]) in
      interp_casted_constr_evars isevars ~impls:newimpls
	(push_rel_context ctx env) body (lift 1 top_arity)
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (Name argname, argtyp, top_arity_let) in
  let def =
    mkApp (constr_of_global (delayed_force fix_sub_ref),
	  [| argtyp ; wf_rel ;
	     Evarutil.e_new_evar isevars env 
	       ~src:(dummy_loc, Evd.QuestionMark (Evd.Define false)) wf_proof;
	     prop ; intern_body_lam |])
  in
  let _ = isevars := Evarutil.nf_evar_map !isevars in
  let binders_rel = nf_evar_context !isevars binders_rel in
  let binders = nf_evar_context !isevars binders in
  let top_arity = Evarutil.nf_evar !isevars top_arity in
  let hook, recname, typ = 
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      let hook l gr = 
	let body = it_mkLambda_or_LetIn (mkApp (constr_of_global gr, [|make|])) binders_rel in
	let ty = it_mkProd_or_LetIn top_arity binders_rel in
	let ce =
          { const_entry_body = Evarutil.nf_evar !isevars body;
            const_entry_secctx = None;
	    const_entry_type = Some ty;
	    const_entry_opaque = false }
	in 
	let c = Declare.declare_constant recname (DefinitionEntry ce, IsDefinition Definition) in
	let gr = ConstRef c in
	  if Impargs.is_implicit_args () || impls <> [] then
	    Impargs.declare_manual_implicits false gr [impls]
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
	hook, name, typ
    else 
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook l gr = 
	if Impargs.is_implicit_args () || impls <> [] then
	  Impargs.declare_manual_implicits false gr [impls]
      in hook, recname, typ
  in
  let fullcoqc = Evarutil.nf_evar !isevars def in
  let fullctyp = Evarutil.nf_evar !isevars typ in
  Obligations.check_evars env !isevars;
  let evars, _, evars_def, evars_typ = 
    Obligations.eterm_obligations env recname !isevars 0 fullcoqc fullctyp 
  in
    ignore(Obligations.add_definition recname ~term:evars_def evars_typ evars ~hook)


let interp_recursive isfix fixl notations =
  let env = Global.env() in
  let fixnames = List.map (fun fix -> fix.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let evdref = ref Evd.empty in
  let fixctxs, fiximps, fixannots =
    list_split3 (List.map (interp_fix_context evdref env isfix) fixl) in
  let fixccls = List.map2 (interp_fix_ccl evdref) fixctxs fixl in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let fixtypes = List.map (nf_evar !evdref) fixtypes in
  let rec_sign =
    List.fold_left2 
      (fun env' id t ->
	 if Flags.is_program_mode () then
	   let sort = Retyping.get_type_of env !evdref t in
	   let fixprot =
	     try mkApp (delayed_force fix_proto, [|sort; t|])
	     with e -> t
	   in
	     (id,None,fixprot) :: env'
	 else (id,None,t) :: env')
      [] fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let impls = compute_internalization_env env Recursive fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs =
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
      list_map3 (interp_fix_body evdref env_rec impls) fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd = consider_remaining_unif_problems env_rec !evdref in
  let fixdefs = List.map (Option.map (nf_evar evd)) fixdefs in
  let fixtypes = List.map (nf_evar evd) fixtypes in
  let fixctxnames = List.map (fun (_,ctx) -> List.map pi1 ctx) fixctxs in

  (* Build the fix declaration block *)
  (env,rec_sign,evd), (fixnames,fixdefs,fixtypes), list_combine3 fixctxnames fiximps fixannots

let check_recursive isfix ((env,rec_sign,evd),(fixnames,fixdefs,fixtypes),info) =
  let evd = Typeclasses.resolve_typeclasses ~with_goals:false ~fail:true env evd in
  List.iter (Option.iter (check_evars (push_named_context rec_sign env) Evd.empty evd)) fixdefs;
  List.iter (check_evars env Evd.empty evd) fixtypes;
  if not (List.mem None fixdefs) then begin
    let fixdefs = List.map Option.get fixdefs in
    check_mutuality env isfix (List.combine fixnames fixdefs)
  end;
  ((fixnames,fixdefs,fixtypes),info)

let interp_fixpoint l ntns = check_recursive true (interp_recursive true l ntns)
let interp_cofixpoint l ntns = check_recursive false (interp_recursive false l ntns)
    
let declare_fixpoint ((fixnames,fixdefs,fixtypes),fiximps) indexes ntns =
  if List.mem None fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      list_map3 (fun id t (len,imps,_) -> (id,(t,(len,imps)))) fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata Tacmach.refine_no_check Tacticals.tclIDTAC)
        fixdefs) in
    Lemmas.start_proof_with_initialization (Global,DefinitionBody Fixpoint)
      (Some(false,indexes,init_tac)) thms None (fun _ _ -> ())
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let indexes = search_guard dummy_loc (Global.env()) indexes fixdecls in
    let fiximps = List.map (fun (n,r,p) -> r) fiximps in
    let fixdecls =
      list_map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 fixnames in
    ignore (list_map4 (declare_fix Fixpoint) fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    fixpoint_message (Some indexes) fixnames;
  end;
  (* Declare notations *)
  List.iter Metasyntax.add_notation_interpretation ntns

let declare_cofixpoint ((fixnames,fixdefs,fixtypes),fiximps) ntns =
  if List.mem None fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      list_map3 (fun id t (len,imps,_) -> (id,(t,(len,imps)))) fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata Tacmach.refine_no_check Tacticals.tclIDTAC)
        fixdefs) in
    Lemmas.start_proof_with_initialization (Global,DefinitionBody CoFixpoint)
      (Some(true,[],init_tac)) thms None (fun _ _ -> ())
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let fixdecls = list_map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 fixnames in
    let fiximps = List.map (fun (len,imps,idx) -> imps) fiximps in
    ignore (list_map4 (declare_fix CoFixpoint) fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    cofixpoint_message fixnames
  end;
  (* Declare notations *)
  List.iter Metasyntax.add_notation_interpretation ntns

let extract_decreasing_argument limit = function
  | (na,CStructRec) -> na
  | (na,_) when not limit -> na
  | _ -> error 
      "Only structural decreasing is supported for a non-Program Fixpoint"

let extract_fixpoint_components limit l =
  let fixl, ntnl = List.split l in
  let fixl = List.map (fun ((_,id),ann,bl,typ,def) ->
    let ann = extract_decreasing_argument limit ann in
      {fix_name = id; fix_annot = ann; fix_binders = bl; fix_body = def; fix_type = typ}) fixl in
  fixl, List.flatten ntnl

let extract_cofixpoint_components l =
  let fixl, ntnl = List.split l in
  List.map (fun ((_,id),bl,typ,def) ->
    {fix_name = id; fix_annot = None; fix_binders = bl; fix_body = def; fix_type = typ}) fixl,
  List.flatten ntnl

let check_program_evars env initial_sigma evd c =
  let sigma =  evd in
  let c = nf_evar sigma c in
  let rec proc_rec c =
    match kind_of_term c with
      | Evar (evk,args) ->
          assert (Evd.mem sigma evk);
	  if not (Evd.mem initial_sigma evk) then
            let (loc,k) = Evd.evar_source evk evd in
	      (match k with
	      | Evd.QuestionMark _
	      | Evd.ImplicitArg (_, _, false) -> ()
	      | _ ->
		  let evi = nf_evar_info sigma (Evd.find sigma evk) in
		    Pretype_errors.error_unsolvable_implicit loc env sigma evi k None)
      | _ -> iter_constr proc_rec c
  in proc_rec c

let out_def = function
  | Some def -> def
  | None -> error "Program Fixpoint needs defined bodies."

let do_program_recursive fixkind fixl ntns =
  let isfix = fixkind <> Obligations.IsCoFixpoint in
  let (env, rec_sign, evd), fix, info = 
    interp_recursive isfix fixl ntns 
  in
    (* Program-specific code *)
    (* Get the interesting evars, those that were not instanciated *)
  let evd = Typeclasses.resolve_typeclasses ~with_goals:false ~fail:true env evd in
    (* Solve remaining evars *)
  let rec collect_evars id def typ imps =
    (* Generalize by the recursive prototypes  *)
    let def =
      Termops.it_mkNamedLambda_or_LetIn def rec_sign
    and typ =
      Termops.it_mkNamedProd_or_LetIn typ rec_sign
    in
    let evars, _, def, typ = 
      Obligations.eterm_obligations env id evd 
	(List.length rec_sign) 
	(nf_evar evd def) (nf_evar evd typ)
    in (id, def, typ, imps, evars)
  in
  let (fixnames,fixdefs,fixtypes) = fix in
  let fiximps = List.map pi2 info in
  let fixdefs = List.map Option.get fixdefs in
  let defs = list_map4 collect_evars fixnames fixdefs fixtypes fiximps in
    if isfix then begin
      let possible_indexes = List.map compute_possible_guardness_evidences info in
      let fixdecls = Array.of_list (List.map (fun x -> Name x) fixnames),
	Array.of_list fixtypes,
	Array.of_list (List.map (subst_vars (List.rev fixnames)) fixdefs)
      in
      let indexes = 
	Pretyping.search_guard dummy_loc (Global.env ()) possible_indexes fixdecls in
	list_iter_i (fun i _ -> Inductive.check_fix env ((indexes,i),fixdecls)) fixl
    end;
    Obligations.add_mutual_definitions defs ntns fixkind

let do_program_fixpoint l =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
    match g, l with
    | [(n, CWfRec r)], [(((_,id),_,bl,typ,def),ntn)] ->
	let recarg = 
	  match n with
	  | Some n -> mkIdentC (snd n)
	  | None ->
	      errorlabstrm "do_program_fixpoint"
		(str "Recursive argument required for well-founded fixpoints")
	in build_wellfounded (id, n, bl, typ, out_def def) r recarg ntn
	     
    | [(n, CMeasureRec (m, r))], [(((_,id),_,bl,typ,def),ntn)] ->
	build_wellfounded (id, n, bl, typ, out_def def)
	  (Option.default (CRef lt_ref) r) m ntn
	  
    | _, _ when List.for_all (fun (n, ro) -> ro = CStructRec) g ->
	let fixl,ntns = extract_fixpoint_components true l in
	let fixkind = Obligations.IsFixpoint g in
	  do_program_recursive fixkind fixl ntns

    | _, _ ->
	errorlabstrm "do_program_fixpoint"
	  (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let do_fixpoint l =
  if Flags.is_program_mode () then do_program_fixpoint l else
  let fixl,ntns = extract_fixpoint_components true l in
  let fix = interp_fixpoint fixl ntns in
  let possible_indexes =
    List.map compute_possible_guardness_evidences (snd fix) in
  declare_fixpoint fix possible_indexes ntns

let do_cofixpoint l =
  let fixl,ntns = extract_cofixpoint_components l in
    if Flags.is_program_mode () then
      do_program_recursive Obligations.IsCoFixpoint fixl ntns
    else
      let cofix = interp_cofixpoint fixl ntns in
	declare_cofixpoint cofix ntns
