(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
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

let interp_definition boxed bl red_option c ctypopt =
  let env = Global.env() in
  let evdref = ref Evd.empty in
  let (env_bl, ctx), imps1 =
    interp_context_evars ~fail_anonymous:false evdref env bl in
  let imps,ce =
    match ctypopt with
      None ->
	let c, imps2 = interp_constr_evars_impls ~evdref ~fail_evar:false env_bl c in
	let body = nf_evar !evdref (it_mkLambda_or_LetIn c ctx) in
	check_evars env Evd.empty !evdref body;
	imps1@imps2,
	{ const_entry_body = body;
	  const_entry_type = None;
          const_entry_opaque = false;
	  const_entry_boxed = boxed }
    | Some ctyp ->
	let ty, impls = interp_type_evars_impls ~evdref ~fail_evar:false env_bl ctyp in
	let c, imps2 = interp_casted_constr_evars_impls ~evdref ~fail_evar:false env_bl c ty in
	let body = nf_evar !evdref (it_mkLambda_or_LetIn c ctx) in
	let typ = nf_evar !evdref (it_mkProd_or_LetIn ty ctx) in
	check_evars env Evd.empty !evdref body;
	check_evars env Evd.empty !evdref typ;
	imps1@imps2,
	{ const_entry_body = body;
	  const_entry_type = Some typ;
          const_entry_opaque = false;
	  const_entry_boxed = boxed }
  in
  red_constant_entry (rel_context_length ctx) ce red_option, imps

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
          SectionLocalDef(ce.const_entry_body,ce.const_entry_type,false) in
        let _ = declare_variable ident (Lib.cwd(),c,IsDefinition k) in
        definition_message ident;
        if Pfedit.refining () then
          Flags.if_verbose msg_warning
	    (str"Local definition " ++ pr_id ident ++
             str" is not visible from current goals");
        VarRef ident
    | (Global|Local) ->
        declare_global_definition ident ce local k imps in
  hook local r

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
	Autoinstance.search_declaration (ConstRef kn);
        gr in
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
  let (env_params, ctx_params), userimpls =
    interp_context_evars ~fail_anonymous:false evdref env0 paramsl
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
  let indimpls = List.map (fun (_, impls) -> userimpls @ lift_implicits (List.length userimpls) impls) arities in
  let arities = List.map fst arities in
  let impls = compute_full_internalization_env env0 Inductive params indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data evdref env_params params) arities indnames in

  let constructors =
    States.with_state_protection (fun () ->
     (* Temporary declaration of notations and scopes *)
     List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
     (* Interpret the constructor types *)
     list_map3 (interp_cstrs evdref env_ar_params impls) mldatas arities indl)
     () in

  (* Instantiate evars and check all are resolved *)
  let evd = consider_remaining_unif_problems env_params !evdref in
  let evd = Typeclasses.resolve_typeclasses ~onlyargs:false ~fail:true env_params evd in
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
    let len = List.length ctx_params in
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
    ind_arity = Option.cata (fun x -> x) (CSort (dummy_loc, Rawterm.RType None)) ar;
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
  let mind = Global.mind_of_delta (mind_of_kn kn) in
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
	if_verbose msg_warning (non_full_mutual_message x xge y yge isfix rest)
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
  let (env', ctx), imps = interp_context_evars evdref env before in
  let (env'', ctx'), imps' = interp_context_evars evdref env' after in
    ((env'', ctx' @ ctx), imps @ imps', Option.map (fun _ -> List.length ctx) fix.fix_annot)
      
let interp_fix_ccl evdref (env,_) fix =
  interp_type_evars evdref env fix.fix_type

let interp_fix_body evdref env_rec impls (_,ctx) fix ccl =
  Option.map (fun body ->
    let env = push_rel_context ctx env_rec in
    let body = interp_casted_constr_evars evdref env ~impls body ccl in
    it_mkLambda_or_LetIn body ctx) fix.fix_body

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
  Autoinstance.search_declaration (ConstRef kn);
  maybe_declare_manual_implicits false gr imps;
  gr

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
  let env_rec = push_named_types env fixnames fixtypes in

  (* Get interpretation metadatas *)
  let impls = compute_full_internalization_env env Recursive [] fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs =
    States.with_state_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
      list_map3 (interp_fix_body evdref env_rec impls) fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd = consider_remaining_unif_problems env_rec !evdref in
  let fixdefs = List.map (Option.map (nf_evar evd)) fixdefs in
  let fixtypes = List.map (nf_evar evd) fixtypes in
  let fixctxnames = List.map (fun (_,ctx) -> List.map pi1 ctx) fixctxs in
  let evd = Typeclasses.resolve_typeclasses ~onlyargs:false ~fail:true env evd in
  List.iter (Option.iter (check_evars env_rec Evd.empty evd)) fixdefs;
  List.iter (check_evars env Evd.empty evd) fixtypes;
  if not (List.mem None fixdefs) then begin
    let fixdefs = List.map Option.get fixdefs in
    check_mutuality env isfix (List.combine fixnames fixdefs)
  end;

  (* Build the fix declaration block *)
  (fixnames,fixdefs,fixtypes), list_combine3 fixctxnames fiximps fixannots

let interp_fixpoint = interp_recursive true
let interp_cofixpoint = interp_recursive false

let declare_fixpoint boxed ((fixnames,fixdefs,fixtypes),fiximps) indexes ntns =
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
    ignore (list_map4 (declare_fix boxed Fixpoint) fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    fixpoint_message (Some indexes) fixnames;
  end;
  (* Declare notations *)
  List.iter Metasyntax.add_notation_interpretation ntns

let declare_cofixpoint boxed ((fixnames,fixdefs,fixtypes),fiximps) ntns =
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
    ignore (list_map4 (declare_fix boxed CoFixpoint) fixnames fixdecls fixtypes fiximps);
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

let do_fixpoint l b =
  let fixl,ntns = extract_fixpoint_components true l in
  let fix = interp_fixpoint fixl ntns in
  let possible_indexes =
    List.map compute_possible_guardness_evidences (snd fix) in
  declare_fixpoint b fix possible_indexes ntns

let do_cofixpoint l b =
  let fixl,ntns = extract_cofixpoint_components l in
  declare_cofixpoint b (interp_cofixpoint fixl ntns) ntns
