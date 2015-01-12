(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util
open Flags
open Term
open Vars
open Context
open Termops
open Entries
open Environ
open Redexpr
open Declare
open Names
open Libnames
open Globnames
open Nameops
open Constrexpr
open Constrexpr_ops
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
open Indschemes
open Misctypes
open Vernacexpr

let do_universe l = Declare.do_universe l  
let do_constraint l = Declare.do_constraint l

let rec under_binders env f n c =
  if Int.equal n 0 then snd (f env Evd.empty c) else
    match kind_of_term c with
      | Lambda (x,t,c) ->
	  mkLambda (x,t,under_binders (push_rel (x,None,t) env) f (n-1) c)
      | LetIn (x,b,t,c) ->
	  mkLetIn (x,b,t,under_binders (push_rel (x,Some b,t) env) f (n-1) c)
      | _ -> assert false

let rec complete_conclusion a cs = function
  | CProdN (loc,bl,c) -> CProdN (loc,bl,complete_conclusion a cs c)
  | CLetIn (loc,b,t,c) -> CLetIn (loc,b,t,complete_conclusion a cs c)
  | CHole (loc, k, _, _) ->
      let (has_no_args,name,params) = a in
      if not has_no_args then
	user_err_loc (loc,"",
	  strbrk"Cannot infer the non constant arguments of the conclusion of "
	  ++ pr_id cs ++ str ".");
      let args = List.map (fun id -> CRef(Ident(loc,id),None)) params in
      CAppExpl (loc,(None,Ident(loc,name),None),List.rev args)
  | c -> c

(* Commands of the interface *)

(* 1| Constant definitions *)

let red_constant_entry n ce = function
  | None -> ce
  | Some red ->
      let proof_out = ce.const_entry_body in
      let env = Global.env () in
      { ce with const_entry_body = Future.chain ~greedy:true ~pure:true proof_out
        (fun ((body,ctx),eff) ->
          (under_binders env
             (fst (reduction_of_red_expr env red)) n body,ctx),eff) }

let interp_definition bl p red_option c ctypopt =
  let env = Global.env() in
  let evdref = ref (Evd.from_env env) in
  let impls, ((env_bl, ctx), imps1) = interp_context_evars env evdref bl in
  let nb_args = List.length ctx in
  let imps,ce =
    match ctypopt with
      None ->
        let subst = evd_comb0 Evd.nf_univ_variables evdref in
	let ctx = map_rel_context (Vars.subst_univs_constr subst) ctx in
	let env_bl = push_rel_context ctx env in
	let c, imps2 = interp_constr_evars_impls ~impls env_bl evdref c in
        let nf,subst = Evarutil.e_nf_evars_and_universes evdref in
        let body = nf (it_mkLambda_or_LetIn c ctx) in
	let vars = Universes.universes_of_constr body in
	let ctx = Universes.restrict_universe_context
	  (Evd.universe_context_set !evdref) vars in
 	imps1@(Impargs.lift_implicits nb_args imps2),
	  definition_entry ~univs:(Univ.ContextSet.to_context ctx) ~poly:p body
    | Some ctyp ->
	let ty, impsty = interp_type_evars_impls ~impls env_bl evdref ctyp in
	let subst = evd_comb0 Evd.nf_univ_variables evdref in
	let ctx = map_rel_context (Vars.subst_univs_constr subst) ctx in
	let env_bl = push_rel_context ctx env in
	let c, imps2 = interp_casted_constr_evars_impls ~impls env_bl evdref c ty in
	let nf, subst = Evarutil.e_nf_evars_and_universes evdref in
	let body = nf (it_mkLambda_or_LetIn c ctx) in
	let typ = nf (it_mkProd_or_LetIn ty ctx) in
        let beq b1 b2 = if b1 then b2 else not b2 in
        let impl_eq (x,y,z) (x',y',z') = beq x x' && beq y y' && beq z z' in
	(* Check that all implicit arguments inferable from the term
           are inferable from the type *)
        let chk (key,va) =
          impl_eq (List.assoc_f Pervasives.(=) key impsty) va (* FIXME *)
        in
	if not (try List.for_all chk imps2 with Not_found -> false)
	then msg_warning
          (strbrk "Implicit arguments declaration relies on type." ++ spc () ++
	   strbrk "The term declares more implicits than the type here.");
        let vars = Univ.LSet.union (Universes.universes_of_constr body) 
          (Universes.universes_of_constr typ) in
        let ctx = Universes.restrict_universe_context
          (Evd.universe_context_set !evdref) vars in
	imps1@(Impargs.lift_implicits nb_args impsty),
	  definition_entry ~types:typ ~poly:p 
	    ~univs:(Univ.ContextSet.to_context ctx) body
  in
  red_constant_entry (rel_context_length ctx) ce red_option, !evdref, imps

let check_definition (ce, evd, imps) =
  check_evars_are_solved (Global.env ()) evd (Evd.empty,evd);
  ce

let get_locality id = function
| Discharge ->
  (** If a Let is defined outside a section, then we consider it as a local definition *)
  let msg = pr_id id ++ strbrk " is declared as a local definition" in
  let () = msg_warning msg in
  true
| Local -> true
| Global -> false

let declare_global_definition ident ce local k imps =
  let local = get_locality ident local in
  let kn = declare_constant ident ~local (DefinitionEntry ce, IsDefinition k) in
  let gr = ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = definition_message ident in
  gr

let declare_definition_hook = ref ignore
let set_declare_definition_hook = (:=) declare_definition_hook
let get_declare_definition_hook () = !declare_definition_hook

let declare_definition ident (local, p, k) ce imps hook =
  let () = !declare_definition_hook ce in
  let r = match local with
  | Discharge when Lib.sections_are_opened () ->
    let c = SectionLocalDef ce in
    let _ = declare_variable ident (Lib.cwd(), c, IsDefinition k) in
    let () = definition_message ident in
    let gr = VarRef ident in
    let () = maybe_declare_manual_implicits false gr imps in
    let () = if Pfedit.refining () then
      let msg = strbrk "Section definition " ++
        pr_id ident ++ strbrk " is not visible from current goals" in
      msg_warning msg
    in
    gr
  | Discharge | Local | Global ->
    declare_global_definition ident ce local k imps in
  Lemmas.call_hook (Future.fix_exn_of ce.Entries.const_entry_body) hook local r

let _ = Obligations.declare_definition_ref := declare_definition

let do_definition ident k bl red_option c ctypopt hook =
  let (ce, evd, imps as def) = interp_definition bl (pi2 k) red_option c ctypopt in
    if Flags.is_program_mode () then
      let env = Global.env () in
      let (c,ctx), sideff = Future.force ce.const_entry_body in
      assert(Declareops.side_effects_is_empty sideff);
      assert(Univ.ContextSet.is_empty ctx);
      let typ = match ce.const_entry_type with 
	| Some t -> t
	| None -> Retyping.get_type_of env evd c
      in 
      Obligations.check_evars env evd;
      let obls, _, c, cty = 
	Obligations.eterm_obligations env ident evd 0 c typ
      in
      let ctx = Evd.evar_universe_context evd in
	ignore(Obligations.add_definition
          ident ~term:c cty ctx ~implicits:imps ~kind:k ~hook obls)
    else let ce = check_definition def in
      ignore(declare_definition ident k ce imps
        (Lemmas.mk_hook
          (fun l r -> Lemmas.call_hook (fun exn -> exn) hook l r;r)))

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let declare_assumption is_coe (local,p,kind) (c,ctx) imps impl nl (_,ident) = match local with
| Discharge when Lib.sections_are_opened () ->
  let decl = (Lib.cwd(), SectionLocalAssum ((c,ctx),p,impl), IsAssumption kind) in
  let _ = declare_variable ident decl in
  let () = assumption_message ident in
  let () =
    if is_verbose () && Pfedit.refining () then
    msg_warning (str"Variable" ++ spc () ++ pr_id ident ++
    strbrk " is not visible from current goals")
  in
  let r = VarRef ident in
  let () = Typeclasses.declare_instance None true r in
  let () = if is_coe then Class.try_add_new_coercion r ~local:true false in
  (r,Univ.Instance.empty,true)

| Global | Local | Discharge ->
  let local = get_locality ident local in
  let inl = match nl with
    | NoInline -> None
    | DefaultInline -> Some (Flags.get_inline_level())
    | InlineAt i -> Some i
  in
  let ctx = Univ.ContextSet.to_context ctx in
  let decl = (ParameterEntry (None,p,(c,ctx),inl), IsAssumption kind) in
  let kn = declare_constant ident ~local decl in
  let gr = ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = assumption_message ident in
  let () = Typeclasses.declare_instance None false gr in
  let () = if is_coe then Class.try_add_new_coercion gr local p in
  let inst = 
    if p (* polymorphic *) then Univ.UContext.instance ctx 
    else Univ.Instance.empty
  in
    (gr,inst,Lib.is_modtype_strict ())

let interp_assumption evdref env bl c =
  let c = prod_constr_expr c bl in
  let ty, impls = interp_type_evars_impls env evdref c in
  let evd, nf = nf_evars_and_universes !evdref in
  let ctx = Evd.universe_context_set evd in
    ((nf ty, ctx), impls)

let declare_assumptions idl is_coe k c imps impl_is_on nl =
  let refs, status =
    List.fold_left (fun (refs,status) id ->
      let ref',u',status' = declare_assumption is_coe k c imps impl_is_on nl id in
      (ref',u')::refs, status' && status) ([],true) idl in
  List.rev refs, status

let do_assumptions (_, poly, _ as kind) nl l =
  let env = Global.env () in
  let evdref = ref (Evd.from_env env) in
  let l = 
    if poly then
      (* Separate declarations so that A B : Type puts A and B in different levels. *)
      List.fold_right (fun (is_coe,(idl,c)) acc ->
        List.fold_right (fun id acc -> 
	  (is_coe, ([id], c)) :: acc) idl acc)
        l []
    else l
  in
  let _,l = List.fold_map (fun env (is_coe,(idl,c)) ->
    let (t,ctx),imps = interp_assumption evdref env [] c in
    let env =
      push_named_context (List.map (fun (_,id) -> (id,None,t)) idl) env in
      (env,((is_coe,idl),t,(ctx,imps)))) 
    env l 
  in
  let evd = solve_remaining_evars all_and_fail_flags env !evdref (Evd.empty,!evdref) in
  let l = List.map (on_pi2 (nf_evar evd)) l in
  snd (List.fold_left (fun (subst,status) ((is_coe,idl),t,(ctx,imps)) ->
    let t = replace_vars subst t in
    let (refs,status') = declare_assumptions idl is_coe kind (t,ctx) imps false nl in
    let subst' = List.map2 
      (fun (_,id) (c,u) -> (id,Universes.constr_of_global_univ (c,u)))
      idl refs 
    in
      (subst'@subst, status' && status)) ([],true) l)

(* 3a| Elimination schemes for mutual inductive definitions *)

(* 3b| Mutual inductive definitions *)

let push_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_rel (Name id,None,t) env)
    env idl tl

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

type structured_inductive_expr =
  local_binder list * structured_one_inductive_expr list

let minductive_message warn = function
  | []  -> error "No inductive definition."
  | [x] -> (pr_id x ++ str " is defined" ++ 
	    if warn then str " as a non-primitive record" else mt())
  | l   -> hov 0  (prlist_with_sep pr_comma pr_id l ++
		     spc () ++ str "are defined")

let check_all_names_different indl =
  let ind_names = List.map (fun ind -> ind.ind_name) indl in
  let cstr_names = List.map_append (fun ind -> List.map fst ind.ind_lc) indl in
  let l = List.duplicates Id.equal ind_names in
  let () = match l with
  | [] -> ()
  | t :: _ -> raise (InductiveError (SameNamesTypes t))
  in
  let l = List.duplicates Id.equal cstr_names in
  let () = match l with
  | [] -> ()
  | c :: _ -> raise (InductiveError (SameNamesConstructors (List.hd l)))
  in
  let l = List.intersect Id.equal ind_names cstr_names in
  match l with
  | [] -> ()
  | _ -> raise (InductiveError (SameNamesOverlap l))

let mk_mltype_data evdref env assums arity indname =
  let is_ml_type = is_sort env !evdref arity in
  (is_ml_type,indname,assums)

let prepare_param = function
  | (na,None,t) -> out_name na, LocalAssum t
  | (na,Some b,_) -> out_name na, LocalDef b

(** Make the arity conclusion flexible to avoid generating an upper bound universe now,
    only if the universe does not appear anywhere else.
    This is really a hack to stay compatible with the semantics of template polymorphic 
    inductives which are recognized when a "Type" appears at the end of the conlusion in
    the source syntax. *)
    
let rec check_anonymous_type ind =
  let open Glob_term in
    match ind with
    | GSort (_, GType []) -> true
    | GProd (_, _, _, _, e) 
    | GLetIn (_, _, _, e)
    | GLambda (_, _, _, _, e)
    | GApp (_, e, _)
    | GCast (_, e, _) -> check_anonymous_type e
    | _ -> false

let make_conclusion_flexible evdref ty poly =
  if poly && isArity ty then
    let _, concl = destArity ty in
      match concl with
      | Type u -> 
        (match Univ.universe_level u with
        | Some u -> 
	  evdref := Evd.make_flexible_variable !evdref true u
	| None -> ())
      | _ -> ()
  else () 
	
let is_impredicative env u = 
  u = Prop Null || 
  (engagement env = Some Declarations.ImpredicativeSet && u = Prop Pos)

let interp_ind_arity env evdref ind =
  let c = intern_gen IsType env ind.ind_arity in
  let imps = Implicit_quantifiers.implicits_of_glob_constr ~with_products:true c in
  let t, impls = understand_tcc_evars env evdref ~expected_type:IsType c, imps in
  let pseudo_poly = check_anonymous_type c in
  let () = if not (Reduction.is_arity env t) then
    user_err_loc (constr_loc ind.ind_arity, "", str "Not an arity")
  in
    t, pseudo_poly, impls

let interp_cstrs evdref env impls mldata arity ind =
  let cnames,ctyps = List.split ind.ind_lc in
  (* Complete conclusions of constructor types if given in ML-style syntax *)
  let ctyps' = List.map2 (complete_conclusion mldata) cnames ctyps in
  (* Interpret the constructor types *)
  let ctyps'', cimpls = List.split (List.map (interp_type_evars_impls evdref env ~impls) ctyps') in
    (cnames, ctyps'', cimpls)

let sign_level env evd sign =
  fst (List.fold_right
    (fun (_,b,t as d) (lev,env) ->
      match b with
      | Some _ -> (lev, push_rel d env)
      | None ->
	let s = destSort (Reduction.whd_betadeltaiota env 
			    (nf_evar evd (Retyping.get_type_of env evd t)))
	in
	let u = univ_of_sort s in
	  (Univ.sup u lev, push_rel d env))
    sign (Univ.type0m_univ,env))

let sup_list min = List.fold_left Univ.sup min

let extract_level env evd min tys = 
  let sorts = List.map (fun ty -> 
    let ctx, concl = Reduction.dest_prod_assum env ty in
      sign_level env evd ((Anonymous, None, concl) :: ctx)) tys 
  in sup_list min sorts

let inductive_levels env evdref poly arities inds =
  let destarities = List.map (Reduction.dest_arity env) arities in
  let levels = List.map (fun (ctx,a) -> 
    if a = Prop Null then None
    else Some (univ_of_sort a)) destarities
  in
  let cstrs_levels, min_levels, sizes = 
    CList.split3
      (List.map2 (fun (_,tys,_) (ctx,du) -> 
	let len = List.length tys in
	let minlev =
	  if len > 1 && not (is_impredicative env du) then
	    Univ.type0_univ
	  else Univ.type0m_univ
	in
	let clev = extract_level env !evdref minlev tys in
	  (clev, minlev, len)) inds destarities)
  in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = Universes.solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels) (Array.of_list min_levels)
  in
  let evd =
    CList.fold_left3 (fun evd cu (ctx,du) len ->
      if is_impredicative env du then
	(** Any product is allowed here. *)
	evd
      else (** If in a predicative sort, or asked to infer the type,
	       we take the max of:
	       - indices (if in indices-matter mode)
	       - constructors
	       - Type(1) if there is more than 1 constructor
	   *)
	let evd = 
	  (** Indices contribute. *)
	  if Indtypes.is_indices_matter () && List.length ctx > 0 then (
	    let ilev = sign_level env !evdref ctx in
	      Evd.set_leq_sort env evd (Type ilev) du)
	  else evd
	in
        (** Constructors contribute. *)
	let evd = 
	  if Sorts.is_set du then
	    if not (Evd.check_leq evd cu Univ.type0_univ) then 
	      raise (Indtypes.InductiveError Indtypes.LargeNonPropInductiveNotInType)
	    else evd
	  else
	    Evd.set_leq_sort env evd (Type cu) du
	in
	let evd = 
	  if len >= 2 && Univ.is_type0m_univ cu then 
	   (** "Polymorphic" type constraint and more than one constructor, 
	       should not land in Prop. Add constraint only if it would
	       land in Prop directly (no informative arguments as well). *)
	    Evd.set_leq_sort env evd (Prop Pos) du
	  else evd
	in evd)
    !evdref (Array.to_list levels') destarities sizes
  in evdref := evd; arities

let check_named (loc, na) = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err_loc (loc, "", msg)


let check_param = function
| LocalRawDef (na, _) -> check_named na
| LocalRawAssum (nas, Default _, _) -> List.iter check_named nas
| LocalRawAssum (nas, Generalized _, _) -> ()

let interp_mutual_inductive (paramsl,indl) notations poly prv finite =
  check_all_names_different indl;
  List.iter check_param paramsl;
  let env0 = Global.env() in
  let evdref = ref Evd.(from_env env0) in
  let _, ((env_params, ctx_params), userimpls) =
    interp_context_evars env0 evdref paramsl
  in
  let indnames = List.map (fun ind -> ind.ind_name) indl in

  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter(fun (_,b,_) -> Option.is_empty b) ctx_params in
  let params = List.map (fun (na,_,_) -> out_name na) assums in

  (* Interpret the arities *)
  let arities = List.map (interp_ind_arity env_params evdref) indl in

  let fullarities = List.map (fun (c, _, _) -> it_mkProd_or_LetIn c ctx_params) arities in
  let env_ar = push_types env0 indnames fullarities in
  let env_ar_params = push_rel_context ctx_params env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun (_, _, impls) -> userimpls @ 
    lift_implicits (rel_context_nhyps ctx_params) impls) arities in
  let arities = List.map pi1 arities and aritypoly = List.map pi2 arities in
  let impls = compute_internalization_env env0 (Inductive params) indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data evdref env_params params) arities indnames in

  let constructors =
    Metasyntax.with_syntax_protection (fun () ->
     (* Temporary declaration of notations and scopes *)
     List.iter (Metasyntax.set_notation_for_interpretation impls) notations;
     (* Interpret the constructor types *)
     List.map3 (interp_cstrs env_ar_params evdref impls) mldatas arities indl)
     () in

  (* Try further to solve evars, and instantiate them *)
  let sigma = solve_remaining_evars all_and_fail_flags env_params !evdref (Evd.empty,!evdref) in
  evdref := sigma;
  (* Compute renewed arities *)
  let nf,_ = e_nf_evars_and_universes evdref in
  let arities = List.map nf arities in
  let constructors = List.map (fun (idl,cl,impsl) -> (idl,List.map nf cl,impsl)) constructors in
  let _ = List.iter2 (fun ty poly -> make_conclusion_flexible evdref ty poly) arities aritypoly in
  let arities = inductive_levels env_ar_params evdref poly arities constructors in
  let nf',_ = e_nf_evars_and_universes evdref in
  let nf x = nf' (nf x) in
  let arities = List.map nf' arities in
  let constructors = List.map (fun (idl,cl,impsl) -> (idl,List.map nf' cl,impsl)) constructors in
  let ctx_params = map_rel_context nf ctx_params in
  let evd = !evdref in
  List.iter (check_evars env_params Evd.empty evd) arities;
  iter_rel_context (check_evars env0 Evd.empty evd) ctx_params;
  List.iter (fun (_,ctyps,_) ->
    List.iter (check_evars env_ar_params Evd.empty evd) ctyps)
    constructors;

  (* Build the inductive entries *)
  let entries = List.map4 (fun ind arity template (cnames,ctypes,cimpls) -> {
    mind_entry_typename = ind.ind_name;
    mind_entry_arity = arity;
    mind_entry_template = template;
    mind_entry_consnames = cnames;
    mind_entry_lc = ctypes
  }) indl arities aritypoly constructors in
  let impls =
    let len = rel_context_nhyps ctx_params in
      List.map2 (fun indimpls (_,_,cimpls) ->
	indimpls, List.map (fun impls ->
	  userimpls @ (lift_implicits len impls)) cimpls) indimpls constructors
  in
  (* Build the mutual inductive entry *)
  { mind_entry_params = List.map prepare_param ctx_params;
    mind_entry_record = None;
    mind_entry_finite = finite;
    mind_entry_inds = entries;
    mind_entry_polymorphic = poly;
    mind_entry_private = if prv then Some false else None;
    mind_entry_universes = Evd.universe_context evd },
    impls

(* Very syntactical equality *)
let eq_local_binders bl1 bl2 =
  List.equal local_binder_eq bl1 bl2

let extract_coercions indl =
  let mkqid (_,((_,id),_)) = qualid_of_ident id in
  let extract lc = List.filter (fun (iscoe,_) -> iscoe) lc in
  List.map mkqid (List.flatten(List.map (fun (_,_,_,lc) -> extract lc) indl))

let extract_params indl =
  let paramsl = List.map (fun (_,params,_,_) -> params) indl in
  match paramsl with
  | [] -> anomaly (Pp.str "empty list of inductive types")
  | params::paramsl ->
      if not (List.for_all (eq_local_binders params) paramsl) then error
	"Parameters should be syntactically the same for each inductive type.";
      params

let extract_inductive indl =
  List.map (fun ((_,indname),_,ar,lc) -> {
    ind_name = indname;
    ind_arity = Option.cata (fun x -> x) (CSort (Loc.ghost,GType [])) ar;
    ind_lc = List.map (fun (_,((_,id),t)) -> (id,t)) lc
  }) indl

let extract_mutual_inductive_declaration_components indl =
  let indl,ntnl = List.split indl in
  let params = extract_params indl in
  let coes = extract_coercions indl in
  let indl = extract_inductive indl in
  (params,indl), coes, List.flatten ntnl

let is_recursive mie =
  let rec is_recursive_constructor lift typ =
    match Term.kind_of_term typ with
    | Prod (_,arg,rest) ->
        Termops.dependent (mkRel lift) arg ||
        is_recursive_constructor (lift+1) rest
    | LetIn (na,b,t,rest) -> is_recursive_constructor (lift+1) rest
    | _ -> false
  in
  match mie.mind_entry_inds with
  | [ind] ->
      let nparams = List.length mie.mind_entry_params in
      List.exists (fun t -> is_recursive_constructor (nparams+1) t) ind.mind_entry_lc
  | _ -> false

let declare_mutual_inductive_with_eliminations mie impls =
  (* spiwack: raises an error if the structure is supposed to be non-recursive,
        but isn't *)
  begin match mie.mind_entry_finite with
  | BiFinite when is_recursive mie ->
      if Option.has_some mie.mind_entry_record then
        error ("Records declared with the keywords Record or Structure cannot be recursive." ^
                  "You can, however, define recursive records using the Inductive or CoInductive command.")
      else
        error ("Types declared with the keyword Variant cannot be recursive. Recursive types are defined with the Inductive and CoInductive command.")
  | _ -> ()
  end;
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_, kn), prim = declare_mind mie in
  let mind = Global.mind_of_delta_kn kn in
  List.iteri (fun i (indimpls, constrimpls) ->
		   let ind = (mind,i) in
		     maybe_declare_manual_implicits false (IndRef ind) indimpls;
		     List.iteri
		       (fun j impls ->
			  maybe_declare_manual_implicits false (ConstructRef (ind, succ j)) impls)
		       constrimpls)
      impls;
  let warn_prim = match mie.mind_entry_record with Some (Some _) -> not prim | _ -> false in
  if_verbose msg_info (minductive_message warn_prim names);
  if mie.mind_entry_private == None
  then declare_default_schemes mind;
  mind

type one_inductive_impls =
  Impargs.manual_explicitation list (* for inds *)*
  Impargs.manual_explicitation list list (* for constrs *)

let do_mutual_inductive indl poly prv finite =
  let indl,coes,ntns = extract_mutual_inductive_declaration_components indl in
  (* Interpret the types *)
  let mie,impls = interp_mutual_inductive indl ntns poly prv finite in
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (declare_mutual_inductive_with_eliminations mie impls);
  (* Declare the possible notations of inductive types *)
  List.iter Metasyntax.add_notation_interpretation ntns;
  (* Declare the coercions *)
  List.iter (fun qid -> Class.try_add_new_coercion (locate qid) false poly) coes

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

let rec partial_order cmp = function
  | [] -> []
  | (x,xge)::rest ->
    let rec browse res xge' = function
    | [] ->
	let res = List.map (function
	  | (z, Inr zge) when List.mem_f cmp x zge ->
            (z, Inr (List.union cmp zge xge'))
	  | r -> r) res in
	(x,Inr xge')::res
    | y::xge ->
      let rec link y =
	try match List.assoc_f cmp y res with
	| Inl z -> link z
	| Inr yge ->
	  if List.mem_f cmp x yge then
	    let res = List.remove_assoc_f cmp y res in
	    let res = List.map (function
	      | (z, Inl t) ->
		  if cmp t y then (z, Inl x) else (z, Inl t)
	      | (z, Inr zge) ->
		  if List.mem_f cmp y zge then
		    (z, Inr (List.add_set cmp x (List.remove cmp y zge)))
		  else
		    (z, Inr zge)) res in
	    browse ((y,Inl x)::res) xge' (List.union cmp xge (List.remove cmp x yge))
	  else
	    browse res (List.add_set cmp y (List.union cmp xge' yge)) xge
	with Not_found -> browse res (List.add_set cmp y xge') xge
      in link y
    in browse (partial_order cmp rest) [] xge

let non_full_mutual_message x xge y yge isfix rest =
  let reason =
    if Id.List.mem x yge then
      Id.to_string y^" depends on "^Id.to_string x^" but not conversely"
    else if Id.List.mem y xge then
      Id.to_string x^" depends on "^Id.to_string y^" but not conversely"
    else
      Id.to_string y^" and "^Id.to_string x^" are not mutually dependent" in
  let e = if List.is_empty rest then reason else "e.g.: "^reason in
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
      (id, List.filter (fun id' -> not (Id.equal id id') && occur_var env id' def) names))
      fixl in
  let po = partial_order Id.equal preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
	msg_warning (non_full_mutual_message x xge y yge isfix rest)
    | _ -> ()

type structured_fixpoint_expr = {
  fix_name : Id.t;
  fix_annot : Id.t Loc.located option;
  fix_binders : local_binder list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

let interp_fix_context env evdref isfix fix =
  let before, after = if isfix then split_at_annot fix.fix_binders fix.fix_annot else [], fix.fix_binders in
  let impl_env, ((env', ctx), imps) = interp_context_evars env evdref before in
  let impl_env', ((env'', ctx'), imps') = interp_context_evars ~impl_env env' evdref after in
  let annot = Option.map (fun _ -> List.length (assums_of_rel_context ctx)) fix.fix_annot in
    ((env'', ctx' @ ctx), (impl_env',imps @ imps'), annot)

let interp_fix_ccl evdref impls (env,_) fix =
  interp_type_evars_impls ~impls env evdref fix.fix_type

let interp_fix_body env_rec evdref impls (_,ctx) fix ccl =
  Option.map (fun body ->
    let env = push_rel_context ctx env_rec in
    let body = interp_casted_constr_evars env evdref ~impls body ccl in
    it_mkLambda_or_LetIn body ctx) fix.fix_body

let build_fix_type (_,ctx) ccl = it_mkProd_or_LetIn ccl ctx

let declare_fix (_,poly,_ as kind) ctx f ((def,_),eff) t imps =
  let ce = definition_entry ~types:t ~poly ~univs:ctx ~eff def in
  declare_definition f kind ce imps (Lemmas.mk_hook (fun _ r -> r))

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
      List.interval 0 (List.length ids - 1)

type recursive_preentry =
  Id.t list * constr option list * types list

(* Wellfounded definition *)

open Coqlib

let contrib_name = "Program"
let subtac_dir = [contrib_name]
let fixsub_module = subtac_dir @ ["Wf"]
let tactics_module = subtac_dir @ ["Tactics"]

let init_reference dir s () = Coqlib.gen_reference "Command" dir s
let init_constant dir s () = Coqlib.gen_constant "Command" dir s
let make_ref l s = init_reference l s
let fix_proto = init_constant tactics_module "fix_proto"
let fix_sub_ref = make_ref fixsub_module "Fix_sub"
let measure_on_R_ref = make_ref fixsub_module "MR"
let well_founded = init_constant ["Init"; "Wf"] "well_founded"
let mkSubset name typ prop =
  mkApp (Universes.constr_of_global (delayed_force build_sigma).typ,
	 [| typ; mkLambda (name, typ, prop) |])
let sigT = Lazy.lazy_from_fun build_sigma_type

let make_qref s = Qualid (Loc.ghost, qualid_of_string s)
let lt_ref = make_qref "Init.Peano.lt"

let rec telescope = function
  | [] -> assert false
  | [(n, None, t)] -> t, [n, Some (mkRel 1), t], mkRel 1
  | (n, None, t) :: tl ->
      let ty, tys, (k, constr) =
	List.fold_left
	  (fun (ty, tys, (k, constr)) (n, b, t) ->
	    let pred = mkLambda (n, t, ty) in
	    let ty = Universes.constr_of_global (Lazy.force sigT).typ in
	    let intro = Universes.constr_of_global (Lazy.force sigT).intro in
	    let sigty = mkApp (ty, [|t; pred|]) in
	    let intro = mkApp (intro, [|lift k t; lift k pred; mkRel k; constr|]) in
	      (sigty, pred :: tys, (succ k, intro)))
	  (t, [], (2, mkRel 1)) tl
      in
      let (last, subst) = List.fold_right2
	(fun pred (n, b, t) (prev, subst) ->
	  let p1 = Universes.constr_of_global (Lazy.force sigT).proj1 in
	  let p2 = Universes.constr_of_global (Lazy.force sigT).proj2 in
	  let proj1 = applistc p1 [t; pred; prev] in
	  let proj2 = applistc p2 [t; pred; prev] in
	    (lift 1 proj2, (n, Some proj1, t) :: subst))
	(List.rev tys) tl (mkRel 1, [])
      in ty, ((n, Some last, t) :: subst), constr

  | (n, Some b, t) :: tl -> let ty, subst, term = telescope tl in
      ty, ((n, Some b, t) :: subst), lift 1 term

let nf_evar_context sigma ctx =
  List.map (fun (n, b, t) ->
    (n, Option.map (Evarutil.nf_evar sigma) b, Evarutil.nf_evar sigma t)) ctx

let build_wellfounded (recname,n,bl,arityc,body) r measure notation =
  Coqlib.check_required_library ["Coq";"Program";"Wf"];
  let env = Global.env() in
  let evdref = ref (Evd.from_env env) in
  let _, ((env', binders_rel), impls) = interp_context_evars env evdref bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let top_arity = interp_type_evars top_env evdref arityc in
  let full_arity = it_mkProd_or_LetIn top_arity binders_rel in
  let argtyp, letbinders, make = telescope binders_rel in
  let argname = Id.of_string "recarg" in
  let arg = (Name argname, None, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let rel, _ = interp_constr_evars_impls env evdref r in
  let () = check_evars_are_solved env !evdref (Evd.empty,!evdref)  in
  let relty = Typing.type_of env !evdref rel in
  let relargty =
    let error () =
      user_err_loc (constr_loc r,
		    "Command.build_wellfounded",
		    Printer.pr_constr_env env !evdref rel ++ str " is not an homogeneous binary relation.")
    in
      try
	let ctx, ar = Reductionops.splay_prod_n env !evdref 2 relty in
	  match ctx, kind_of_term ar with
	  | [(_, None, t); (_, None, u)], Sort (Prop Null)
	      when Reductionops.is_conv env !evdref t u -> t
	  | _, _ -> error ()
      with e when Errors.noncritical e -> error ()
  in
  let measure = interp_casted_constr_evars binders_env evdref measure relargty in
  let wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let comb = Universes.constr_of_global (delayed_force measure_on_R_ref) in
    let wf_rel = mkApp (comb, [| argtyp; relargty; rel; measure |]) in
    let wf_rel_fun x y =
      mkApp (rel, [| subst1 x measure_body;
 		     subst1 y measure_body |])
    in wf_rel, wf_rel_fun, measure
  in
  let wf_proof = mkApp (delayed_force well_founded, [| argtyp ; wf_rel |]) in
  let argid' = Id.of_string (Id.to_string argname ^ "'") in
  let wfarg len = (Name argid', None,
  		   mkSubset (Name argid') argtyp
		    (wf_rel_fun (mkRel 1) (mkRel (len + 1))))
  in
  let intern_bl = wfarg 1 :: [arg] in
  let _intern_env = push_rel_context intern_bl env in
  let proj = (*FIXME*)Universes.constr_of_global (delayed_force build_sigma).Coqlib.proj1 in
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
    let intro = (*FIXME*)Universes.constr_of_global (delayed_force build_sigma).Coqlib.intro in
    let arg = mkApp (intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = (Name (Id.of_string "recproof"), None, rcurry) in
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
    let newimpls = Id.Map.singleton recname
      (r, l, impls @ [(Some (Id.of_string "recproof", Impargs.Manual, (true, false)))],
       scopes @ [None]) in
      interp_casted_constr_evars (push_rel_context ctx env) evdref
        ~impls:newimpls body (lift 1 top_arity)
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (Name argname, argtyp, top_arity_let) in
  let def =
    mkApp (Universes.constr_of_global (delayed_force fix_sub_ref),
	  [| argtyp ; wf_rel ;
	     Evarutil.e_new_evar env evdref
	       ~src:(Loc.ghost, Evar_kinds.QuestionMark (Evar_kinds.Define false)) wf_proof;
	     prop |])
  in
  let def = Typing.solve_evars env evdref def in
  let _ = evdref := Evarutil.nf_evar_map !evdref in
  let def = mkApp (def, [|intern_body_lam|]) in
  let binders_rel = nf_evar_context !evdref binders_rel in
  let binders = nf_evar_context !evdref binders in
  let top_arity = Evarutil.nf_evar !evdref top_arity in
  let hook, recname, typ = 
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      let hook l gr = 
	let body = it_mkLambda_or_LetIn (mkApp (Universes.constr_of_global gr, [|make|])) binders_rel in
	let ty = it_mkProd_or_LetIn top_arity binders_rel in
	let univs = Evd.universe_context !evdref in
	  (*FIXME poly? *)
	let ce = definition_entry ~types:ty ~univs (Evarutil.nf_evar !evdref body) in
	(** FIXME: include locality *)
	let c = Declare.declare_constant recname (DefinitionEntry ce, IsDefinition Definition) in
	let gr = ConstRef c in
	  if Impargs.is_implicit_args () || not (List.is_empty impls) then
	    Impargs.declare_manual_implicits false gr [impls]
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
	hook, name, typ
    else 
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook l gr = 
	if Impargs.is_implicit_args () || not (List.is_empty impls) then
	  Impargs.declare_manual_implicits false gr [impls]
      in hook, recname, typ
  in
  let hook = Lemmas.mk_hook hook in
  let fullcoqc = Evarutil.nf_evar !evdref def in
  let fullctyp = Evarutil.nf_evar !evdref typ in
  Obligations.check_evars env !evdref;
  let evars, _, evars_def, evars_typ = 
    Obligations.eterm_obligations env recname !evdref 0 fullcoqc fullctyp 
  in
  let ctx = Evd.evar_universe_context !evdref in
    ignore(Obligations.add_definition recname ~term:evars_def 
	     evars_typ ctx evars ~hook)

let interp_recursive isfix fixl notations =
  let env = Global.env() in
  let fixnames = List.map (fun fix -> fix.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let evdref = ref (Evd.from_env env) in
  let fixctxs, fiximppairs, fixannots =
    List.split3 (List.map (interp_fix_context env evdref isfix) fixl) in
  let fixctximpenvs, fixctximps = List.split fiximppairs in
  let fixccls,fixcclimps = List.split (List.map3 (interp_fix_ccl evdref) fixctximpenvs fixctxs fixl) in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let fixtypes = List.map (nf_evar !evdref) fixtypes in
  let fiximps = List.map3
    (fun ctximps cclimps (_,ctx) -> ctximps@(Impargs.lift_implicits (List.length ctx) cclimps))
    fixctximps fixcclimps fixctxs in
  let rec_sign =
    List.fold_left2
      (fun env' id t ->
	 if Flags.is_program_mode () then
	   let sort = Evarutil.evd_comb1 (Typing.e_type_of ~refresh:true env) evdref t in
	   let fixprot =
	     try 
	       let app = mkApp (delayed_force fix_proto, [|sort; t|]) in
		 Typing.solve_evars env evdref app
	     with e  when Errors.noncritical e -> t
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
      List.map4
	(fun fixctximpenv -> interp_fix_body env_rec evdref (Id.Map.fold Id.Map.add fixctximpenv impls))
	fixctximpenvs fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd = consider_remaining_unif_problems env_rec !evdref in
  let evd, nf = nf_evars_and_universes evd in
  let fixdefs = List.map (Option.map nf) fixdefs in
  let fixtypes = List.map nf fixtypes in
  let fixctxnames = List.map (fun (_,ctx) -> List.map pi1 ctx) fixctxs in

  (* Build the fix declaration block *)
  (env,rec_sign,evd), (fixnames,fixdefs,fixtypes), List.combine3 fixctxnames fiximps fixannots

let check_recursive isfix env evd (fixnames,fixdefs,_) =
  check_evars_are_solved env evd (Evd.empty,evd);
  if List.for_all Option.has_some fixdefs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_mutuality env isfix (List.combine fixnames fixdefs)
  end

let interp_fixpoint l ntns =
  let (env,_,evd),fix,info = interp_recursive true l ntns in
  check_recursive true env evd fix;
  (fix,Evd.evar_universe_context evd,info)

let interp_cofixpoint l ntns =
  let (env,_,evd),fix,info = interp_recursive false l ntns in
  check_recursive false  env evd fix;
  fix,Evd.evar_universe_context evd,info
    
let declare_fixpoint local poly ((fixnames,fixdefs,fixtypes),ctx,fiximps) indexes ntns =
  if List.exists Option.is_empty fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      List.map3 (fun id t (len,imps,_) -> (id,(t,(len,imps)))) fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata Tacmach.refine_no_check Tacticals.tclIDTAC)
        fixdefs) in
    let init_tac =
      Option.map (List.map Proofview.V82.tactic) init_tac
    in
    let evd = Evd.from_env ~ctx Environ.empty_env in
    Lemmas.start_proof_with_initialization (Global,poly,DefinitionBody Fixpoint)
      evd (Some(false,indexes,init_tac)) thms None (Lemmas.mk_hook (fun _ _ -> ()))
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let env = Global.env() in
    let indexes = search_guard Loc.ghost env indexes fixdecls in
    let fiximps = List.map (fun (n,r,p) -> r) fiximps in
    let vars = Universes.universes_of_constr (mkFix ((indexes,0),fixdecls)) in
    let fixdecls =
      List.map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 fixnames in
    let ctx = Evd.evar_universe_context_set ctx in
    let ctx = Universes.restrict_universe_context ctx vars in
    let fixdecls = List.map Term_typing.mk_pure_proof fixdecls in
    let ctx = Univ.ContextSet.to_context ctx in
    ignore (List.map4 (declare_fix (local, poly, Fixpoint) ctx)
	      fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    fixpoint_message (Some indexes) fixnames;
  end;
  (* Declare notations *)
  List.iter Metasyntax.add_notation_interpretation ntns

let declare_cofixpoint local poly ((fixnames,fixdefs,fixtypes),ctx,fiximps) ntns =
  if List.exists Option.is_empty fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      List.map3 (fun id t (len,imps,_) -> (id,(t,(len,imps)))) fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata Tacmach.refine_no_check Tacticals.tclIDTAC)
        fixdefs) in
    let init_tac =
      Option.map (List.map Proofview.V82.tactic) init_tac
    in
    let evd = Evd.from_env ~ctx Environ.empty_env in
    Lemmas.start_proof_with_initialization (Global,poly, DefinitionBody CoFixpoint)
      evd (Some(true,[],init_tac)) thms None (Lemmas.mk_hook (fun _ _ -> ()))
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let fixdecls = List.map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 fixnames in
    let fixdecls = List.map Term_typing.mk_pure_proof fixdecls in
    let fiximps = List.map (fun (len,imps,idx) -> imps) fiximps in
    let ctx = Evd.evar_universe_context_set ctx in
    let ctx = Univ.ContextSet.to_context ctx in
    ignore (List.map4 (declare_fix (local, poly, CoFixpoint) ctx) 
	      fixnames fixdecls fixtypes fiximps);
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

let out_def = function
  | Some def -> def
  | None -> error "Program Fixpoint needs defined bodies."

let do_program_recursive local p fixkind fixl ntns =
  let isfix = fixkind != Obligations.IsCoFixpoint in
  let (env, rec_sign, evd), fix, info = 
    interp_recursive isfix fixl ntns 
  in
    (* Program-specific code *)
    (* Get the interesting evars, those that were not instanciated *)
  let evd = Typeclasses.resolve_typeclasses ~filter:Typeclasses.no_goals ~fail:true env evd in
    (* Solve remaining evars *)
  let evd = nf_evar_map_undefined evd in
  let collect_evars id def typ imps =
    (* Generalize by the recursive prototypes  *)
    let def =
      nf_evar evd (Termops.it_mkNamedLambda_or_LetIn def rec_sign)
    and typ =
      nf_evar evd (Termops.it_mkNamedProd_or_LetIn typ rec_sign)
    in
    let evars, _, def, typ = 
      Obligations.eterm_obligations env id evd
	(List.length rec_sign) def typ
    in (id, def, typ, imps, evars)
  in
  let (fixnames,fixdefs,fixtypes) = fix in
  let fiximps = List.map pi2 info in
  let fixdefs = List.map out_def fixdefs in
  let defs = List.map4 collect_evars fixnames fixdefs fixtypes fiximps in
  let () = if isfix then begin
      let possible_indexes = List.map compute_possible_guardness_evidences info in
      let fixdecls = Array.of_list (List.map (fun x -> Name x) fixnames),
	Array.of_list fixtypes,
	Array.of_list (List.map (subst_vars (List.rev fixnames)) fixdefs)
      in
      let indexes = 
	Pretyping.search_guard Loc.ghost (Global.env ()) possible_indexes fixdecls in
	List.iteri (fun i _ -> Inductive.check_fix env ((indexes,i),fixdecls)) fixl
  end in
  let ctx = Evd.evar_universe_context evd in
  let kind = match fixkind with
  | Obligations.IsFixpoint _ -> (local, p, Fixpoint)
  | Obligations.IsCoFixpoint -> (local, p, CoFixpoint)
  in
  Obligations.add_mutual_definitions defs ~kind ctx ntns fixkind

let do_program_fixpoint local poly l =
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
	  (Option.default (CRef (lt_ref,None)) r) m ntn
	  
    | _, _ when List.for_all (fun (n, ro) -> ro == CStructRec) g ->
	let fixl,ntns = extract_fixpoint_components true l in
	let fixkind = Obligations.IsFixpoint g in
	  do_program_recursive local poly fixkind fixl ntns

    | _, _ ->
	errorlabstrm "do_program_fixpoint"
	  (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let do_fixpoint local poly l =
  if Flags.is_program_mode () then do_program_fixpoint local poly l
  else
    let fixl, ntns = extract_fixpoint_components true l in
    let fix = interp_fixpoint fixl ntns in
    let possible_indexes =
      List.map compute_possible_guardness_evidences (pi3 fix) in
    declare_fixpoint local poly fix possible_indexes ntns

let do_cofixpoint local poly l =
  let fixl,ntns = extract_cofixpoint_components l in
    if Flags.is_program_mode () then
      do_program_recursive local poly Obligations.IsCoFixpoint fixl ntns
    else
      let cofix = interp_cofixpoint fixl ntns in
	declare_cofixpoint local poly cofix ntns
