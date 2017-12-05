(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Sorts
open Util
open Constr
open Vars
open Termops
open Environ
open Redexpr
open Declare
open Names
open Libnames
open Globnames
open Nameops
open Constrexpr
open Constrexpr_ops
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
open Context.Rel.Declaration
open Entries

module RelDecl = Context.Rel.Declaration

let do_universe poly l = Declare.do_universe poly l
let do_constraint poly l = Declare.do_constraint poly l

let rec under_binders env sigma f n c =
  if Int.equal n 0 then f env sigma (EConstr.of_constr c) else
    match Constr.kind c with
      | Lambda (x,t,c) ->
	  mkLambda (x,t,under_binders (push_rel (LocalAssum (x,t)) env) sigma f (n-1) c)
      | LetIn (x,b,t,c) ->
	  mkLetIn (x,b,t,under_binders (push_rel (LocalDef (x,b,t)) env) sigma f (n-1) c)
      | _ -> assert false

let rec complete_conclusion a cs = CAst.map_with_loc (fun ?loc -> function
  | CProdN (bl,c) -> CProdN (bl,complete_conclusion a cs c)
  | CLetIn (na,b,t,c) -> CLetIn (na,b,t,complete_conclusion a cs c)
  | CHole (k, _, _) ->
      let (has_no_args,name,params) = a in
      if not has_no_args then
	user_err ?loc
	 (strbrk"Cannot infer the non constant arguments of the conclusion of "
	  ++ Id.print cs ++ str ".");
      let args = List.map (fun id -> CAst.make ?loc @@ CRef(Ident(loc,id),None)) params in
      CAppExpl ((None,Ident(loc,name),None),List.rev args)
  | c -> c
  )

(* Commands of the interface *)

(* 1| Constant definitions *)

let red_constant_entry n ce sigma = function
  | None -> ce
  | Some red ->
      let proof_out = ce.const_entry_body in
      let env = Global.env () in
      let (redfun, _) = reduction_of_red_expr env red in
      let redfun env sigma c =
        let (_, c) = redfun env sigma c in
        EConstr.Unsafe.to_constr c
      in
      { ce with const_entry_body = Future.chain proof_out
        (fun ((body,ctx),eff) -> (under_binders env sigma redfun n body,ctx),eff) }

let warn_implicits_in_term =
  CWarnings.create ~name:"implicits-in-term" ~category:"implicits"
         (fun () ->
          strbrk "Implicit arguments declaration relies on type." ++ spc () ++
            strbrk "The term declares more implicits than the type here.")
        
let interp_definition pl bl poly red_option c ctypopt =
  let env = Global.env() in
  let evd, decl = Univdecls.interp_univ_decl_opt env pl in
  let evdref = ref evd in
  let impls, ((env_bl, ctx), imps1) = interp_context_evars env evdref bl in
  let ctx = List.map (fun d -> map_rel_decl EConstr.Unsafe.to_constr d) ctx in
  let nb_args = Context.Rel.nhyps ctx in
  let imps,ce =
    match ctypopt with
      None ->
        let subst = evd_comb0 Evd.nf_univ_variables evdref in
	let ctx = Context.Rel.map (Vars.subst_univs_constr subst) ctx in
	let env_bl = push_rel_context ctx env in
	let c, imps2 = interp_constr_evars_impls ~impls env_bl evdref c in
	let c = EConstr.Unsafe.to_constr c in
        let nf,subst = Evarutil.e_nf_evars_and_universes evdref in
        let body = nf (it_mkLambda_or_LetIn c ctx) in
        let vars = EConstr.universes_of_constr !evdref (EConstr.of_constr body) in
        let () = evdref := Evd.restrict_universe_context !evdref vars in
        let uctx = Evd.check_univ_decl ~poly !evdref decl in
        imps1@(Impargs.lift_implicits nb_args imps2),
          definition_entry ~univs:uctx body
    | Some ctyp ->
        let ty, impsty = interp_type_evars_impls ~impls env_bl evdref ctyp in
        let subst = evd_comb0 Evd.nf_univ_variables evdref in
	let ctx = Context.Rel.map (Vars.subst_univs_constr subst) ctx in
	let env_bl = push_rel_context ctx env in
	let c, imps2 = interp_casted_constr_evars_impls ~impls env_bl evdref c ty in
	let c = EConstr.Unsafe.to_constr c in
	let nf, subst = Evarutil.e_nf_evars_and_universes evdref in
	let body = nf (it_mkLambda_or_LetIn c ctx) in
	let ty = EConstr.Unsafe.to_constr ty in
	let typ = nf (Term.it_mkProd_or_LetIn ty ctx) in
        let beq b1 b2 = if b1 then b2 else not b2 in
        let impl_eq (x,y,z) (x',y',z') = beq x x' && beq y y' && beq z z' in
	(* Check that all implicit arguments inferable from the term
           are inferable from the type *)
        let chk (key,va) =
          impl_eq (List.assoc_f Pervasives.(=) key impsty) va (* FIXME *)
        in
	if not (try List.for_all chk imps2 with Not_found -> false)
	then warn_implicits_in_term ();
        let bodyvars = EConstr.universes_of_constr !evdref (EConstr.of_constr body) in
        let tyvars = EConstr.universes_of_constr !evdref (EConstr.of_constr ty) in
        let vars = Univ.LSet.union bodyvars tyvars in
        let () = evdref := Evd.restrict_universe_context !evdref vars in
        let uctx = Evd.check_univ_decl ~poly !evdref decl in
        imps1@(Impargs.lift_implicits nb_args impsty),
          definition_entry ~types:typ ~univs:uctx body
  in
  (red_constant_entry (Context.Rel.length ctx) ce !evdref red_option, !evdref, decl, imps)

let check_definition (ce, evd, _, imps) =
  check_evars_are_solved (Global.env ()) evd Evd.empty;
  ce

let do_definition ident k univdecl bl red_option c ctypopt hook =
  let (ce, evd, univdecl, imps as def) =
    interp_definition univdecl bl (pi2 k) red_option c ctypopt
  in
    if Flags.is_program_mode () then
      let env = Global.env () in
      let (c,ctx), sideff = Future.force ce.const_entry_body in
      assert(Safe_typing.empty_private_constants = sideff);
      assert(Univ.ContextSet.is_empty ctx);
      let typ = match ce.const_entry_type with 
	| Some t -> t
	| None -> EConstr.to_constr evd (Retyping.get_type_of env evd (EConstr.of_constr c))
      in 
      Obligations.check_evars env evd;
      let obls, _, c, cty = 
	Obligations.eterm_obligations env ident evd 0 c typ
      in
      let ctx = Evd.evar_universe_context evd in
      let hook = Lemmas.mk_hook (fun l r _ -> Lemmas.call_hook (fun exn -> exn) hook l r) in
      ignore(Obligations.add_definition
          ident ~term:c cty ctx ~univdecl ~implicits:imps ~kind:k ~hook obls)
    else let ce = check_definition def in
      ignore(DeclareDef.declare_definition ident k ce (Evd.universe_binders evd) imps
        (Lemmas.mk_hook
          (fun l r -> Lemmas.call_hook (fun exn -> exn) hook l r;r)))

(* 2| Variable/Hypothesis/Parameter/Axiom declarations *)

let axiom_into_instance = ref false

let _ =
  let open Goptions in
  declare_bool_option
    { optdepr = false;
      optname = "automatically declare axioms whose type is a typeclass as instances";
      optkey = ["Typeclasses";"Axioms";"Are";"Instances"];
      optread = (fun _ -> !axiom_into_instance);
      optwrite = (:=) axiom_into_instance; }

let should_axiom_into_instance = function
  | Discharge ->
    (* The typeclass behaviour of Variable and Context doesn't depend
       on section status *)
    true
  | Global | Local -> !axiom_into_instance

let declare_assumption is_coe (local,p,kind) (c,ctx) pl imps impl nl (_,ident) =
match local with
| Discharge when Lib.sections_are_opened () ->
  let ctx = match ctx with
    | Monomorphic_const_entry ctx -> ctx
    | Polymorphic_const_entry ctx -> Univ.ContextSet.of_context ctx
  in
  let decl = (Lib.cwd(), SectionLocalAssum ((c,ctx),p,impl), IsAssumption kind) in
  let _ = declare_variable ident decl in
  let () = assumption_message ident in
  let () =
    if not !Flags.quiet && Proof_global.there_are_pending_proofs () then
    Feedback.msg_info (str"Variable" ++ spc () ++ Id.print ident ++
    strbrk " is not visible from current goals")
  in
  let r = VarRef ident in
  let () = Typeclasses.declare_instance None true r in
  let () = if is_coe then Class.try_add_new_coercion r ~local:true false in
  (r,Univ.Instance.empty,true)

| Global | Local | Discharge ->
  let do_instance = should_axiom_into_instance local in
  let local = DeclareDef.get_locality ident ~kind:"axiom" local in
  let inl = match nl with
    | NoInline -> None
    | DefaultInline -> Some (Flags.get_inline_level())
    | InlineAt i -> Some i
  in
  let decl = (ParameterEntry (None,(c,ctx),inl), IsAssumption kind) in
  let kn = declare_constant ident ~local decl in
  let gr = ConstRef kn in
  let () = maybe_declare_manual_implicits false gr imps in
  let () = Declare.declare_univ_binders gr pl in
  let () = assumption_message ident in
  let () = if do_instance then Typeclasses.declare_instance None false gr in
  let () = if is_coe then Class.try_add_new_coercion gr ~local p in
  let inst = match ctx with
    | Polymorphic_const_entry ctx -> Univ.UContext.instance ctx
    | Monomorphic_const_entry _ -> Univ.Instance.empty
  in
    (gr,inst,Lib.is_modtype_strict ())

let interp_assumption evdref env impls bl c =
  let c = mkCProdN ?loc:(local_binders_loc bl) bl c in
  let ty, impls = interp_type_evars_impls env evdref ~impls c in
  let ty = EConstr.Unsafe.to_constr ty in
  (ty, impls)

(* When monomorphic the universe constraints are declared with the first declaration only. *)
let next_uctx =
  let empty_uctx = Monomorphic_const_entry Univ.ContextSet.empty in
  function
  | Polymorphic_const_entry _ as uctx -> uctx
  | Monomorphic_const_entry _ -> empty_uctx

let declare_assumptions idl is_coe k (c,uctx) pl imps nl =
  let refs, status, _ =
    List.fold_left (fun (refs,status,uctx) id ->
      let ref',u',status' =
        declare_assumption is_coe k (c,uctx) pl imps false nl id in
      (ref',u')::refs, status' && status, next_uctx uctx)
      ([],true,uctx) idl
  in
  List.rev refs, status


let maybe_error_many_udecls = function
  | ((loc,id), Some _) ->
    user_err ?loc ~hdr:"many_universe_declarations"
      Pp.(str "When declaring multiple axioms in one command, " ++
          str "only the first is allowed a universe binder " ++
          str "(which will be shared by the whole block).")
  | (_, None) -> ()

let process_assumptions_udecls kind l =
  let udecl, first_id = match l with
    | (coe, ((id, udecl)::rest, c))::rest' ->
      List.iter maybe_error_many_udecls rest;
      List.iter (fun (coe, (idl, c)) -> List.iter maybe_error_many_udecls idl) rest';
      udecl, id
    | (_, ([], _))::_ | [] -> assert false
  in
  let () = match kind, udecl with
    | (Discharge, _, _), Some _ when Lib.sections_are_opened () ->
      let loc = fst first_id in
      let msg = Pp.str "Section variables cannot be polymorphic." in
      user_err ?loc  msg
    | _ -> ()
  in
  udecl, List.map (fun (coe, (idl, c)) -> coe, (List.map fst idl, c)) l

let do_assumptions kind nl l =
  let open Context.Named.Declaration in
  let env = Global.env () in
  let udecl, l = process_assumptions_udecls kind l in
  let evdref, udecl =
    let evd, udecl = Univdecls.interp_univ_decl_opt env udecl in
    ref evd, udecl
  in
  let l =
    if pi2 kind (* poly *) then
      (* Separate declarations so that A B : Type puts A and B in different levels. *)
      List.fold_right (fun (is_coe,(idl,c)) acc ->
        List.fold_right (fun id acc ->
          (is_coe, ([id], c)) :: acc) idl acc)
        l []
    else l
  in
  (* We intepret all declarations in the same evar_map, i.e. as a telescope. *)
  let _,l = List.fold_left_map (fun (env,ienv) (is_coe,(idl,c)) ->
    let t,imps = interp_assumption evdref env ienv [] c in
    let env =
      push_named_context (List.map (fun (_,id) -> LocalAssum (id,t)) idl) env in
    let ienv = List.fold_right (fun (_,id) ienv ->
      let impls = compute_internalization_data env Variable t imps in
      Id.Map.add id impls ienv) idl ienv in
      ((env,ienv),((is_coe,idl),t,imps)))
    (env,empty_internalization_env) l
  in
  let evd = solve_remaining_evars all_and_fail_flags env !evdref Evd.empty in
  (* The universe constraints come from the whole telescope. *)
  let evd = Evd.nf_constraints evd in
  let nf_evar c = EConstr.to_constr evd (EConstr.of_constr c) in
  let uvars, l = List.fold_left_map (fun uvars (coe,t,imps) ->
      let t = nf_evar t in
      let uvars = Univ.LSet.union uvars (Univops.universes_of_constr t) in
      uvars, (coe,t,imps))
      Univ.LSet.empty l
  in
  let evd = Evd.restrict_universe_context evd uvars in
  let uctx = Evd.check_univ_decl ~poly:(pi2 kind) evd udecl in
  let ubinders = Evd.universe_binders evd in
  pi2 (List.fold_left (fun (subst,status,uctx) ((is_coe,idl),t,imps) ->
      let t = replace_vars subst t in
      let refs, status' = declare_assumptions idl is_coe kind (t,uctx) ubinders imps nl in
      let subst' = List.map2
          (fun (_,id) (c,u) -> (id, Universes.constr_of_global_univ (c,u)))
          idl refs
      in
      subst'@subst, status' && status, next_uctx uctx)
    ([], true, uctx) l)

(* 3a| Elimination schemes for mutual inductive definitions *)

(* 3b| Mutual inductive definitions *)

let push_types env idl tl =
  List.fold_left2 (fun env id t -> Environ.push_rel (LocalAssum (Name id,t)) env)
    env idl tl

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_univs : Vernacexpr.universe_decl_expr option;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

type structured_inductive_expr =
  local_binder_expr list * structured_one_inductive_expr list

let minductive_message warn = function
  | []  -> user_err Pp.(str "No inductive definition.")
  | [x] -> (Id.print x ++ str " is defined" ++ 
	    if warn then str " as a non-primitive record" else mt())
  | l   -> hov 0  (prlist_with_sep pr_comma Id.print l ++
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
  let is_ml_type = is_sort env !evdref (EConstr.of_constr arity) in
  (is_ml_type,indname,assums)

let prepare_param = function
  | LocalAssum (na,t) -> Name.get_id na, LocalAssumEntry t
  | LocalDef (na,b,_) -> Name.get_id na, LocalDefEntry b

(** Make the arity conclusion flexible to avoid generating an upper bound universe now,
    only if the universe does not appear anywhere else.
    This is really a hack to stay compatible with the semantics of template polymorphic 
    inductives which are recognized when a "Type" appears at the end of the conlusion in
    the source syntax. *)
    
let rec check_anonymous_type ind =
  let open Glob_term in
    match DAst.get ind with
    | GSort (GType []) -> true
    | GProd ( _, _, _, e) 
    | GLetIn (_, _, _, e)
    | GLambda (_, _, _, e)
    | GApp (e, _)
    | GCast (e, _) -> check_anonymous_type e
    | _ -> false

let make_conclusion_flexible evdref ty poly =
  if poly && Term.isArity ty then
    let _, concl = Term.destArity ty in
      match concl with
      | Type u -> 
        (match Univ.universe_level u with
        | Some u -> 
	  evdref := Evd.make_flexible_variable !evdref ~algebraic:true u
	| None -> ())
      | _ -> ()
  else () 
	
let is_impredicative env u = 
  u = Prop Null || (is_impredicative_set env && u = Prop Pos)

let interp_ind_arity env evdref ind =
  let c = intern_gen IsType env ind.ind_arity in
  let impls = Implicit_quantifiers.implicits_of_glob_constr ~with_products:true c in
  let (evd,t) = understand_tcc env !evdref ~expected_type:IsType c in
  evdref := evd;
  let pseudo_poly = check_anonymous_type c in
  let () = if not (Reductionops.is_arity env !evdref t) then
    user_err ?loc:(constr_loc ind.ind_arity) (str "Not an arity")
  in
  let t = EConstr.Unsafe.to_constr t in
    t, pseudo_poly, impls

let interp_cstrs evdref env impls mldata arity ind =
  let cnames,ctyps = List.split ind.ind_lc in
  (* Complete conclusions of constructor types if given in ML-style syntax *)
  let ctyps' = List.map2 (complete_conclusion mldata) cnames ctyps in
  (* Interpret the constructor types *)
  let ctyps'', cimpls = List.split (List.map (interp_type_evars_impls evdref env ~impls %> on_fst EConstr.Unsafe.to_constr) ctyps') in
    (cnames, ctyps'', cimpls)

let sign_level env evd sign =
  fst (List.fold_right
    (fun d (lev,env) ->
      match d with
      | LocalDef _ -> lev, push_rel d env
      | LocalAssum _ ->
	let s = destSort (Reduction.whd_all env 
			    (EConstr.Unsafe.to_constr (nf_evar evd (Retyping.get_type_of env evd (EConstr.of_constr (RelDecl.get_type d))))))
	in
	let u = univ_of_sort s in
	  (Univ.sup u lev, push_rel d env))
    sign (Univ.type0m_univ,env))

let sup_list min = List.fold_left Univ.sup min

let extract_level env evd min tys = 
  let sorts = List.map (fun ty -> 
    let ctx, concl = Reduction.dest_prod_assum env ty in
      sign_level env evd (LocalAssum (Anonymous, concl) :: ctx)) tys
  in sup_list min sorts

let is_flexible_sort evd u =
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

let inductive_levels env evdref poly arities inds =
  let destarities = List.map (fun x -> x, Reduction.dest_arity env x) arities in
  let levels = List.map (fun (x,(ctx,a)) -> 
    if a = Prop Null then None
    else Some (univ_of_sort a)) destarities
  in
  let cstrs_levels, min_levels, sizes = 
    CList.split3
      (List.map2 (fun (_,tys,_) (arity,(ctx,du)) -> 
	let len = List.length tys in
	let minlev = Sorts.univ_of_sort du in
	let minlev =
	  if len > 1 && not (is_impredicative env du) then
	    Univ.sup minlev Univ.type0_univ
	  else minlev
	in
	let minlev =
	  (** Indices contribute. *)
	  if Indtypes.is_indices_matter () && List.length ctx > 0 then (
	    let ilev = sign_level env !evdref ctx in
	      Univ.sup ilev minlev)
	  else minlev
	in
	let clev = extract_level env !evdref minlev tys in
	  (clev, minlev, len)) inds destarities)
  in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = Universes.solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels) (Array.of_list min_levels)
  in
  let evd, arities =
    CList.fold_left3 (fun (evd, arities) cu (arity,(ctx,du)) len ->
      if is_impredicative env du then
	(** Any product is allowed here. *)
	evd, arity :: arities
      else (** If in a predicative sort, or asked to infer the type,
	       we take the max of:
	       - indices (if in indices-matter mode)
	       - constructors
	       - Type(1) if there is more than 1 constructor
	   *)
        (** Constructors contribute. *)
	let evd = 
	  if Sorts.is_set du then
	    if not (Evd.check_leq evd cu Univ.type0_univ) then 
	      raise (Indtypes.InductiveError Indtypes.LargeNonPropInductiveNotInType)
	    else evd
	  else evd
	    (* Evd.set_leq_sort env evd (Type cu) du *)
	in
	let evd = 
	  if len >= 2 && Univ.is_type0m_univ cu then 
	   (** "Polymorphic" type constraint and more than one constructor, 
	       should not land in Prop. Add constraint only if it would
	       land in Prop directly (no informative arguments as well). *)
	    Evd.set_leq_sort env evd (Prop Pos) du
	  else evd
	in
	let duu = Sorts.univ_of_sort du in
	let evd =
	  if not (Univ.is_small_univ duu) && Univ.Universe.equal cu duu then
	    if is_flexible_sort evd duu && not (Evd.check_leq evd Univ.type0_univ duu) then
	      Evd.set_eq_sort env evd (Prop Null) du
	    else evd
	  else Evd.set_eq_sort env evd (Type cu) du
	in
	  (evd, arity :: arities))
    (!evdref,[]) (Array.to_list levels') destarities sizes
  in evdref := evd; List.rev arities

let check_named (loc, na) = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err ?loc  msg


let check_param = function
| CLocalDef (na, _, _) -> check_named na
| CLocalAssum (nas, Default _, _) -> List.iter check_named nas
| CLocalAssum (nas, Generalized _, _) -> ()
| CLocalPattern (loc,_) ->
    Loc.raise ?loc (Stream.Error "pattern with quote not allowed here.")

let interp_mutual_inductive (paramsl,indl) notations cum poly prv finite =
  check_all_names_different indl;
  List.iter check_param paramsl;
  let env0 = Global.env() in
  let pl = (List.hd indl).ind_univs in
  let evd, decl = Univdecls.interp_univ_decl_opt env0 pl in
  let evdref = ref evd in
  let impls, ((env_params, ctx_params), userimpls) =
    interp_context_evars env0 evdref paramsl
  in
  let ctx_params = List.map (fun d -> map_rel_decl EConstr.Unsafe.to_constr d) ctx_params in
  let indnames = List.map (fun ind -> ind.ind_name) indl in
      
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter is_local_assum ctx_params in
  let params = List.map (RelDecl.get_name %> Name.get_id) assums in

  (* Interpret the arities *)
  let arities = List.map (interp_ind_arity env_params evdref) indl in

  let fullarities = List.map (fun (c, _, _) -> Term.it_mkProd_or_LetIn c ctx_params) arities in
  let env_ar = push_types env0 indnames fullarities in
  let env_ar_params = push_rel_context ctx_params env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun (_, _, impls) -> userimpls @ 
    lift_implicits (Context.Rel.nhyps ctx_params) impls) arities in
  let arities = List.map pi1 arities and aritypoly = List.map pi2 arities in
  let impls = compute_internalization_env env0 ~impls (Inductive (params,true)) indnames fullarities indimpls in
  let ntn_impls = compute_internalization_env env0 (Inductive (params,true)) indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data evdref env_params params) arities indnames in

  let constructors =
    Metasyntax.with_syntax_protection (fun () ->
     (* Temporary declaration of notations and scopes *)
     List.iter (Metasyntax.set_notation_for_interpretation env_params ntn_impls) notations;
     (* Interpret the constructor types *)
     List.map3 (interp_cstrs env_ar_params evdref impls) mldatas arities indl)
     () in

  (* Try further to solve evars, and instantiate them *)
  let sigma = solve_remaining_evars all_and_fail_flags env_params !evdref Evd.empty in
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
  let ctx_params = Context.Rel.map nf ctx_params in
  let evd = !evdref in
  let uctx = Evd.check_univ_decl ~poly evd decl in
  List.iter (fun c -> check_evars env_params Evd.empty evd (EConstr.of_constr c)) arities;
  Context.Rel.iter (fun c -> check_evars env0 Evd.empty evd (EConstr.of_constr c)) ctx_params;
  List.iter (fun (_,ctyps,_) ->
    List.iter (fun c -> check_evars env_ar_params Evd.empty evd (EConstr.of_constr c)) ctyps)
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
    let len = Context.Rel.nhyps ctx_params in
      List.map2 (fun indimpls (_,_,cimpls) ->
	indimpls, List.map (fun impls ->
	  userimpls @ (lift_implicits len impls)) cimpls) indimpls constructors
  in
  let univs =
    match uctx with
    | Polymorphic_const_entry uctx ->
      if cum then
        Cumulative_ind_entry (Universes.univ_inf_ind_from_universe_context uctx)
      else Polymorphic_ind_entry uctx
    | Monomorphic_const_entry uctx ->
      Monomorphic_ind_entry uctx
  in
  (* Build the mutual inductive entry *)
  let mind_ent =
    { mind_entry_params = List.map prepare_param ctx_params;
      mind_entry_record = None;
      mind_entry_finite = finite;
      mind_entry_inds = entries;
      mind_entry_private = if prv then Some false else None;
      mind_entry_universes = univs;
    }
  in
  (if poly && cum then
      Inductiveops.infer_inductive_subtyping env_ar evd mind_ent
   else mind_ent), Evd.universe_binders evd, impls

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
  | [] -> anomaly (Pp.str "empty list of inductive types.")
  | params::paramsl ->
      if not (List.for_all (eq_local_binders params) paramsl) then user_err Pp.(str
	"Parameters should be syntactically the same for each inductive type.");
      params

let extract_inductive indl =
  List.map (fun (((_,indname),pl),_,ar,lc) -> {
    ind_name = indname; ind_univs = pl;
    ind_arity = Option.cata (fun x -> x) (CAst.make @@ CSort (GType [])) ar;
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
    match Constr.kind typ with
    | Prod (_,arg,rest) ->
        not (EConstr.Vars.noccurn Evd.empty (** FIXME *) lift (EConstr.of_constr arg)) ||
        is_recursive_constructor (lift+1) rest
    | LetIn (na,b,t,rest) -> is_recursive_constructor (lift+1) rest
    | _ -> false
  in
  match mie.mind_entry_inds with
  | [ind] ->
      let nparams = List.length mie.mind_entry_params in
      List.exists (fun t -> is_recursive_constructor (nparams+1) t) ind.mind_entry_lc
  | _ -> false

let declare_mutual_inductive_with_eliminations mie pl impls =
  (* spiwack: raises an error if the structure is supposed to be non-recursive,
        but isn't *)
  begin match mie.mind_entry_finite with
  | BiFinite when is_recursive mie ->
      if Option.has_some mie.mind_entry_record then
        user_err Pp.(str "Records declared with the keywords Record or Structure cannot be recursive. You can, however, define recursive records using the Inductive or CoInductive command.")
      else
        user_err Pp.(str ("Types declared with the keyword Variant cannot be recursive. Recursive types are defined with the Inductive and CoInductive command."))
  | _ -> ()
  end;
  let names = List.map (fun e -> e.mind_entry_typename) mie.mind_entry_inds in
  let (_, kn), prim = declare_mind mie in
  let mind = Global.mind_of_delta_kn kn in
  List.iteri (fun i (indimpls, constrimpls) ->
	      let ind = (mind,i) in
	      let gr = IndRef ind in
	      maybe_declare_manual_implicits false gr indimpls;
              Declare.declare_univ_binders gr pl;
	      List.iteri
		(fun j impls ->
		 maybe_declare_manual_implicits false
		    (ConstructRef (ind, succ j)) impls)
		constrimpls)
      impls;
  let warn_prim = match mie.mind_entry_record with Some (Some _) -> not prim | _ -> false in
  Flags.if_verbose Feedback.msg_info (minductive_message warn_prim names);
  if mie.mind_entry_private == None
  then declare_default_schemes mind;
  mind

type one_inductive_impls =
  Impargs.manual_explicitation list (* for inds *)*
  Impargs.manual_explicitation list list (* for constrs *)

let do_mutual_inductive indl cum poly prv finite =
  let indl,coes,ntns = extract_mutual_inductive_declaration_components indl in
  (* Interpret the types *)
  let mie,pl,impls = interp_mutual_inductive indl ntns cum poly prv finite in
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (declare_mutual_inductive_with_eliminations mie pl impls);
  (* Declare the possible notations of inductive types *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env ())) ntns;
  (* Declare the coercions *)
  List.iter (fun qid -> Class.try_add_new_coercion (locate qid) ~local:false poly) coes;
  (* If positivity is assumed declares itself as unsafe. *)
  if Environ.deactivated_guard (Global.env ()) then Feedback.feedback Feedback.AddedAxiom else ()

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
      Id.print y ++ str " depends on " ++ Id.print x ++ strbrk " but not conversely"
    else if Id.List.mem y xge then
      Id.print x ++ str " depends on " ++ Id.print y ++ strbrk " but not conversely"
    else
      Id.print y ++ str " and " ++ Id.print x ++ strbrk " are not mutually dependent" in
  let e = if List.is_empty rest then reason else strbrk "e.g., " ++ reason in
  let k = if isfix then "fixpoint" else "cofixpoint" in
  let w =
    if isfix
    then strbrk "Well-foundedness check may fail unexpectedly." ++ fnl()
    else mt () in
  strbrk "Not a fully mutually defined " ++ str k ++ fnl () ++
  str "(" ++ e ++ str ")." ++ fnl () ++ w

let warn_non_full_mutual =
  CWarnings.create ~name:"non-full-mutual" ~category:"fixpoints"
         (fun (x,xge,y,yge,isfix,rest) ->
          non_full_mutual_message x xge y yge isfix rest)

let check_mutuality env evd isfix fixl =
  let names = List.map fst fixl in
  let preorder =
    List.map (fun (id,def) ->
      (id, List.filter (fun id' -> not (Id.equal id id') && occur_var env evd id' (EConstr.of_constr def)) names))
      fixl in
  let po = partial_order Id.equal preorder in
  match List.filter (function (_,Inr _) -> true | _ -> false) po with
    | (x,Inr xge)::(y,Inr yge)::rest ->
       warn_non_full_mutual (x,xge,y,yge,isfix,rest)
    | _ -> ()

type structured_fixpoint_expr = {
  fix_name : Id.t;
  fix_univs : universe_decl_expr option;
  fix_annot : Id.t Loc.located option;
  fix_binders : local_binder_expr list;
  fix_body : constr_expr option;
  fix_type : constr_expr
}

let interp_fix_context env evdref isfix fix =
  let before, after = if isfix then split_at_annot fix.fix_binders fix.fix_annot else [], fix.fix_binders in
  let impl_env, ((env', ctx), imps) = interp_context_evars env evdref before in
  let impl_env', ((env'', ctx'), imps') = interp_context_evars ~impl_env ~shift:(Context.Rel.nhyps ctx) env' evdref after in
  let annot = Option.map (fun _ -> List.length (assums_of_rel_context ctx)) fix.fix_annot in
    ((env'', ctx' @ ctx), (impl_env',imps @ imps'), annot)

let interp_fix_ccl evdref impls (env,_) fix =
  let (c, impl) = interp_type_evars_impls ~impls env evdref fix.fix_type in
  (c, impl)

let interp_fix_body env_rec evdref impls (_,ctx) fix ccl =
  let open EConstr in
  Option.map (fun body ->
    let env = push_rel_context ctx env_rec in
    let body = interp_casted_constr_evars env evdref ~impls body ccl in
    it_mkLambda_or_LetIn body ctx) fix.fix_body

let build_fix_type (_,ctx) ccl = EConstr.it_mkProd_or_LetIn ccl ctx

let prepare_recursive_declaration fixnames fixtypes fixdefs =
  let defs = List.map (subst_vars (List.rev fixnames)) fixdefs in
  let names = List.map (fun id -> Name id) fixnames in
  (Array.of_list names, Array.of_list fixtypes, Array.of_list defs)

(* Jump over let-bindings. *)

let compute_possible_guardness_evidences (ctx,_,recindex) =
  (* A recursive index is characterized by the number of lambdas to
     skip before finding the relevant inductive argument *)
  match recindex with
  | Some i -> [i]
  | None ->
      (* If recursive argument was not given by user, we try all args.
	 An earlier approach was to look only for inductive arguments,
	 but doing it properly involves delta-reduction, and it finally
         doesn't seem to worth the effort (except for huge mutual
	 fixpoints ?) *)
      List.interval 0 (Context.Rel.nhyps ctx - 1)

type recursive_preentry =
  Id.t list * constr option list * types list

(* Wellfounded definition *)

open Coqlib

let contrib_name = "Program"
let subtac_dir = [contrib_name]
let fixsub_module = subtac_dir @ ["Wf"]
let tactics_module = subtac_dir @ ["Tactics"]

let init_reference dir s () = Coqlib.coq_reference "Command" dir s
let init_constant  dir s evdref =
  let (sigma, c) = Evarutil.new_global !evdref (Coqlib.coq_reference "Command" dir s)
  in evdref := sigma; c

let make_ref l s = init_reference l s
let fix_proto = init_constant tactics_module "fix_proto"
let fix_sub_ref = make_ref fixsub_module "Fix_sub"
let measure_on_R_ref = make_ref fixsub_module "MR"
let well_founded = init_constant ["Init"; "Wf"] "well_founded"
let mkSubset evdref name typ prop =
  let open EConstr in
  mkApp (Evarutil.e_new_global evdref (delayed_force build_sigma).typ,
	 [| typ; mkLambda (name, typ, prop) |])
let sigT = Lazy.from_fun build_sigma_type

let make_qref s = Qualid (Loc.tag @@ qualid_of_string s)
let lt_ref = make_qref "Init.Peano.lt"

let rec telescope evdref l =
  let open EConstr in
  let open Vars in
  match l with
  | [] -> assert false
  | [LocalAssum (n, t)] -> t, [LocalDef (n, mkRel 1, t)], mkRel 1
  | LocalAssum (n, t) :: tl ->
      let ty, tys, (k, constr) =
	List.fold_left
	  (fun (ty, tys, (k, constr)) decl ->
            let t = RelDecl.get_type decl in
            let pred = mkLambda (RelDecl.get_name decl, t, ty) in
	    let ty = Evarutil.e_new_global evdref (Lazy.force sigT).typ in
	    let intro = Evarutil.e_new_global evdref (Lazy.force sigT).intro in
	    let sigty = mkApp (ty, [|t; pred|]) in
	    let intro = mkApp (intro, [|lift k t; lift k pred; mkRel k; constr|]) in
	      (sigty, pred :: tys, (succ k, intro)))
	  (t, [], (2, mkRel 1)) tl
      in
      let (last, subst) = List.fold_right2
        (fun pred decl (prev, subst) ->
          let t = RelDecl.get_type decl in
	  let p1 = Evarutil.e_new_global evdref (Lazy.force sigT).proj1 in
	  let p2 = Evarutil.e_new_global evdref (Lazy.force sigT).proj2 in
	  let proj1 = applist (p1, [t; pred; prev]) in
	  let proj2 = applist (p2, [t; pred; prev]) in
	    (lift 1 proj2, LocalDef (get_name decl, proj1, t) :: subst))
	(List.rev tys) tl (mkRel 1, [])
      in ty, (LocalDef (n, last, t) :: subst), constr

  | LocalDef (n, b, t) :: tl -> let ty, subst, term = telescope evdref tl in
      ty, (LocalDef (n, b, t) :: subst), lift 1 term

let nf_evar_context sigma ctx =
  List.map (map_constr (fun c -> Evarutil.nf_evar sigma c)) ctx

let build_wellfounded (recname,pl,n,bl,arityc,body) poly r measure notation =
  let open EConstr in
  let open Vars in
  let lift_rel_context n l = Termops.map_rel_context_with_binders (liftn n) l in
  Coqlib.check_required_library ["Coq";"Program";"Wf"];
  let env = Global.env() in
  let evd, decl = Univdecls.interp_univ_decl_opt env pl in
  let evdref = ref evd in
  let _, ((env', binders_rel), impls) = interp_context_evars env evdref bl in
  let len = List.length binders_rel in
  let top_env = push_rel_context binders_rel env in
  let top_arity = interp_type_evars top_env evdref arityc in
  let full_arity = it_mkProd_or_LetIn top_arity binders_rel in
  let argtyp, letbinders, make = telescope evdref binders_rel in
  let argname = Id.of_string "recarg" in
  let arg = LocalAssum (Name argname, argtyp) in
  let binders = letbinders @ [arg] in
  let binders_env = push_rel_context binders_rel env in
  let rel, _ = interp_constr_evars_impls env evdref r in
  let relty = Typing.unsafe_type_of env !evdref rel in
  let relargty =
    let error () =
      user_err ?loc:(constr_loc r)
               ~hdr:"Command.build_wellfounded"
		    (Printer.pr_econstr_env env !evdref rel ++ str " is not an homogeneous binary relation.")
    in
      try
	let ctx, ar = Reductionops.splay_prod_n env !evdref 2 relty in
	  match ctx, EConstr.kind !evdref ar with
	  | [LocalAssum (_,t); LocalAssum (_,u)], Sort s
	      when Sorts.is_prop (ESorts.kind !evdref s) && Reductionops.is_conv env !evdref t u -> t
	  | _, _ -> error ()
      with e when CErrors.noncritical e -> error ()
  in
  let relargty = EConstr.Unsafe.to_constr relargty in
  let measure = interp_casted_constr_evars binders_env evdref measure relargty in
  let wf_rel, wf_rel_fun, measure_fn =
    let measure_body, measure =
      it_mkLambda_or_LetIn measure letbinders,
      it_mkLambda_or_LetIn measure binders
    in
    let comb = Evarutil.e_new_global evdref (delayed_force measure_on_R_ref) in
    let relargty = EConstr.of_constr relargty in
    let wf_rel = mkApp (comb, [| argtyp; relargty; rel; measure |]) in
    let wf_rel_fun x y =
      mkApp (rel, [| subst1 x measure_body;
 		     subst1 y measure_body |])
    in wf_rel, wf_rel_fun, measure
  in
  let wf_proof = mkApp (well_founded evdref, [| argtyp ; wf_rel |]) in
  let argid' = Id.of_string (Id.to_string argname ^ "'") in
  let wfarg len = LocalAssum (Name argid',
                              mkSubset evdref (Name argid') argtyp
				       (wf_rel_fun (mkRel 1) (mkRel (len + 1))))
  in
  let intern_bl = wfarg 1 :: [arg] in
  let _intern_env = push_rel_context intern_bl env in
  let proj = Evarutil.e_new_global evdref (delayed_force build_sigma).Coqlib.proj1 in
  let wfargpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel 3)) in
  let projection = (* in wfarg :: arg :: before *)
    mkApp (proj, [| argtyp ; wfargpred ; mkRel 1 |])
  in
  let top_arity_let = it_mkLambda_or_LetIn top_arity letbinders in
  let intern_arity = substl [projection] top_arity_let in
  (* substitute the projection of wfarg for something,
     now intern_arity is in wfarg :: arg *)
  let intern_fun_arity_prod = it_mkProd_or_LetIn intern_arity [wfarg 1] in
  let intern_fun_binder = LocalAssum (Name (add_suffix recname "'"), intern_fun_arity_prod) in
  let curry_fun =
    let wfpred = mkLambda (Name argid', argtyp, wf_rel_fun (mkRel 1) (mkRel (2 * len + 4))) in
    let intro = Evarutil.e_new_global evdref (delayed_force build_sigma).Coqlib.intro in
    let arg = mkApp (intro, [| argtyp; wfpred; lift 1 make; mkRel 1 |]) in
    let app = mkApp (mkRel (2 * len + 2 (* recproof + orig binders + current binders *)), [| arg |]) in
    let rcurry = mkApp (rel, [| measure; lift len measure |]) in
    let lam = LocalAssum (Name (Id.of_string "recproof"), rcurry) in
    let body = it_mkLambda_or_LetIn app (lam :: binders_rel) in
    let ty = it_mkProd_or_LetIn (lift 1 top_arity) (lam :: binders_rel) in
      LocalDef (Name recname, body, ty)
  in
  let fun_bl = intern_fun_binder :: [arg] in
  let lift_lets = lift_rel_context 1 letbinders in
  let intern_body =
    let ctx = LocalAssum (Name recname, get_type curry_fun) :: binders_rel in
    let (r, l, impls, scopes) =
      Constrintern.compute_internalization_data env
	Constrintern.Recursive (EConstr.Unsafe.to_constr full_arity) impls 
    in
    let newimpls = Id.Map.singleton recname
      (r, l, impls @ [(Some (Id.of_string "recproof", Impargs.Manual, (true, false)))],
       scopes @ [None]) in
      interp_casted_constr_evars (push_rel_context ctx env) evdref
        ~impls:newimpls body (EConstr.Unsafe.to_constr (lift 1 top_arity))
  in
  let intern_body_lam = it_mkLambda_or_LetIn intern_body (curry_fun :: lift_lets @ fun_bl) in
  let prop = mkLambda (Name argname, argtyp, top_arity_let) in
  let def =
    mkApp (Evarutil.e_new_global evdref (delayed_force fix_sub_ref),
	  [| argtyp ; wf_rel ;
	     Evarutil.e_new_evar env evdref
	       ~src:(Loc.tag @@ Evar_kinds.QuestionMark (Evar_kinds.Define false,Anonymous)) wf_proof;
	     prop |])
  in
  let def = Typing.e_solve_evars env evdref def in
  let _ = evdref := Evarutil.nf_evar_map !evdref in
  let def = mkApp (def, [|intern_body_lam|]) in
  let binders_rel = nf_evar_context !evdref binders_rel in
  let binders = nf_evar_context !evdref binders in
  let top_arity = Evarutil.nf_evar !evdref top_arity in
  let hook, recname, typ =
    if List.length binders_rel > 1 then
      let name = add_suffix recname "_func" in
      let hook l gr _ = 
        let body = it_mkLambda_or_LetIn (mkApp (Evarutil.e_new_global evdref gr, [|make|])) binders_rel in
        let ty = it_mkProd_or_LetIn top_arity binders_rel in
        let ty = EConstr.Unsafe.to_constr ty in
        let univs = Evd.check_univ_decl ~poly !evdref decl in
        (*FIXME poly? *)
        let ce = definition_entry ~types:ty ~univs (EConstr.to_constr !evdref body) in
        (** FIXME: include locality *)
        let c = Declare.declare_constant recname (DefinitionEntry ce, IsDefinition Definition) in
        let gr = ConstRef c in
        let () = Universes.register_universe_binders gr (Evd.universe_binders !evdref) in
        if Impargs.is_implicit_args () || not (List.is_empty impls) then
          Impargs.declare_manual_implicits false gr [impls]
      in
      let typ = it_mkProd_or_LetIn top_arity binders in
	hook, name, typ
    else 
      let typ = it_mkProd_or_LetIn top_arity binders_rel in
      let hook l gr _ = 
	if Impargs.is_implicit_args () || not (List.is_empty impls) then
	  Impargs.declare_manual_implicits false gr [impls]
      in hook, recname, typ
  in
  let hook = Lemmas.mk_hook hook in
  let fullcoqc = EConstr.to_constr !evdref def in
  let fullctyp = EConstr.to_constr !evdref typ in
  Obligations.check_evars env !evdref;
  let evars, _, evars_def, evars_typ = 
    Obligations.eterm_obligations env recname !evdref 0 fullcoqc fullctyp 
  in
  let ctx = Evd.evar_universe_context !evdref in
    ignore(Obligations.add_definition recname ~term:evars_def ~univdecl:decl
	     evars_typ ctx evars ~hook)

let interp_recursive isfix fixl notations =
  let open Context.Named.Declaration in
  let open EConstr in
  let env = Global.env() in
  let fixnames = List.map (fun fix -> fix.fix_name) fixl in

  (* Interp arities allowing for unresolved types *)
  let all_universes =
    List.fold_right (fun sfe acc ->
        match sfe.fix_univs , acc with
        | None , acc -> acc
        | x , None -> x
        | Some ls , Some us ->
           let lsu = ls.univdecl_instance and usu = us.univdecl_instance in
	   if not (CList.for_all2eq (fun x y -> Id.equal (snd x) (snd y)) lsu usu) then
	     user_err Pp.(str "(co)-recursive definitions should all have the same universe binders");
	   Some us) fixl None in
  let evd, decl = Univdecls.interp_univ_decl_opt env all_universes in
  let evdref = ref evd in
  let fixctxs, fiximppairs, fixannots =
    List.split3 (List.map (interp_fix_context env evdref isfix) fixl) in
  let fixctximpenvs, fixctximps = List.split fiximppairs in
  let fixccls,fixcclimps = List.split (List.map3 (interp_fix_ccl evdref) fixctximpenvs fixctxs fixl) in
  let fixtypes = List.map2 build_fix_type fixctxs fixccls in
  let fixtypes = List.map (fun c -> nf_evar !evdref c) fixtypes in
  let fiximps = List.map3
    (fun ctximps cclimps (_,ctx) -> ctximps@(Impargs.lift_implicits (Context.Rel.nhyps ctx) cclimps))
    fixctximps fixcclimps fixctxs in
  let rec_sign =
    List.fold_left2
      (fun env' id t ->
 	 if Flags.is_program_mode () then
	   let sort = Evarutil.evd_comb1 (Typing.type_of ~refresh:true env) evdref t in
	   let fixprot =
	     try 
	       let app = mkApp (fix_proto evdref, [|sort; t|]) in
		 Typing.e_solve_evars env evdref app
	     with e  when CErrors.noncritical e -> t
	   in
	     LocalAssum (id,fixprot) :: env'
	 else LocalAssum (id,t) :: env')
      [] fixnames fixtypes
  in
  let env_rec = push_named_context rec_sign env in

  (* Get interpretation metadatas *)
  let fixtypes = List.map EConstr.Unsafe.to_constr fixtypes in
  let fixccls = List.map EConstr.Unsafe.to_constr fixccls in
  let impls = compute_internalization_env env Recursive fixnames fixtypes fiximps in

  (* Interp bodies with rollback because temp use of notations/implicit *)
  let fixdefs =
    Metasyntax.with_syntax_protection (fun () ->
      List.iter (Metasyntax.set_notation_for_interpretation env_rec impls) notations;
      List.map4
	(fun fixctximpenv -> interp_fix_body env_rec evdref (Id.Map.fold Id.Map.add fixctximpenv impls))
	fixctximpenvs fixctxs fixl fixccls)
      () in

  (* Instantiate evars and check all are resolved *)
  let evd = solve_unif_constraints_with_heuristics env_rec !evdref in
  let evd, nf = nf_evars_and_universes evd in
  let fixdefs = List.map (fun c -> Option.map EConstr.Unsafe.to_constr c) fixdefs in
  let fixdefs = List.map (Option.map nf) fixdefs in
  let fixtypes = List.map nf fixtypes in
  let fixctxs = List.map (fun (_,ctx) -> ctx) fixctxs in

  (* Build the fix declaration block *)
  (env,rec_sign,decl,evd), (fixnames,fixdefs,fixtypes), List.combine3 fixctxs fiximps fixannots

let check_recursive isfix env evd (fixnames,fixdefs,_) =
  check_evars_are_solved env evd Evd.empty;
  if List.for_all Option.has_some fixdefs then begin
    let fixdefs = List.map Option.get fixdefs in
    check_mutuality env evd isfix (List.combine fixnames fixdefs)
  end

let interp_fixpoint l ntns =
  let (env,_,pl,evd),fix,info = interp_recursive true l ntns in
  check_recursive true env evd fix;
  (fix,pl,Evd.evar_universe_context evd,info)

let interp_cofixpoint l ntns =
  let (env,_,pl,evd),fix,info = interp_recursive false l ntns in
  check_recursive false env evd fix;
  (fix,pl,Evd.evar_universe_context evd,info)
    
let declare_fixpoint local poly ((fixnames,fixdefs,fixtypes),pl,ctx,fiximps) indexes ntns =
  if List.exists Option.is_empty fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      List.map3 (fun id t (ctx,imps,_) -> (id,(t,(List.map RelDecl.get_name ctx,imps))))
		fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC)
        fixdefs) in
    let evd = Evd.from_ctx ctx in
    Lemmas.start_proof_with_initialization (Global,poly,DefinitionBody Fixpoint)
      evd pl (Some(false,indexes,init_tac)) thms None (Lemmas.mk_hook (fun _ _ -> ()))
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let env = Global.env() in
    let indexes = search_guard env indexes fixdecls in
    let fiximps = List.map (fun (n,r,p) -> r) fiximps in
    let vars = Univops.universes_of_constr (mkFix ((indexes,0),fixdecls)) in
    let fixdecls =
      List.map_i (fun i _ -> mkFix ((indexes,i),fixdecls)) 0 fixnames in
    let evd = Evd.from_ctx ctx in
    let evd = Evd.restrict_universe_context evd vars in
    let ctx = Evd.check_univ_decl ~poly evd pl in
    let pl = Evd.universe_binders evd in
    let fixdecls = List.map Safe_typing.mk_pure_proof fixdecls in
    ignore (List.map4 (DeclareDef.declare_fix (local, poly, Fixpoint) pl ctx)
	      fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    fixpoint_message (Some indexes) fixnames;
  end;
  (* Declare notations *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns

let declare_cofixpoint local poly ((fixnames,fixdefs,fixtypes),pl,ctx,fiximps) ntns =
  if List.exists Option.is_empty fixdefs then
    (* Some bodies to define by proof *)
    let thms =
      List.map3 (fun id t (ctx,imps,_) -> (id,(t,(List.map RelDecl.get_name ctx,imps))))
		fixnames fixtypes fiximps in
    let init_tac =
      Some (List.map (Option.cata (EConstr.of_constr %> Tactics.exact_no_check) Tacticals.New.tclIDTAC)
        fixdefs) in
    let evd = Evd.from_ctx ctx in
      Lemmas.start_proof_with_initialization (Global,poly, DefinitionBody CoFixpoint)
      evd pl (Some(true,[],init_tac)) thms None (Lemmas.mk_hook (fun _ _ -> ()))
  else begin
    (* We shortcut the proof process *)
    let fixdefs = List.map Option.get fixdefs in
    let fixdecls = prepare_recursive_declaration fixnames fixtypes fixdefs in
    let fixdecls = List.map_i (fun i _ -> mkCoFix (i,fixdecls)) 0 fixnames in
    let vars = Univops.universes_of_constr (List.hd fixdecls) in
    let fixdecls = List.map Safe_typing.mk_pure_proof fixdecls in
    let fiximps = List.map (fun (len,imps,idx) -> imps) fiximps in
    let evd = Evd.from_ctx ctx in
    let evd = Evd.restrict_universe_context evd vars in
    let ctx = Evd.check_univ_decl ~poly evd pl in
    let pl = Evd.universe_binders evd in
    ignore (List.map4 (DeclareDef.declare_fix (local, poly, CoFixpoint) pl ctx)
	      fixnames fixdecls fixtypes fiximps);
    (* Declare the recursive definitions *)
    cofixpoint_message fixnames
  end;
  (* Declare notations *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env())) ntns

let extract_decreasing_argument limit = function
  | (na,CStructRec) -> na
  | (na,_) when not limit -> na
  | _ -> user_err Pp.(str 
      "Only structural decreasing is supported for a non-Program Fixpoint")

let extract_fixpoint_components limit l =
  let fixl, ntnl = List.split l in
  let fixl = List.map (fun (((_,id),pl),ann,bl,typ,def) ->
    let ann = extract_decreasing_argument limit ann in
      {fix_name = id; fix_annot = ann; fix_univs = pl;
       fix_binders = bl; fix_body = def; fix_type = typ}) fixl in
  fixl, List.flatten ntnl

let extract_cofixpoint_components l =
  let fixl, ntnl = List.split l in
  List.map (fun (((_,id),pl),bl,typ,def) ->
	    {fix_name = id; fix_annot = None; fix_univs = pl;
	     fix_binders = bl; fix_body = def; fix_type = typ}) fixl,
  List.flatten ntnl

let out_def = function
  | Some def -> def
  | None -> user_err Pp.(str "Program Fixpoint needs defined bodies.")

let collect_evars_of_term evd c ty =
  let evars = Evar.Set.union (Evd.evars_of_term c) (Evd.evars_of_term ty) in
  Evar.Set.fold (fun ev acc -> Evd.add acc ev (Evd.find_undefined evd ev))
  evars (Evd.from_ctx (Evd.evar_universe_context evd))

let do_program_recursive local poly fixkind fixl ntns =
  let isfix = fixkind != Obligations.IsCoFixpoint in
  let (env, rec_sign, pl, evd), fix, info = 
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
      EConstr.to_constr evd (Termops.it_mkNamedLambda_or_LetIn (EConstr.of_constr def) rec_sign)
    and typ =
      EConstr.to_constr evd (Termops.it_mkNamedProd_or_LetIn (EConstr.of_constr typ) rec_sign)
    in
    let evm = collect_evars_of_term evd def typ in
    let evars, _, def, typ = 
      Obligations.eterm_obligations env id evm
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
        Pretyping.search_guard (Global.env ()) possible_indexes fixdecls in
      List.iteri (fun i _ ->
          Inductive.check_fix env
                              ((indexes,i),fixdecls))
        fixl
  end in
  let ctx = Evd.evar_universe_context evd in
  let kind = match fixkind with
  | Obligations.IsFixpoint _ -> (local, poly, Fixpoint)
  | Obligations.IsCoFixpoint -> (local, poly, CoFixpoint)
  in
  Obligations.add_mutual_definitions defs ~kind ~univdecl:pl ctx ntns fixkind

let do_program_fixpoint local poly l =
  let g = List.map (fun ((_,wf,_,_,_),_) -> wf) l in
    match g, l with
    | [(n, CWfRec r)], [((((_,id),pl),_,bl,typ,def),ntn)] ->
	let recarg = 
	  match n with
	  | Some n -> mkIdentC (snd n)
	  | None ->
	      user_err ~hdr:"do_program_fixpoint"
		(str "Recursive argument required for well-founded fixpoints")
	in build_wellfounded (id, pl, n, bl, typ, out_def def) poly r recarg ntn
	     
    | [(n, CMeasureRec (m, r))], [((((_,id),pl),_,bl,typ,def),ntn)] ->
	build_wellfounded (id, pl, n, bl, typ, out_def def) poly
	  (Option.default (CAst.make @@ CRef (lt_ref,None)) r) m ntn
	  
    | _, _ when List.for_all (fun (n, ro) -> ro == CStructRec) g ->
	let fixl,ntns = extract_fixpoint_components true l in
	let fixkind = Obligations.IsFixpoint g in
	  do_program_recursive local poly fixkind fixl ntns

    | _, _ ->
	user_err ~hdr:"do_program_fixpoint"
	  (str "Well-founded fixpoints not allowed in mutually recursive blocks")

let check_safe () =
  let open Declarations in
  let flags = Environ.typing_flags (Global.env ()) in
  flags.check_universes && flags.check_guarded

let do_fixpoint local poly l =
  if Flags.is_program_mode () then do_program_fixpoint local poly l
  else
    let fixl, ntns = extract_fixpoint_components true l in
    let (_, _, _, info as fix) = interp_fixpoint fixl ntns in
    let possible_indexes =
      List.map compute_possible_guardness_evidences info in
    declare_fixpoint local poly fix possible_indexes ntns;
    if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()

let do_cofixpoint local poly l =
  let fixl,ntns = extract_cofixpoint_components l in
    if Flags.is_program_mode () then
      do_program_recursive local poly Obligations.IsCoFixpoint fixl ntns
    else
      let cofix = interp_cofixpoint fixl ntns in
      declare_cofixpoint local poly cofix ntns;
      if not (check_safe ()) then Feedback.feedback Feedback.AddedAxiom else ()
