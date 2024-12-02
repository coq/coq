(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module CVars = Vars

open Pp
open CErrors
open Sorts
open Util
open Context
open Environ
open Names
open Libnames
open Constrexpr
open Constrexpr_ops
open Constrintern
open Type_errors
open Pretyping
open Context.Rel.Declaration
open Entries
open EConstr

module RelDecl = Context.Rel.Declaration

type flags = {
  poly : bool;
  cumulative : bool;
  template : bool option;
  auto_prop_lowering : bool;
  finite : Declarations.recursivity_kind;
  mode : Hints.hint_mode list option;
}

(* 3b| Mutual inductive definitions *)

let warn_auto_template =
  CWarnings.create ~name:"auto-template" ~default:CWarnings.Disabled
    (fun id ->
       Pp.(strbrk "Automatically declaring " ++ Id.print id ++
           strbrk " as template polymorphic. Use attributes or " ++
           strbrk "disable Auto Template Polymorphism to avoid this warning."))

let should_auto_template =
  let open Goptions in
  let auto = ref true in
  let () = declare_bool_option
      { optstage = Summary.Stage.Interp;
        optdepr  = None;
        optkey   = ["Auto";"Template";"Polymorphism"];
        optread  = (fun () -> !auto);
        optwrite = (fun b -> auto := b); }
  in
  fun id would_auto ->
    let b = !auto && would_auto in
    if b then warn_auto_template id;
    b

let push_types env idl rl tl =
  List.fold_left3 (fun env id r t -> EConstr.push_rel (LocalAssum (make_annot (Name id) r,t)) env)
    env idl rl tl

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_arity_explicit : bool;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

exception Same of Id.t

let check_all_names_different indl =
  let rec elements = function
  | [] -> Id.Set.empty
  | id :: l ->
    let s = elements l in
    if Id.Set.mem id s then raise (Same id) else Id.Set.add id s
  in
  let ind_names = List.map (fun ind -> ind.ind_name) indl in
  let cstr_names = List.map_append (fun ind -> List.map fst ind.ind_lc) indl in
  let ind_names = match elements ind_names with
  | s -> s
  | exception (Same t) -> raise (InductiveError (SameNamesTypes t))
  in
  let cstr_names = match elements cstr_names with
  | s -> s
  | exception (Same c) -> raise (InductiveError (SameNamesConstructors c))
  in
  let l = Id.Set.inter ind_names cstr_names in
  if not (Id.Set.is_empty l) then
    raise (InductiveError (SameNamesOverlap (Id.Set.elements l)))

(** Make the arity conclusion flexible to avoid generating an upper bound universe now,
    only if the universe does not appear anywhere else.
    This is really a hack to stay compatible with the semantics of template polymorphic
    inductives which are recognized when a "Type" appears at the end of the conlusion in
    the source syntax. *)

let rec check_type_conclusion ind =
  let open Glob_term in
  match DAst.get ind with
  | GSort s ->
    (* not sure what this check is expected to be exactly *)
    begin match s with
      | (None, UAnonymous {rigid=UnivRigid}) ->
        (* should have been made flexible *)
        assert false
      | (None, UAnonymous {rigid=UnivFlexible}) -> true
      | _ -> true
    end
  | GProd (_, _, _, _, e)
  | GLetIn (_, _, _, _, e) ->
    check_type_conclusion e
  | _ -> false

let rec make_anonymous_conclusion_flexible ind =
  let open Glob_term in
  match DAst.get ind with
  | GSort (None, UAnonymous {rigid=UnivRigid}) ->
    Some (DAst.make ?loc:ind.loc (GSort (None, UAnonymous {rigid=UnivFlexible})))
  | GSort _ -> None
  | GProd (a, b, c, d, e) -> begin match make_anonymous_conclusion_flexible e with
      | None -> None
      | Some e -> Some (DAst.make ?loc:ind.loc (GProd (a, b, c, d, e)))
    end
  | GLetIn (a, b, c, d, e) -> begin match make_anonymous_conclusion_flexible e with
      | None -> None
      | Some e -> Some (DAst.make ?loc:ind.loc (GLetIn (a, b, c, d, e)))
    end
  | _ -> None

type syntax_allows_template_poly = SyntaxAllowsTemplatePoly | SyntaxNoTemplatePoly

let intern_ind_arity env sigma ind =
  let c = intern_gen IsType env sigma ind.ind_arity in
  let impls = Implicit_quantifiers.implicits_of_glob_constr ~with_products:true c in
  let pseudo_poly, c = match make_anonymous_conclusion_flexible c with
    | None -> check_type_conclusion c, c
    | Some c -> true, c
  in
  let template_syntax = if pseudo_poly then SyntaxAllowsTemplatePoly else SyntaxNoTemplatePoly in
  (constr_loc ind.ind_arity, c, impls, template_syntax)

let pretype_ind_arity ~unconstrained_sorts env sigma (loc, c, impls, template_syntax) =
  let flags = { Pretyping.all_no_fail_flags with unconstrained_sorts } in
  let sigma,t = understand_tcc ~flags env sigma ~expected_type:IsType c in
  match Reductionops.sort_of_arity env sigma t with
  | exception Reduction.NotArity ->
    user_err ?loc (str "Not an arity")
  | s ->
    sigma, (t, Retyping.relevance_of_sort s, template_syntax, impls)

(* ind_rel is the Rel for this inductive in the context without params.
   n is how many arguments there are in the constructor. *)
let model_conclusion env sigma ind_rel params n arity_indices =
  let model_head = EConstr.mkRel (n + Context.Rel.length params + ind_rel) in
  let model_params = Context.Rel.instance EConstr.mkRel n params in
  let sigma,model_indices =
    List.fold_right
      (fun (_,t) (sigma, subst) ->
        let t = EConstr.Vars.substl subst (EConstr.Vars.liftn n (List.length subst + 1) t) in
        let sigma, c = Evarutil.new_evar env sigma t in
        sigma, c::subst)
      arity_indices (sigma, []) in
  sigma, mkApp (mkApp (model_head, model_params), Array.of_list (List.rev model_indices))

let interp_cstrs env (sigma, ind_rel) impls params ind arity =
  let cnames,ctyps = List.split ind.ind_lc in
  let arity_indices, cstr_sort = Reductionops.splay_arity env sigma arity in
  (* Interpret the constructor types *)
  let interp_cstr sigma ctyp =
    let flags =
      Pretyping.{ all_no_fail_flags with
                  use_typeclasses = UseTCForConv;
                  solve_unification_constraints = false }
    in
    let sigma, (ctyp, cimpl) = interp_type_evars_impls ~flags env sigma ~impls ctyp in
    let ctx, concl = Reductionops.whd_decompose_prod_decls env sigma ctyp in
    let concl_env = EConstr.push_rel_context ctx env in
    let sigma_with_model_evars, model =
      model_conclusion concl_env sigma ind_rel params (Context.Rel.length ctx) arity_indices
    in
    (* unify the expected with the provided conclusion *)
    let sigma =
      try Evarconv.unify concl_env sigma_with_model_evars Conversion.CONV concl model
      with Evarconv.UnableToUnify (sigma,e) ->
        user_err (Himsg.explain_pretype_error concl_env sigma
                    (Pretype_errors.CannotUnify (concl, model, (Some e))))
    in
    sigma, (ctyp, cimpl)
  in
  let sigma, (ctyps, cimpls) =
    on_snd List.split @@
    List.fold_left_map interp_cstr sigma ctyps
  in
  (sigma, pred ind_rel), (cnames, ctyps, cimpls)

(***** Generate constraints from constructor arguments *****)

let compute_constructor_levels env evd sign =
  fst (List.fold_right
    (fun d (lev,env) ->
      match d with
      | LocalDef _ -> lev, EConstr.push_rel d env
      | LocalAssum _ ->
        let s = Retyping.get_sort_of env evd (RelDecl.get_type d) in
          (s :: lev, EConstr.push_rel d env))
    sign ([],env))

let warn_auto_prop_lowering =
  CWarnings.create ~name:"automatic-prop-lowering" ~category:Deprecation.Version.v8_20
    Pp.(fun na ->
        strbrk "Automatically putting " ++ Id.print na ++ strbrk " in Prop" ++ spc() ++
        strbrk "even though it was declared with Type." ++ fnl() ++
        strbrk "Unset Automatic Proposition Inductives to prevent this" ++ spc() ++
        strbrk "(it will become the default in a future version)." ++ fnl() ++
        strbrk "If you instead put " ++ Id.print na ++ strbrk " explicitly in Prop," ++ spc() ++
        strbrk "set Dependent Proposition Eliminators around the declaration for full backwards compatibility.")

let is_flexible_sort evd s = match ESorts.kind evd s with
| Set | Prop | SProp -> false
| Type u | QSort (_, u) ->
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

let prop_lowering_candidates ~auto_prop_lowering evd ~arities_explicit inds =
  let less_than_2 = function [] | [_] -> true | _ :: _ :: _ -> false in

  (* handle automatic lowering to Prop
     We repeatedly add information about which inductives should not be Prop
     until no more progress can be made
  *)
  let is_prop_candidate_arity (raw_arity,(_,s),indices,ctors) =
    less_than_2 ctors
    && EConstr.isArity evd raw_arity
    && is_flexible_sort evd s
    && not (Evd.check_leq evd ESorts.set s)
  in
  let candidates = List.filter_map (fun (explicit,(_,(_,s),_,_ as ind)) ->
      if (auto_prop_lowering || not explicit) && is_prop_candidate_arity ind
      then Some s else None)
      (List.combine arities_explicit inds)
  in

  let in_candidates s candidates = List.mem_f (ESorts.equal evd) s candidates in
  let is_prop_candidate_size candidates (_,_,indices,ctors) =
    List.for_all
      (List.for_all (fun s -> match ESorts.kind evd s with
           | SProp | Prop -> true
           | Set -> false
           | Type _ | QSort _ ->
             not (Evd.check_leq evd ESorts.set s)
             && in_candidates s candidates))
      (Option.List.cons indices ctors)
  in
  let rec spread_nonprop candidates =
    let (changed, candidates) = List.fold_left
        (fun (changed, candidates as acc) (raw_arity,(_,s),indices,ctors as ind) ->
           if is_prop_candidate_size candidates ind
           then acc (* still a Prop candidate *)
           else if in_candidates s candidates
           then (true, List.remove (ESorts.equal evd) s candidates)
           else acc)
        (false,candidates)
        inds
    in
    if changed then spread_nonprop candidates
    else candidates
  in
  let candidates = spread_nonprop candidates in
  candidates

let include_constructor_argument env evd ~poly ~ctor_sort ~inductive_sort =
  if poly then
    (* We ignore the quality when comparing the sorts: it has an impact
       on squashing in the kernel but cannot cause a universe error. *)
    let univ_of_sort s =
      match ESorts.kind evd s with
      | SProp | Prop -> None
      | Set -> Some Univ.Universe.type0
      | Type u | QSort (_,u) -> Some u
    in
    match univ_of_sort ctor_sort, univ_of_sort inductive_sort with
    | _, None ->
      (* This function is only called when [s] is not impredicative *)
      assert false
    | None, Some _ -> evd
    | Some uctor, Some uind ->
      let mk u = ESorts.make (Sorts.sort_of_univ u) in
      Evd.set_leq_sort env evd (mk uctor) (mk uind)
  else
    match ESorts.kind evd ctor_sort with
    | SProp | Prop -> evd
    | Set | Type _ | QSort _ ->
      Evd.set_leq_sort env evd ctor_sort inductive_sort

type default_dep_elim = DeclareInd.default_dep_elim = DefaultElim | PropButDepElim

let inductive_levels ~auto_prop_lowering env evd ~poly ~indnames ~arities_explicit arities ctors =
  let inds = List.map2 (fun x ctors ->
      let ctx, s = Reductionops.dest_arity env evd x in
      x, (ctx, s), List.map (compute_constructor_levels env evd) ctors)
      arities ctors
  in
  (* Inductives explicitly put in an impredicative sort can be
     squashed, so there are no constraints to get from them. *)
  let is_impredicative_sort evd s = is_impredicative_sort env (ESorts.kind evd s) in
  (* Inductives with >= 2 constructors are >= Set *)
  let less_than_2 = function [] | [_] -> true | _ :: _ :: _ -> false in
  let evd = List.fold_left (fun evd (raw_arity,(_,s),ctors) ->
      if less_than_2 ctors || is_impredicative_sort evd s then evd
      else (* >=2 constructors is like having a bool argument *)
        include_constructor_argument env evd ~poly ~ctor_sort:ESorts.set ~inductive_sort:s)
      evd inds
  in
  (* If indices_matter, the index telescope acts like an extra
     constructor except for constructor count checks. *)
  let inds =
    List.map (fun (raw_arity,(ctx,_ as arity),ctors) ->
        let indices = if indices_matter env then
            Some (compute_constructor_levels env evd ctx)
          else None
        in
        (raw_arity,arity,indices,ctors))
      inds
  in

  let candidates = prop_lowering_candidates ~auto_prop_lowering evd ~arities_explicit inds in
  (* Do the lowering. We forget about the generated universe for the
     lowered inductive and rely on universe restriction to get rid of
     it.

     NB: it would probably be less hacky to use the sort polymorphism system
     ie lowering to Prop by setting a qvar equal to prop.

     However this means we wouldn't lower "Inductive foo : Type := ."
     as "Type" doesn't produce a qvar.

     Perhaps someday we can stop lowering these explicit ": Type". *)
  let inds = List.map3 (fun na explicit (raw_arity,(ctx,s),indices,ctors) ->
      if List.mem_f (ESorts.equal evd) s candidates then
        (* NB: is_prop_candidate requires is_flexible_sort
           so in this branch we know s <> Prop *)
        let () = if explicit then warn_auto_prop_lowering na in
        ((PropButDepElim, mkArity (ctx, ESorts.prop)),ESorts.prop,indices,ctors)
      else ((DefaultElim, raw_arity), s, indices, ctors))
      indnames
      arities_explicit
      inds
  in

  (* Add constraints from constructor arguments and indices.
     We must do this after Prop lowering as otherwise we risk unifying sorts
     eg on "Box (A:Type)" we risk unifying the parameter sort and the output sort
     then ESorts.equal would make us believe that the constructor argument is a lowering candidate.
  *)
  let evd = List.fold_left (fun evd (_,s,indices,ctors) ->
      if is_impredicative_sort evd s then evd
      else List.fold_left
          (List.fold_left (fun evd ctor_sort ->
               include_constructor_argument env evd ~poly ~ctor_sort ~inductive_sort:s))
          evd (Option.List.cons indices ctors))
      evd inds
  in
  let arities = List.map (fun (arity,_,_,_) -> arity) inds in
  evd, List.split arities

(** Template poly ***)

let check_named {CAst.loc;v=na} = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err ?loc  msg

let get_arity c =
  let decls, c = Term.decompose_prod_decls c in
  match Constr.kind c with
  | Sort (Type u) ->
    begin match Univ.Universe.level u with
    | Some l -> Some (decls, l)
    | None -> None
    end
  | _ -> None

let non_template_levels ~params entry =
  let ctx, u = Term.destArity entry.mind_entry_arity in
  let add_levels c levels = Univ.Level.Set.union levels (CVars.universes_of_constr c) in
  let fold_params levels = function
    | LocalDef (_, b, t) -> add_levels b (add_levels t levels)
    | LocalAssum (_, t) ->
      match get_arity t with
      | None -> add_levels t levels
      | Some (decls, _) -> add_levels (Term.it_mkProd_or_LetIn Constr.mkProp decls) levels
  in
  (* Levels in LocalDef params, on the left of the context in LocalAssum params,
     in the indices and in the constructor types are not allowed to be template.
     (partly to guarantee Irrelevant variance, and partly to simplify universe substitution code) *)
  let levels = List.fold_left fold_params Univ.Level.Set.empty params in
  let levels = add_levels (Term.mkArity (ctx,Sorts.prop)) levels in
  let levels = List.fold_left (fun levels c -> add_levels c levels)
      levels entry.mind_entry_lc
  in
  (* levels with nonzero increment in the conclusion may not be template
     (until constraint checking can handle arbitrary +k, cf #19230) *)
  let concl_univs = match u with
    | Sorts.Type u -> Univ.Universe.repr u
    | QSort _ -> assert false
    | SProp | Prop | Set -> []
  in
  let levels =
    List.fold_left (fun levels (u,n) ->
        if Int.equal n 0 then levels else Univ.Level.Set.add u levels)
      levels
      concl_univs
  in
  levels

let unbounded_from_below u cstrs =
  let open Univ in
  Univ.Constraints.for_all (fun (l, d, r) ->
      match d with
      | Eq -> not (Univ.Universe.mem u l) && not (Univ.Universe.mem u r)
      | Le -> not (Univ.Universe.mem u r))
    cstrs

type linearity = Linear | NonLinear

(* Returns the list [x_1, ..., x_n] of levels contributing to template
   polymorphism. The elements x_k is None if the k-th parameter
   (starting from the most recent and ignoring let-definitions) is not
   template or is Some u_k if its level is u_k and is template. *)
let template_polymorphic_univs uctx params entry =
  let non_template_levels = non_template_levels ~params entry in
  let fold_params accu decl = match decl with
  | LocalAssum (_, p) ->
    let c = Term.strip_prod_decls p in
    begin match get_arity c with
    | Some (_, l) ->
      Univ.Level.Map.update l (function None -> Some Linear | Some _ -> Some NonLinear) accu
    | None -> accu
    end
  | LocalDef _ -> accu
  in
  let paramslevels = List.fold_left fold_params Univ.Level.Map.empty params in
  let paramslevels =
    Univ.Level.Map.filter (fun u -> function
        | NonLinear -> false
        | Linear ->
          assert (not @@ Univ.Level.is_set u);
          Univ.Level.Set.mem u (Univ.ContextSet.levels uctx) &&
          unbounded_from_below u (Univ.ContextSet.constraints uctx) &&
          not (Univ.Level.Set.mem u non_template_levels))
      paramslevels
  in
  Univ.Level.Map.domain paramslevels

let template_polymorphism_candidate uctx params entry template_syntax = match template_syntax with
| SyntaxNoTemplatePoly -> Univ.Level.Set.empty
| SyntaxAllowsTemplatePoly ->
  let univs = template_polymorphic_univs uctx params entry in
  univs

(* Returns two universe contexts, for the template and global universes.
   The global universe will be declared before the template ones. *)
let split_universe_context subset (univs, csts) =
  let rem = Univ.Level.Set.diff univs subset in
  let subfilter (l, _, r) =
    let l = Univ.Universe.levels l in
    let r = Univ.Universe.levels r in
    let () = assert (not @@ Univ.Level.Set.for_all (fun r -> Univ.Level.Set.mem r subset) r) in
    Univ.Level.Set.exists (fun l -> Univ.Level.Set.mem l subset) l
  in
  let subcst, remcst = Univ.Constraints.partition subfilter csts in
  (subset, subcst), (rem, remcst)

let warn_no_template_universe =
  CWarnings.create ~name:"no-template-universe"
    (fun () -> Pp.str "This inductive type has no template universes.")

let compute_template_inductive ~user_template ~ctx_params ~univ_entry entry template_syntax =
match user_template, univ_entry with
| Some false, UState.Monomorphic_entry uctx ->
  Monomorphic_ind_entry, uctx
| Some false, UState.Polymorphic_entry (uctx, variances) ->
  Polymorphic_ind_entry (uctx, variances), Univ.ContextSet.empty
| Some true, UState.Monomorphic_entry uctx ->
  let template_universes = template_polymorphism_candidate uctx ctx_params entry template_syntax in
  let template, global = split_universe_context template_universes uctx in
  let () = if Univ.Level.Set.is_empty (fst template) then warn_no_template_universe () in
  Template_ind_entry template, global
| Some true, UState.Polymorphic_entry _ ->
  user_err Pp.(strbrk "Template-polymorphism and universe polymorphism are not compatible.")
| None, UState.Polymorphic_entry (uctx, variances) ->
  Polymorphic_ind_entry (uctx, variances), Univ.ContextSet.empty
| None, UState.Monomorphic_entry uctx ->
  let template_candidate = template_polymorphism_candidate uctx ctx_params entry template_syntax in
  let has_template = not @@ Univ.Level.Set.is_empty template_candidate in
  let template = should_auto_template entry.mind_entry_typename has_template in
  if template then
    let template, global = split_universe_context template_candidate uctx in
    Template_ind_entry template, global
  else Monomorphic_ind_entry, uctx

let check_param = function
| CLocalDef (na, _, _, _) -> check_named na
| CLocalAssum (nas, _, Default _, _) -> List.iter check_named nas
| CLocalAssum (nas, _, Generalized _, _) -> ()
| CLocalPattern {CAst.loc} ->
  Loc.raise ?loc (Gramlib.Grammar.Error "pattern with quote not allowed here")

let restrict_inductive_universes ~lbound sigma ctx_params arities constructors =
  let merge_universes_of_constr c =
    Univ.Level.Set.union (snd (EConstr.universes_of_constr sigma (EConstr.of_constr c))) in
  let uvars = Univ.Level.Set.empty in
  let uvars = Context.Rel.(fold_outside (Declaration.fold_constr merge_universes_of_constr) ctx_params ~init:uvars) in
  let uvars = List.fold_right merge_universes_of_constr arities uvars in
  let uvars = List.fold_right (fun (_,ctypes) -> List.fold_right merge_universes_of_constr ctypes) constructors uvars in
  Evd.restrict_universe_context ~lbound sigma uvars

let check_trivial_variances = function
  | None -> ()
  | Some variances ->
    Array.iter (function
      | UVars.Variance.Invariant, _ -> ()
      | _ ->
        CErrors.user_err
          Pp.(strbrk "Universe variance was specified but this inductive will not be cumulative."))
    variances

let variance_of_entry ~cumulative ctx variances =
  let ivariances = Option.map UVars.Variances.repr variances in
  if not cumulative then begin check_trivial_variances ivariances; variances end
  else
    match ivariances with
    | None -> variances
    | Some variances ->
      let lvs = Array.length variances in
      let _, lus = UVars.UContext.size ctx in
      assert (lvs <= lus);
      Some (UVars.Variances.of_array (Array.append variances (Array.make (lus - lvs) UVars.(VariancePos.make Variance.Invariant Position.InTerm))))

let interp_mutual_inductive_constr ~sigma ~flags ~udecl ~ctx_params ~indnames ~arities_explicit ~arities ~template_syntax ~constructors ~env_ar_params ~private_ind =
  let {
    poly;
    cumulative;
    template;
    auto_prop_lowering;
    finite;
  } = flags in
  (* Compute renewed arities *)
  let ctor_args =  List.map (fun (_,tys) ->
      List.map (fun ty ->
          let ctx = fst (Reductionops.whd_decompose_prod_decls env_ar_params sigma ty) in
          ctx)
        tys)
      constructors
  in
  let sigma, (default_dep_elim, arities) = inductive_levels ~auto_prop_lowering env_ar_params sigma ~poly ~indnames ~arities_explicit arities ctor_args in
  let lbound = if poly then UGraph.Bound.Set else UGraph.Bound.Prop in
  let ivariances = UnivVariances.universe_variances_of_inductive env_ar_params sigma ~params:ctx_params ~arities ~constructors in
  let sigma, ivariances = Evd.minimize_universes ~lbound ~variances:ivariances sigma in
  let arities = List.map EConstr.(to_constr sigma) arities in
  let constructors = List.map (on_snd (List.map (EConstr.to_constr sigma))) constructors in
  let ctx_params = List.map (fun d -> EConstr.to_rel_decl sigma d) ctx_params in
  let sigma = restrict_inductive_universes ~lbound sigma ctx_params arities constructors in
  let UState.{ universes_entry_universes = univ_entry; universes_entry_binders = binders } = Evd.check_univ_decl ~poly ~cumulative sigma ivariances udecl in

  (* Build the inductive entries *)
  let entries = List.map3 (fun indname arity (cnames,ctypes) ->
      { mind_entry_typename = indname;
        mind_entry_arity = arity;
        mind_entry_consnames = cnames;
        mind_entry_lc = ctypes
      })
      indnames arities constructors
  in
  let univ_entry, ctx = match entries, template_syntax with
  | [entry], [template_syntax] ->
    compute_template_inductive ~user_template:template ~ctx_params ~univ_entry entry template_syntax
  | _ ->
    let () = match template with
    | Some true -> user_err Pp.(str "Template-polymorphism not allowed with mutual inductives.")
    | _ -> ()
    in
    match univ_entry with
    | UState.Monomorphic_entry ctx -> Monomorphic_ind_entry, ctx
    | UState.Polymorphic_entry (uctx, variances) ->
      let variances = variance_of_entry ~cumulative uctx variances in
      Polymorphic_ind_entry (uctx, variances), Univ.ContextSet.empty
  in
  (* Build the mutual inductive entry *)
  let mind_ent =
    { mind_entry_params = ctx_params;
      mind_entry_record = None;
      mind_entry_finite = finite;
      mind_entry_inds = entries;
      mind_entry_private = if private_ind then Some false else None;
      mind_entry_universes = univ_entry;
    }
  in
  default_dep_elim, mind_ent, binders, ctx

let interp_params ~unconstrained_sorts env udecl uparamsl paramsl =
  let sigma, udecl = interp_cumul_univ_decl_opt env udecl in
  let sigma, (uimpls, ((env_uparams, ctx_uparams), useruimpls)) =
    interp_context_evars ~program_mode:false ~unconstrained_sorts env sigma uparamsl in
  let sigma, (impls, ((env_params, ctx_params), userimpls)) =
    interp_context_evars ~program_mode:false ~unconstrained_sorts ~impl_env:uimpls env_uparams sigma paramsl
  in
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  sigma, env_params, (ctx_params, env_uparams, ctx_uparams,
  userimpls, useruimpls, impls, udecl)

(* When a hole remains for a param, pretend the param is uniform and
   do the unification.
   [env_ar_par] is [uparams; inds; params]
 *)
let maybe_unify_params_in env_ar_par sigma ~ninds ~nparams ~binders:k c =
  let is_ind sigma k c = match EConstr.kind sigma c with
    | Constr.Rel n ->
      (* env is [uparams; inds; params; k other things] *)
      n > k + nparams && n <= k + nparams + ninds
    | _ -> false
  in
  let rec aux (env,k as envk) sigma c = match EConstr.kind sigma c with
    | Constr.App (h,args) when is_ind sigma k h ->
      Array.fold_left_i (fun i sigma arg ->
          if i >= nparams || not (EConstr.isEvar sigma arg) then sigma
          else begin try Evarconv.unify_delay env sigma arg (EConstr.mkRel (k+nparams-i))
            with Evarconv.UnableToUnify _ ->
              (* ignore errors, we will get a "Cannot infer ..." error instead *)
              sigma
          end)
        sigma args
    | _ -> Termops.fold_constr_with_full_binders
             env sigma
             (fun d (env,k) -> EConstr.push_rel d env, k+1)
             aux envk sigma c
  in
  aux (env_ar_par,k) sigma c

let interp_mutual_inductive_gen env0 ~flags udecl (uparamsl,paramsl,indl) notations ~private_ind =
  check_all_names_different indl;
  List.iter check_param paramsl;
  if not (List.is_empty uparamsl) && not (List.is_empty notations)
  then user_err (str "Inductives with uniform parameters may not have attached notations.");

  let indnames = List.map (fun ind -> ind.ind_name) indl in
  let ninds = List.length indl in

  (* In case of template polymorphism, we need to compute more constraints *)
  let unconstrained_sorts = not flags.poly in

  let sigma, env_params, (ctx_params, env_uparams, ctx_uparams, userimpls, useruimpls, impls, udecl) =
    interp_params ~unconstrained_sorts env0 udecl uparamsl paramsl
  in

  (* Interpret the arities *)
  let arities = List.map (intern_ind_arity env_params sigma) indl in

  let sigma, arities = List.fold_left_map (pretype_ind_arity ~unconstrained_sorts env_params) sigma arities in
  let arities, relevances, template_syntax, indimpls = List.split4 arities in

  let lift_ctx n ctx =
    let t = EConstr.it_mkProd_or_LetIn EConstr.mkProp ctx in
    let t = EConstr.Vars.lift n t in
    let ctx, _ = EConstr.decompose_prod_decls sigma t in
    ctx
  in
  let ctx_params_lifted, fullarities =
    lift_ctx ninds ctx_params,
    CList.map_i
      (fun i c -> EConstr.Vars.lift i (EConstr.it_mkProd_or_LetIn c ctx_params))
      0 arities
  in
  let env_ar = push_types env_uparams indnames relevances fullarities in
  let env_ar_params = EConstr.push_rel_context ctx_params_lifted env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun impls -> userimpls @ impls) indimpls in
  let impls = compute_internalization_env env_uparams sigma ~impls Inductive indnames fullarities indimpls in
  let ntn_impls = compute_internalization_env env_uparams sigma Inductive indnames fullarities indimpls in

  let (sigma, _), constructors =
    Metasyntax.with_syntax_protection (fun () ->
        (* Temporary declaration of notations and scopes *)
        List.iter (Metasyntax.set_notation_for_interpretation env_params ntn_impls) notations;
        (* Interpret the constructor types *)
        List.fold_left2_map
          (fun (sigma, ind_rel) ind arity ->
            interp_cstrs env_ar_params (sigma, ind_rel) impls ctx_params_lifted
              ind (EConstr.Vars.liftn ninds (Rel.length ctx_params + 1) arity))
          (sigma, ninds) indl arities)
      ()
  in

  let nparams = Context.Rel.length ctx_params in
  let sigma =
    List.fold_left (fun sigma (_,ctyps,_) ->
        List.fold_left (fun sigma ctyp ->
            maybe_unify_params_in env_ar_params sigma ~ninds ~nparams ~binders:0 ctyp)
          sigma ctyps)
      sigma constructors
  in

  (* generalize over the uniform parameters *)
  let nuparams = Context.Rel.length ctx_uparams in
  let uargs = Context.Rel.instance EConstr.mkRel 0 ctx_uparams in
  let uparam_subst =
    List.init ninds EConstr.(fun i -> mkApp (mkRel (i + 1 + nuparams), uargs))
    @ List.init nuparams EConstr.(fun i -> mkRel (i + 1)) in
  let generalize_constructor c = EConstr.Vars.substnl uparam_subst nparams c in
  let cimpls = List.map pi3 constructors in
  let constructors = List.map (fun (cnames,ctypes,cimpls) ->
      (cnames,List.map generalize_constructor ctypes))
      constructors
  in
  let ctx_params = ctx_params @ ctx_uparams in
  let userimpls = useruimpls @ userimpls in
  let indimpls = List.map (fun iimpl -> useruimpls @ iimpl) indimpls in
  let fullarities = List.map (fun c -> EConstr.it_mkProd_or_LetIn c ctx_uparams) fullarities in
  let env_ar = push_types env0 indnames relevances fullarities in
  let env_ar_params = EConstr.push_rel_context ctx_params env_ar in
  (* Try further to solve evars, and instantiate them *)
  let sigma = solve_remaining_evars all_and_fail_flags env_params sigma in
  let impls =
    List.map2 (fun indimpls cimpls ->
        indimpls, List.map (fun impls ->
            userimpls @ impls) cimpls)
      indimpls cimpls
  in
  let arities_explicit = List.map (fun ar -> ar.ind_arity_explicit) indl in
  let default_dep_elim, mie, binders, ctx = interp_mutual_inductive_constr ~flags ~sigma ~ctx_params ~udecl ~arities_explicit ~arities ~template_syntax ~constructors ~env_ar_params ~private_ind ~indnames in
  (default_dep_elim, mie, binders, impls, ctx)


(* Very syntactical equality *)
let eq_local_binders bl1 bl2 =
  List.equal local_binder_eq bl1 bl2

let eq_params (up1,p1) (up2,p2) =
  eq_local_binders up1 up2 && Option.equal eq_local_binders p1 p2

let extract_coercions indl =
  let mkqid (_,({CAst.v=id},_)) = qualid_of_ident id in
  let iscoe (_, coe, inst) = match inst with
    | Vernacexpr.NoInstance -> coe = Vernacexpr.AddCoercion
    | _ -> user_err (Pp.str "'::' not allowed in inductives.") in
  let extract lc = List.filter (fun (coe,_) -> iscoe coe) lc in
  List.map mkqid (List.flatten(List.map (fun (_,_,_,lc) -> extract lc) indl))

exception DifferingParams of
    string (* inductive or record *)
    * (Id.t * Vernacexpr.inductive_params_expr)
    * (Id.t * Vernacexpr.inductive_params_expr)

let explain_differing_params kind (ind,p) (ind',p') =
  let pr_params = function
    | ([],None) -> str "no parameters"
    | (up,p) ->
      let env = Global.env() in
      let sigma = Evd.from_env env in
      let pr_binders = Ppconstr.pr_binders env sigma in
      str "parameters" ++ spc() ++ hov 1 (quote (pr_binders up ++ pr_opt (fun p -> str "|" ++ spc() ++ pr_binders p) p))
  in
  v 0
    (str "Parameters should be syntactically the same for each " ++ str kind ++ str " type." ++ spc() ++
     hov 0 (str "Type " ++ quote (Id.print ind) ++ str " has " ++ pr_params p) ++ spc() ++
     hov 0 (str "but type " ++ quote (Id.print ind') ++ str " has " ++ pr_params p') ++ str ".")

let () = CErrors.register_handler (function
    | DifferingParams (kind, a, b) -> Some (explain_differing_params kind a b)
    | _ -> None)

let error_differing_params ~kind (ind,p) (ind',p') =
  Loc.raise ?loc:ind'.CAst.loc (DifferingParams (kind, (ind.CAst.v,p), (ind'.CAst.v,p')))

let extract_params indl =
  match indl with
  | [] -> anomaly (Pp.str "empty list of inductive types.")
  | (ind,params,_,_)::rest ->
    match List.find_opt (fun (_,p',_,_) -> not @@ eq_params params p') rest with
    | None -> params
    | Some (ind',p',_,_) ->
      error_differing_params ~kind:"inductive" (ind,params) (ind',p')

let extract_inductive indl =
  List.map (fun ({CAst.v=indname},_,ar,lc) -> {
    ind_name = indname;
    ind_arity_explicit = Option.has_some ar;
    ind_arity = Option.default (CAst.make @@ CSort (Constrexpr_ops.expr_Type_sort UState.univ_flexible)) ar;
    ind_lc = List.map (fun (_,({CAst.v=id},t)) -> (id,t)) lc
  }) indl

let extract_mutual_inductive_declaration_components indl =
  let indl,ntnl = List.split indl in
  let params = extract_params indl in
  let coes = extract_coercions indl in
  let indl = extract_inductive indl in
  (params,indl), coes, List.flatten ntnl

type uniform_inductive_flag =
  | UniformParameters
  | NonUniformParameters

module Mind_decl = struct

type t = {
  mie : Entries.mutual_inductive_entry;
  default_dep_elim : default_dep_elim list;
  nuparams : int option;
  univ_binders : UnivNames.universe_binders;
  implicits : DeclareInd.one_inductive_impls list;
  uctx : Univ.ContextSet.t;
  where_notations : Metasyntax.notation_interpretation_decl list;
  coercions : Libnames.qualid list;
  indlocs : DeclareInd.indlocs;
}

end

let rec count_binder_expr = function
  | [] -> 0
  | CLocalAssum(l,_,_,_) :: rest -> List.length l + count_binder_expr rest
  | CLocalDef _ :: rest -> 1 + count_binder_expr rest
  | CLocalPattern {CAst.loc} :: _ ->
    Loc.raise ?loc (Gramlib.Grammar.Error "pattern with quote not allowed here")

let interp_mutual_inductive ~env ~flags ?typing_flags udecl indl ~private_ind ~uniform =
  let indlocs = List.map (fun ((n,_,_,constructors),_) ->
      let conslocs = List.map (fun (_,(c,_)) -> c.CAst.loc) constructors in
      n.CAst.loc, conslocs)
      indl
  in
  let (params,indl),coercions,ntns = extract_mutual_inductive_declaration_components indl in
  let where_notations = List.map Metasyntax.prepare_where_notation ntns in
  (* Interpret the types *)
  let indl, nuparams = match params with
    | uparams, Some params -> (uparams, params, indl), Some (count_binder_expr params)
    | params, None -> match uniform with
      | UniformParameters -> (params, [], indl), Some 0
      | NonUniformParameters -> ([], params, indl), None
  in
  let env = Environ.update_typing_flags ?typing_flags env in
  let default_dep_elim, mie, univ_binders, implicits, uctx = interp_mutual_inductive_gen ~flags env udecl indl where_notations ~private_ind in
  let open Mind_decl in
  { mie; default_dep_elim; nuparams; univ_binders; implicits; uctx; where_notations; coercions; indlocs }

let do_mutual_inductive ~flags ?typing_flags udecl indl ~private_ind ~uniform =
  let open Mind_decl in
  let env = Global.env () in
  let { mie; default_dep_elim; univ_binders; implicits; uctx; where_notations; coercions; indlocs} =
    interp_mutual_inductive ~flags ~env udecl indl ?typing_flags ~private_ind ~uniform in
  (* Slightly hackish global universe declaration due to template types. *)
  let univ_entry =
    let uentry, binders = match mie.mind_entry_universes with
    | Monomorphic_ind_entry -> (UState.Monomorphic_entry uctx, univ_binders)
    | Template_ind_entry ctx -> (UState.Monomorphic_entry (Univ.ContextSet.union uctx ctx), univ_binders)
    | Polymorphic_ind_entry (uctx, variances) -> (UState.Polymorphic_entry (uctx, variances), UnivNames.empty_binders)
    in UState.{ universes_entry_universes = uentry; universes_entry_binders = binders }
  in
  (* Declare the global universes *)
  Global.push_context_set uctx;
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (DeclareInd.declare_mutual_inductive_with_eliminations ~default_dep_elim ?typing_flags ~indlocs mie univ_entry implicits);
  (* Declare the possible notations of inductive types *)
  List.iter (Metasyntax.add_notation_interpretation ~local:false (Global.env ())) where_notations;
  (* Declare the coercions *)
  List.iter (fun qid -> ComCoercion.try_add_new_coercion (Nametab.locate qid) ~local:false ~reversible:true) coercions

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

(*

  HH notes in PR #679:

  The Show Match could also be made more robust, for instance in the
  presence of let in the branch of a constructor. A
  decompose_prod_decls would probably suffice for that, but then, it
  is a Context.Rel.Declaration.t which needs to be matched and not
  just a pair (name,type).

  Otherwise, this is OK. After all, the API on inductive types is not
  so canonical in general, and in this simple case, working at the
  low-level of mind_nf_lc seems reasonable (compared to working at the
  higher-level of Inductiveops).

*)

let make_cases ind =
  let open Declarations in
  let mib, mip = Global.lookup_inductive ind in
  Util.Array.fold_right_i
    (fun i (ctx, _) l ->
       let al = Util.List.skipn (List.length mib.mind_params_ctxt) (List.rev ctx) in
       let rec rename avoid = function
         | [] -> []
         | RelDecl.LocalDef _ :: l -> "_" :: rename avoid l
         | RelDecl.LocalAssum (n, _)::l ->
           let n' = Namegen.next_name_away_with_default (Id.to_string Namegen.default_dependent_ident) n.Context.binder_name avoid in
           Id.to_string n' :: rename (Id.Set.add n' avoid) l in
       let al' = rename Id.Set.empty al in
       let consref = GlobRef.ConstructRef (ith_constructor_of_inductive ind (i + 1)) in
       (Libnames.string_of_qualid (Nametab.shortest_qualid_of_global Id.Set.empty consref) :: al') :: l)
    mip.mind_nf_lc []

module Internal =
struct

let inductive_levels = inductive_levels

let error_differing_params = error_differing_params

end
