(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

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

module RelDecl = Context.Rel.Declaration

(* 3b| Mutual inductive definitions *)

let warn_auto_template =
  CWarnings.create ~name:"auto-template" ~category:"vernacular" ~default:CWarnings.Disabled
    (fun id ->
       Pp.(strbrk "Automatically declaring " ++ Id.print id ++
           strbrk " as template polymorphic. Use attributes or " ++
           strbrk "disable Auto Template Polymorphism to avoid this warning."))

let should_auto_template =
  let open Goptions in
  let auto = ref true in
  let () = declare_bool_option
      { optdepr  = false;
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
    | GSort (UAnonymous {rigid=true}) -> (Some true)
    | GSort (UNamed _) -> (Some false)
    | GProd ( _, _, _, e)
    | GLetIn (_, _, _, e)
    | GLambda (_, _, _, e)
    | GApp (e, _)
    | GCast (e, _, _) -> check_type_conclusion e
    | _ -> None

let make_anonymous_conclusion_flexible sigma = function
  | None -> sigma
  | Some (false, _) -> sigma
  | Some (true, s) ->
    (match EConstr.ESorts.kind sigma s with
     | Type u ->
       (match Univ.Universe.level u with
        | Some u ->
          Evd.make_flexible_variable sigma ~algebraic:true u
        | None -> sigma)
     | _ -> sigma)

let intern_ind_arity env sigma ind =
  let c = intern_gen IsType env sigma ind.ind_arity in
  let impls = Implicit_quantifiers.implicits_of_glob_constr ~with_products:true c in
  let pseudo_poly = check_type_conclusion c in
  (constr_loc ind.ind_arity, c, impls, pseudo_poly)

let pretype_ind_arity env sigma (loc, c, impls, pseudo_poly) =
  let sigma,t = understand_tcc env sigma ~expected_type:IsType c in
  match Reductionops.sort_of_arity env sigma t with
  | exception Reduction.NotArity ->
    user_err ?loc (str "Not an arity")
  | s ->
    let concl = match pseudo_poly with
      | Some b -> Some (b, s)
      | None -> None
    in
    sigma, (t, Retyping.relevance_of_sort s, concl, impls)

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
  sigma, EConstr.mkApp (EConstr.mkApp (model_head, model_params), Array.of_list (List.rev model_indices))

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
    let ctx, concl = Reductionops.splay_prod_assum env sigma ctyp in
    let concl_env = EConstr.push_rel_context ctx env in
    let sigma_with_model_evars, model =
      model_conclusion concl_env sigma ind_rel params (Context.Rel.length ctx) arity_indices
    in
    (* unify the expected with the provided conclusion *)
    let sigma =
      try Evarconv.unify concl_env sigma_with_model_evars Reduction.CONV concl model
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

(** FIXME: This is a horrible hack, use a saner heuristic *)
let max_sort s1 s2 = match s1, s2 with
| (SProp, SProp) | (Prop, Prop) | (Set, Set) -> s1
| (SProp, (Prop | Set | Type _ as s)) | ((Prop | Set | Type _) as s, SProp) -> s
| (Prop, (Set | Type _ as s)) | ((Set | Type _) as s, Prop) -> s
| (Set, Type u) | (Type u, Set) -> Sorts.sort_of_univ (Univ.Universe.sup Univ.Universe.type0 u)
| (Type u, Type v) -> Sorts.sort_of_univ (Univ.Universe.sup u v)

let compute_constructor_level env evd sign =
  fst (List.fold_right
    (fun d (lev,env) ->
      match d with
      | LocalDef _ -> lev, EConstr.push_rel d env
      | LocalAssum _ ->
        let s = Retyping.get_sort_of env evd (RelDecl.get_type d) in
          (max_sort s lev, EConstr.push_rel d env))
    sign (Sorts.sprop,env))

let sign_level env sigma sign =
  compute_constructor_level env sigma (EConstr.of_rel_context sign)

let sup_list min = List.fold_left max_sort min

let extract_level env evd min tys =
  let sorts = List.map (fun ty ->
    let ctx, concl = Reduction.dest_prod_assum env ty in
      sign_level env evd (LocalAssum (make_annot Anonymous Sorts.Relevant, concl) :: ctx)) tys
  in sup_list min sorts

let is_flexible_sort evd s = match s with
| Set | Prop | SProp -> false
| Type u ->
  match Univ.Universe.level u with
  | Some l -> Evd.is_flexible_level evd l
  | None -> false

(**********************************************************************)
(* Tools for template polymorphic inductive types                         *)

(* Miscellaneous functions to remove or test local univ assumed to
   occur only in the le constraints *)

(*
   Solve a system of universe constraint of the form

   u_s11, ..., u_s1p1, w1 <= u1
   ...
   u_sn1, ..., u_snpn, wn <= un

where

  - the ui (1 <= i <= n) are universe variables,
  - the sjk select subsets of the ui for each equations,
  - the wi are arbitrary complex universes that do not mention the ui.
*)

let is_direct_sort_constraint s v = match s with
| None -> false
| Some u ->
  match v with
  | Sorts.Prop | Sorts.Set | Sorts.SProp -> false
  | Sorts.Type v -> Univ.univ_level_mem u v

let solve_constraints_system levels level_bounds =
  let open Univ in
  let levels =
    Array.mapi (fun i o ->
      match o with
      | Some u ->
        (match Universe.level u with
        | Some u -> Some u
        | _ -> level_bounds.(i) <- max_sort level_bounds.(i) (Sorts.sort_of_univ u); None)
      | None -> None)
      levels in
  let v = Array.copy level_bounds in
  let nind = Array.length v in
  let clos = Array.map (fun _ -> Int.Set.empty) levels in
  (* First compute the transitive closure of the levels dependencies *)
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && is_direct_sort_constraint levels.(j) v.(i) then
        clos.(i) <- Int.Set.add j clos.(i);
    done;
  done;
  let rec closure () =
    let continue = ref false in
      Array.iteri (fun i deps ->
        let deps' =
          Int.Set.fold (fun j acc -> Int.Set.union acc clos.(j)) deps deps
        in
          if Int.Set.equal deps deps' then ()
          else (clos.(i) <- deps'; continue := true))
        clos;
      if !continue then closure ()
      else ()
  in
  closure ();
  for i=0 to nind-1 do
    for j=0 to nind-1 do
      if not (Int.equal i j) && Int.Set.mem j clos.(i) then
        (v.(i) <- max_sort v.(i) level_bounds.(j));
    done;
  done;
  v

let inductive_levels env evd arities inds =
  let destarities = List.map (fun x -> x, Reduction.dest_arity env x) arities in
  let map (x, (ctx, s)) = match s with
  | Prop | SProp -> None
  | Set -> Some Univ.Universe.type0
  | Type u -> Some u
  in
  let levels = List.map map destarities in
  let cstrs_levels, sizes =
    CList.split (List.map2 (fun (_,tys) (arity,(ctx,du)) ->
        let len = List.length tys in
        let minlev = du in
        let minlev =
          if len > 1 && not (is_impredicative_sort env du) then
            max_sort minlev Sorts.set
          else minlev
        in
        let minlev =
          (* Indices contribute. *)
          if indices_matter env then begin
            let ilev = sign_level env evd ctx in
            max_sort ilev minlev
          end
          else minlev
        in
        let clev = extract_level env evd minlev tys in
        (clev, len))
        inds destarities)
  in
  (* Take the transitive closure of the system of constructors *)
  (* level constraints and remove the recursive dependencies *)
  let levels' = solve_constraints_system (Array.of_list levels)
    (Array.of_list cstrs_levels)
  in
  let evd, arities =
    CList.fold_left3 (fun (evd, arities) cu (arity,(ctx,du)) len ->
      if is_impredicative_sort env du then
        (* Any product is allowed here. *)
        evd, (false, arity) :: arities
      else (* If in a predicative sort, or asked to infer the type,
              we take the max of:
              - indices (if in indices-matter mode)
              - constructors
              - Type(1) if there is more than 1 constructor
           *)
        (* Constructors contribute. *)
        let evd =
          if Sorts.is_set du then
            if not (Evd.check_leq evd cu Sorts.set) then
              raise (InductiveError LargeNonPropInductiveNotInType)
            else evd
          else evd
        in
        let evd =
          if len >= 2 && Sorts.is_prop cu then
           (* "Polymorphic" type constraint and more than one constructor,
               should not land in Prop. Add constraint only if it would
               land in Prop directly (no informative arguments as well). *)
            Evd.set_leq_sort env evd Sorts.set du
          else evd
        in
        let template_prop, evd, arity =
          if not (Sorts.is_small du) && Sorts.equal cu du then
            if is_flexible_sort evd du && not (Evd.check_leq evd Sorts.set du)
            then if Term.isArity arity
            (* If not a syntactic arity, the universe may be used in a
               polymorphic instance and so cannot be lowered to Prop.
               See #13300. *)
              then
                (* Workaround: the kernel does not handle non-Prop unbounded
                   arities. In this situation we have no constraints from the
                   constructor so we cook up a new type and unify the unbound
                   universe to a dummy value. *)
                let evd = Evd.set_eq_sort env evd Sorts.set du in
                true, evd, Term.mkArity (ctx, Sorts.prop)
              else false, Evd.set_eq_sort env evd Sorts.set du, arity
            else false, evd, arity
          else false, Evd.set_eq_sort env evd cu du, arity
        in
          (evd, (template_prop, arity) :: arities))
    (evd,[]) (Array.to_list levels') destarities sizes
  in evd, List.rev arities

let check_named {CAst.loc;v=na} = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err ?loc  msg

(* Returns the list [x_1, ..., x_n] of levels contributing to template
   polymorphism. The elements x_k is None if the k-th parameter
   (starting from the most recent and ignoring let-definitions) is not
   contributing to the inductive type's sort or is Some u_k if its level
   is u_k and is contributing. *)
let template_polymorphic_univs ~ctor_levels uctx paramsctxt concl =
  let unbounded_from_below u cstrs =
    let open Univ in
    Univ.Constraints.for_all (fun (l, d, r) ->
        match d with
        | Eq -> not (Univ.Level.equal l u) && not (Univ.Level.equal r u)
        | Lt | Le -> not (Univ.Level.equal r u))
      cstrs
  in
  let check_level l =
    Univ.Level.Set.mem l (Univ.ContextSet.levels uctx) &&
    (let () = assert (not @@ Univ.Level.is_set l) in true) &&
    unbounded_from_below l (Univ.ContextSet.constraints uctx) &&
    not (Univ.Level.Set.mem l ctor_levels)
  in
  let univs = match concl with
  | Prop | Set | SProp -> Univ.Level.Set.empty
  | Type u -> Univ.Universe.levels u
  in
  let univs = Univ.Level.Set.filter (fun l -> check_level l) univs in
  match concl with
  | Prop -> true
  | Set | SProp | Type _ -> not @@ Univ.Level.Set.is_empty univs

let template_polymorphism_candidate ~ctor_levels uctx params concl =
  match uctx with
  | UState.Monomorphic_entry uctx ->
    let concltemplate = Option.cata (fun s -> not (Sorts.is_small s)) false concl in
    if not concltemplate then false
    else
      let conclu = Option.default Sorts.prop concl in
      template_polymorphic_univs ~ctor_levels uctx params conclu
  | UState.Polymorphic_entry _ -> false

let check_param = function
| CLocalDef (na, _, _) -> check_named na
| CLocalAssum (nas, Default _, _) -> List.iter check_named nas
| CLocalAssum (nas, Generalized _, _) -> ()
| CLocalPattern {CAst.loc} ->
    Loc.raise ?loc (Stream.Error "pattern with quote not allowed here")

let restrict_inductive_universes sigma ctx_params arities constructors =
  let merge_universes_of_constr c =
    Univ.Level.Set.union (EConstr.universes_of_constr sigma (EConstr.of_constr c)) in
  let uvars = Univ.Level.Set.empty in
  let uvars = Context.Rel.(fold_outside (Declaration.fold_constr merge_universes_of_constr) ctx_params ~init:uvars) in
  let uvars = List.fold_right merge_universes_of_constr arities uvars in
  let uvars = List.fold_right (fun (_,ctypes) -> List.fold_right merge_universes_of_constr ctypes) constructors uvars in
  Evd.restrict_universe_context sigma uvars

let check_trivial_variances variances =
  Array.iter (function
      | None | Some Univ.Variance.Invariant -> ()
      | Some _ ->
        CErrors.user_err
          Pp.(strbrk "Universe variance was specified but this inductive will not be cumulative."))
    variances

let variance_of_entry ~cumulative ~variances uctx =
  match uctx with
  | Monomorphic_ind_entry | Template_ind_entry _ -> check_trivial_variances variances; None
  | Polymorphic_ind_entry uctx ->
    if not cumulative then begin check_trivial_variances variances; None end
    else
      let lvs = Array.length variances in
      let lus = Univ.UContext.size uctx in
      assert (lvs <= lus);
      Some (Array.append variances (Array.make (lus - lvs) None))

let interp_mutual_inductive_constr ~sigma ~template ~udecl ~variances ~ctx_params ~indnames ~arities ~arityconcl ~constructors ~env_ar_params ~cumulative ~poly ~private_ind ~finite =
  (* Compute renewed arities *)
  let sigma = Evd.minimize_universes sigma in
  let nf = Evarutil.nf_evars_universes sigma in
  let constructors = List.map (on_snd (List.map nf)) constructors in
  let arities = List.map EConstr.(to_constr sigma) arities in
  let sigma = List.fold_left make_anonymous_conclusion_flexible sigma arityconcl in
  let sigma, arities = inductive_levels env_ar_params sigma arities constructors in
  let sigma = Evd.minimize_universes sigma in
  let nf = Evarutil.nf_evars_universes sigma in
  let arities = List.map (on_snd nf) arities in
  let constructors = List.map (on_snd (List.map nf)) constructors in
  let ctx_params = List.map Termops.(map_rel_decl (EConstr.to_constr sigma)) ctx_params in
  let arityconcl = List.map (Option.map (fun (_anon, s) -> EConstr.ESorts.kind sigma s)) arityconcl in
  let sigma = restrict_inductive_universes sigma ctx_params (List.map snd arities) constructors in
  let univ_entry, binders = Evd.check_univ_decl ~poly sigma udecl in

  (* Build the inductive entries *)
  let entries = List.map4 (fun indname (templatearity, arity) concl (cnames,ctypes) ->
      { mind_entry_typename = indname;
        mind_entry_arity = arity;
        mind_entry_consnames = cnames;
        mind_entry_lc = ctypes
      })
      indnames arities arityconcl constructors
  in
  let template =
    if not (Int.equal (List.length indnames) 1) then
      let () = match template with
        | Some true -> user_err Pp.(str "Template-polymorphism not allowed with mutual inductives.")
        | _ -> ()
      in
      List.map (fun _ -> false) indnames
    else
      List.map4 (fun indname (templatearity, _) concl (_, ctypes) ->
          let template_candidate () =
            templatearity ||
            let ctor_levels =
              let add_levels c levels = Univ.Level.Set.union levels (Vars.universes_of_constr c) in
              let param_levels =
                List.fold_left (fun levels d -> match d with
                    | LocalAssum _ -> levels
                    | LocalDef (_,b,t) -> add_levels b (add_levels t levels))
                  Univ.Level.Set.empty ctx_params
              in
              List.fold_left (fun levels c -> add_levels c levels)
                param_levels ctypes
            in
            template_polymorphism_candidate ~ctor_levels univ_entry ctx_params concl
          in
          match template with
          | Some template ->
            if poly && template then user_err
                Pp.(strbrk "Template-polymorphism and universe polymorphism are not compatible.");
            template
          | None ->
            should_auto_template indname (template_candidate ())
        )
        indnames arities arityconcl constructors
  in
  let is_template = List.for_all (fun t -> t) template in
  let univ_entry, ctx = match univ_entry with
  | UState.Monomorphic_entry ctx ->
    if is_template then Template_ind_entry ctx, Univ.ContextSet.empty
    else Monomorphic_ind_entry, ctx
  | UState.Polymorphic_entry uctx ->
    Polymorphic_ind_entry uctx, Univ.ContextSet.empty
  in
  let variance = variance_of_entry ~cumulative ~variances univ_entry in
  (* Build the mutual inductive entry *)
  let mind_ent =
    { mind_entry_params = ctx_params;
      mind_entry_record = None;
      mind_entry_finite = finite;
      mind_entry_inds = entries;
      mind_entry_private = if private_ind then Some false else None;
      mind_entry_universes = univ_entry;
      mind_entry_variance = variance;
    }
  in
  mind_ent, binders, ctx

let interp_params env udecl uparamsl paramsl =
  let sigma, udecl, variances = interp_cumul_univ_decl_opt env udecl in
  let sigma, (uimpls, ((env_uparams, ctx_uparams), useruimpls)) =
    interp_context_evars ~program_mode:false env sigma uparamsl in
  let sigma, (impls, ((env_params, ctx_params), userimpls)) =
    interp_context_evars ~program_mode:false ~impl_env:uimpls env_uparams sigma paramsl
  in
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  sigma, env_params, (ctx_params, env_uparams, ctx_uparams,
  userimpls, useruimpls, impls, udecl, variances)

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

let interp_mutual_inductive_gen env0 ~template udecl (uparamsl,paramsl,indl) notations ~cumulative ~poly ~private_ind finite =
  check_all_names_different indl;
  List.iter check_param paramsl;
  if not (List.is_empty uparamsl) && not (List.is_empty notations)
  then user_err (str "Inductives with uniform parameters may not have attached notations.");

  let indnames = List.map (fun ind -> ind.ind_name) indl in
  let ninds = List.length indl in

  let sigma, env_params, (ctx_params, env_uparams, ctx_uparams, userimpls, useruimpls, impls, udecl, variances) =
    (* In case of template polymorphism, we need to compute more constraints *)
    let env0 = if poly then env0 else Environ.set_universes_lbound env0 UGraph.Bound.Prop in
    interp_params env0 udecl uparamsl paramsl
  in

  (* Interpret the arities *)
  let arities = List.map (intern_ind_arity env_params sigma) indl in

  let sigma, arities = List.fold_left_map (pretype_ind_arity env_params) sigma arities in
  let arities, relevances, arityconcl, indimpls = List.split4 arities in

  let lift_ctx n ctx =
    let t = EConstr.it_mkProd_or_LetIn EConstr.mkProp ctx in
    let t = EConstr.Vars.lift n t in
    let ctx, _ = EConstr.decompose_prod_assum sigma t in
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
  let generalize_constructor c = EConstr.Unsafe.to_constr (EConstr.Vars.substnl uparam_subst nparams c) in
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
  let mie, binders, ctx = interp_mutual_inductive_constr ~template ~sigma ~ctx_params ~udecl ~variances ~arities ~arityconcl ~constructors ~env_ar_params ~poly ~finite ~cumulative ~private_ind ~indnames in
  (mie, binders, impls, ctx)


(* Very syntactical equality *)
let eq_local_binders bl1 bl2 =
  List.equal local_binder_eq bl1 bl2

let eq_params (up1,p1) (up2,p2) =
  eq_local_binders up1 up2 && Option.equal eq_local_binders p1 p2

let extract_coercions indl =
  let mkqid (_,({CAst.v=id},_)) = qualid_of_ident id in
  let extract lc = List.filter (fun (iscoe,_) -> iscoe) lc in
  List.map mkqid (List.flatten(List.map (fun (_,_,_,lc) -> extract lc) indl))

let extract_params indl =
  let paramsl = List.map (fun (_,params,_,_) -> params) indl in
  match paramsl with
  | [] -> anomaly (Pp.str "empty list of inductive types.")
  | params::paramsl ->
      if not (List.for_all (eq_params params) paramsl) then user_err Pp.(str
        "Parameters should be syntactically the same for each inductive type.");
      params

let extract_inductive indl =
  List.map (fun ({CAst.v=indname},_,ar,lc) -> {
    ind_name = indname;
    ind_arity = Option.cata (fun x -> x) (CAst.make @@ CSort (Glob_term.UAnonymous {rigid=true})) ar;
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
  nuparams : int option;
  univ_binders : UnivNames.universe_binders;
  implicits : DeclareInd.one_inductive_impls list;
  uctx : Univ.ContextSet.t;
  where_notations : Metasyntax.where_decl_notation list;
  coercions : Libnames.qualid list;
}

end

let rec count_binder_expr = function
  | [] -> 0
  | CLocalAssum(l,_,_) :: rest -> List.length l + count_binder_expr rest
  | CLocalDef _ :: rest -> 1 + count_binder_expr rest
  | CLocalPattern {CAst.loc} :: _ ->
    Loc.raise ?loc (Stream.Error "pattern with quote not allowed here")

let interp_mutual_inductive ~env ~template udecl indl ~cumulative ~poly ?typing_flags ~private_ind ~uniform finite =
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
  let mie, univ_binders, implicits, uctx = interp_mutual_inductive_gen env ~template udecl indl where_notations ~cumulative ~poly ~private_ind finite in
  let open Mind_decl in
  { mie; nuparams; univ_binders; implicits; uctx; where_notations; coercions }

let do_mutual_inductive ~template udecl indl ~cumulative ~poly ?typing_flags ~private_ind ~uniform finite =
  let open Mind_decl in
  let env = Global.env () in
  let { mie; univ_binders; implicits; uctx; where_notations; coercions } =
    interp_mutual_inductive ~env ~template udecl indl ~cumulative ~poly ?typing_flags ~private_ind ~uniform finite in
  (* Slightly hackish global universe declaration due to template types. *)
  let binders = match mie.mind_entry_universes with
  | Monomorphic_ind_entry -> (UState.Monomorphic_entry uctx, univ_binders)
  | Template_ind_entry ctx -> (UState.Monomorphic_entry ctx, univ_binders)
  | Polymorphic_ind_entry uctx -> (UState.Polymorphic_entry uctx, UnivNames.empty_binders)
  in
  (* Declare the global universes *)
  DeclareUctx.declare_universe_context ~poly:false uctx;
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (DeclareInd.declare_mutual_inductive_with_eliminations ?typing_flags mie binders implicits);
  (* Declare the possible notations of inductive types *)
  List.iter (Metasyntax.add_notation_interpretation ~local:false (Global.env ())) where_notations;
  (* Declare the coercions *)
  List.iter (fun qid -> ComCoercion.try_add_new_coercion (Nametab.locate qid) ~local:false ~poly ~nonuniform:false ~reversible:true) coercions

(** Prepare a "match" template for a given inductive type.
    For each branch of the match, we list the constructor name
    followed by enough pattern variables.
    [Not_found] is raised if the given string isn't the qualid of
    a known inductive type. *)

(*

  HH notes in PR #679:

  The Show Match could also be made more robust, for instance in the
  presence of let in the branch of a constructor. A
  decompose_prod_assum would probably suffice for that, but then, it
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

let compute_constructor_level = compute_constructor_level

end
