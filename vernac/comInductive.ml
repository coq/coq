(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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
open Nameops
open Constrexpr
open Constrexpr_ops
open Constrintern
open Reductionops
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

let rec complete_conclusion a cs = CAst.map_with_loc (fun ?loc -> function
  | CProdN (bl,c) -> CProdN (bl,complete_conclusion a cs c)
  | CLetIn (na,b,t,c) -> CLetIn (na,b,t,complete_conclusion a cs c)
  | CHole (k, _, _) ->
      let (has_no_args,name,params) = a in
      if not has_no_args then
        user_err ?loc
         (strbrk"Cannot infer the non constant arguments of the conclusion of "
          ++ Id.print cs ++ str ".");
      let args = List.map (fun id -> CAst.(make ?loc @@ CRef(qualid_of_ident ?loc id,None))) params in
      CAppExpl ((None,qualid_of_ident ?loc name,None),List.rev args)
  | c -> c
  )

let push_types env idl rl tl =
  List.fold_left3 (fun env id r t -> EConstr.push_rel (LocalAssum (make_annot (Name id) r,t)) env)
    env idl rl tl

type structured_one_inductive_expr = {
  ind_name : Id.t;
  ind_arity : constr_expr;
  ind_lc : (Id.t * constr_expr) list
}

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

let mk_mltype_data sigma env assums arity indname =
  let is_ml_type = is_sort env sigma arity in
  (is_ml_type,indname,assums)

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
    | GCast (e, _) -> check_type_conclusion e
    | _ -> None

let make_anonymous_conclusion_flexible sigma = function
  | None -> sigma
  | Some (false, _) -> sigma
  | Some (true, s) ->
    (match EConstr.ESorts.kind sigma s with
     | Type u ->
       (match Univ.universe_level u with
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
  | exception Invalid_argument _ ->
    user_err ?loc (str "Not an arity")
  | s ->
    let concl = match pseudo_poly with
      | Some b -> Some (b, s)
      | None -> None
    in
    sigma, (t, Retyping.relevance_of_sort s, concl, impls)

let interp_cstrs env sigma impls mldata arity ind =
  let cnames,ctyps = List.split ind.ind_lc in
  (* Complete conclusions of constructor types if given in ML-style syntax *)
  let ctyps' = List.map2 (complete_conclusion mldata) cnames ctyps in
  (* Interpret the constructor types *)
  let sigma, (ctyps'', cimpls) =
    on_snd List.split @@
    List.fold_left_map (fun sigma l ->
        interp_type_evars_impls ~program_mode:false env sigma ~impls l) sigma ctyps' in
  sigma, (cnames, ctyps'', cimpls)

let sign_level env evd sign =
  fst (List.fold_right
    (fun d (lev,env) ->
      match d with
      | LocalDef _ -> lev, push_rel d env
      | LocalAssum _ ->
        let s = Retyping.get_sort_of env evd (EConstr.of_constr (RelDecl.get_type d)) in
        let u = univ_of_sort s in
          (Univ.sup u lev, push_rel d env))
    sign (Univ.Universe.sprop,env))

let sup_list min = List.fold_left Univ.sup min

let extract_level env evd min tys =
  let sorts = List.map (fun ty ->
    let ctx, concl = Reduction.dest_prod_assum env ty in
      sign_level env evd (LocalAssum (make_annot Anonymous Sorts.Relevant, concl) :: ctx)) tys
  in sup_list min sorts

let is_flexible_sort evd u =
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
  | Some u -> Univ.univ_level_mem u v
  | None -> false

let solve_constraints_system levels level_bounds =
  let open Univ in
  let levels =
    Array.mapi (fun i o ->
      match o with
      | Some u ->
        (match Universe.level u with
        | Some u -> Some u
        | _ -> level_bounds.(i) <- Universe.sup level_bounds.(i) u; None)
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
        (v.(i) <- Universe.sup v.(i) level_bounds.(j));
    done;
  done;
  v

let inductive_levels env evd arities inds =
  let destarities = List.map (fun x -> x, Reduction.dest_arity env x) arities in
  let levels = List.map (fun (x,(ctx,a)) ->
    if Sorts.is_prop a || Sorts.is_sprop a then None
    else Some (univ_of_sort a)) destarities
  in
  let cstrs_levels, min_levels, sizes =
    CList.split3
      (List.map2 (fun (_,tys) (arity,(ctx,du)) ->
        let len = List.length tys in
        let minlev = Sorts.univ_of_sort du in
        let minlev =
          if len > 1 && not (is_impredicative_sort env du) then
            Univ.sup minlev Univ.type0_univ
          else minlev
        in
        let minlev =
          (* Indices contribute. *)
          if indices_matter env && List.length ctx > 0 then (
            let ilev = sign_level env evd ctx in
              Univ.sup ilev minlev)
          else minlev
        in
        let clev = extract_level env evd minlev tys in
          (clev, minlev, len)) inds destarities)
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
            if not (Evd.check_leq evd cu Univ.type0_univ) then
              raise (InductiveError LargeNonPropInductiveNotInType)
            else evd
          else evd
        in
        let evd =
          if len >= 2 && Univ.is_type0m_univ cu then
           (* "Polymorphic" type constraint and more than one constructor,
               should not land in Prop. Add constraint only if it would
               land in Prop directly (no informative arguments as well). *)
            Evd.set_leq_sort env evd Sorts.set du
          else evd
        in
        let duu = Sorts.univ_of_sort du in
        let template_prop, evd =
          if not (Univ.is_small_univ duu) && Univ.Universe.equal cu duu then
            if is_flexible_sort evd duu && not (Evd.check_leq evd Univ.type0_univ duu) then
              true, Evd.set_eq_sort env evd Sorts.prop du
            else false, evd
          else false, Evd.set_eq_sort env evd (sort_of_univ cu) du
        in
          (evd, (template_prop, arity) :: arities))
    (evd,[]) (Array.to_list levels') destarities sizes
  in evd, List.rev arities

let check_named {CAst.loc;v=na} = match na with
| Name _ -> ()
| Anonymous ->
  let msg = str "Parameters must be named." in
  user_err ?loc  msg

let template_polymorphism_candidate ~ctor_levels uctx params concl =
  match uctx with
  | Entries.Monomorphic_entry uctx ->
    let concltemplate = Option.cata (fun s -> not (Sorts.is_small s)) false concl in
    if not concltemplate then false
    else
      let conclu = Option.cata Sorts.univ_of_sort Univ.type0m_univ concl in
      Option.has_some @@ IndTyping.template_polymorphic_univs ~ctor_levels uctx params conclu
  | Entries.Polymorphic_entry _ -> false

let check_param = function
| CLocalDef (na, _, _) -> check_named na
| CLocalAssum (nas, Default _, _) -> List.iter check_named nas
| CLocalAssum (nas, Generalized _, _) -> ()
| CLocalPattern {CAst.loc} ->
    Loc.raise ?loc (Stream.Error "pattern with quote not allowed here")

let restrict_inductive_universes sigma ctx_params arities constructors =
  let merge_universes_of_constr c =
    Univ.LSet.union (EConstr.universes_of_constr sigma (EConstr.of_constr c)) in
  let uvars = Univ.LSet.empty in
  let uvars = Context.Rel.(fold_outside (Declaration.fold_constr merge_universes_of_constr) ctx_params ~init:uvars) in
  let uvars = List.fold_right merge_universes_of_constr arities uvars in
  let uvars = List.fold_right (fun (_,ctypes) -> List.fold_right merge_universes_of_constr ctypes) constructors uvars in
  Evd.restrict_universe_context sigma uvars

let interp_mutual_inductive_constr ~sigma ~template ~udecl ~ctx_params ~indnames ~arities ~arityconcl ~constructors ~env_ar_params ~cumulative ~poly ~private_ind ~finite =
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
  let uctx = Evd.check_univ_decl ~poly sigma udecl in

  (* Build the inductive entries *)
  let entries = List.map4 (fun indname (templatearity, arity) concl (cnames,ctypes) ->
      { mind_entry_typename = indname;
        mind_entry_arity = arity;
        mind_entry_consnames = cnames;
        mind_entry_lc = ctypes
      })
      indnames arities arityconcl constructors
  in
  let template = List.map4 (fun indname (templatearity, _) concl (_, ctypes) ->
      let template_candidate () = match concl with
      | Some (Prop | Set | SProp) -> false
      | None | Some (Type _) ->
        templatearity ||
        let ctor_levels =
          let add_levels c levels = Univ.LSet.union levels (Vars.universes_of_constr c) in
          let param_levels =
            List.fold_left (fun levels d -> match d with
                | LocalAssum _ -> levels
                | LocalDef (_,b,t) -> add_levels b (add_levels t levels))
              Univ.LSet.empty ctx_params
          in
          List.fold_left (fun levels c -> add_levels c levels)
            param_levels ctypes
        in
        template_polymorphism_candidate ~ctor_levels uctx ctx_params concl
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
  (* Build the mutual inductive entry *)
  let mind_ent =
    { mind_entry_params = ctx_params;
      mind_entry_record = None;
      mind_entry_finite = finite;
      mind_entry_inds = entries;
      mind_entry_private = if private_ind then Some false else None;
      mind_entry_universes = uctx;
      mind_entry_template = is_template;
      mind_entry_cumulative = poly && cumulative;
    }
  in
  mind_ent, Evd.universe_binders sigma

let interp_params env udecl uparamsl paramsl =
  let sigma, udecl = interp_univ_decl_opt env udecl in
  let sigma, (uimpls, ((env_uparams, ctx_uparams), useruimpls)) =
    interp_context_evars ~program_mode:false env sigma uparamsl in
  let sigma, (impls, ((env_params, ctx_params), userimpls)) =
    interp_context_evars ~program_mode:false ~impl_env:uimpls env_uparams sigma paramsl
  in
  (* Names of parameters as arguments of the inductive type (defs removed) *)
  let assums = List.filter is_local_assum ctx_params in
  sigma, env_params, (ctx_params, env_uparams, ctx_uparams,
  List.map (RelDecl.get_name %> Name.get_id) assums, userimpls, useruimpls, impls, udecl)

let interp_mutual_inductive_gen env0 ~template udecl (uparamsl,paramsl,indl) notations ~cumulative ~poly ~private_ind finite =
  check_all_names_different indl;
  List.iter check_param paramsl;
  if not (List.is_empty uparamsl) && not (List.is_empty notations)
  then user_err (str "Inductives with uniform parameters may not have attached notations.");

  let indnames = List.map (fun ind -> ind.ind_name) indl in

  (* In case of template polymorphism, we need to compute more constraints *)
  let env0 = if poly then env0 else Environ.set_universes_lbound env0 Univ.Level.prop in

  let sigma, env_params, (ctx_params, env_uparams, ctx_uparams, params, userimpls, useruimpls, impls, udecl) =
    interp_params env0 udecl uparamsl paramsl
  in

  (* Interpret the arities *)
  let arities = List.map (intern_ind_arity env_params sigma) indl in

  let sigma, arities = List.fold_left_map (pretype_ind_arity env_params) sigma arities in
  let arities, relevances, arityconcl, indimpls = List.split4 arities in

  let lift1_ctx ctx =
    let t = EConstr.it_mkProd_or_LetIn EConstr.mkProp ctx in
    let t = EConstr.Vars.lift 1 t in
    let ctx, _ = EConstr.decompose_prod_assum sigma t in
    ctx
  in
  let ctx_params_lifted, fullarities = CList.fold_left_map
      (fun ctx_params c -> lift1_ctx ctx_params, EConstr.it_mkProd_or_LetIn c ctx_params)
      ctx_params
      arities
  in
  let env_ar = push_types env_uparams indnames relevances fullarities in
  let env_ar_params = EConstr.push_rel_context ctx_params_lifted env_ar in

  (* Compute interpretation metadatas *)
  let indimpls = List.map (fun impls -> userimpls @ impls) indimpls in
  let impls = compute_internalization_env env_uparams sigma ~impls (Inductive (params,true)) indnames fullarities indimpls in
  let ntn_impls = compute_internalization_env env_uparams sigma (Inductive (params,true)) indnames fullarities indimpls in
  let mldatas = List.map2 (mk_mltype_data sigma env_params params) arities indnames in

  let sigma, constructors =
    Metasyntax.with_syntax_protection (fun () ->
     (* Temporary declaration of notations and scopes *)
     List.iter (Metasyntax.set_notation_for_interpretation env_params ntn_impls) notations;
     (* Interpret the constructor types *)
     List.fold_left3_map (fun sigma -> interp_cstrs env_ar_params sigma impls) sigma mldatas arities indl)
     () in

  (* generalize over the uniform parameters *)
  let nparams = Context.Rel.length ctx_params in
  let nuparams = Context.Rel.length ctx_uparams in
  let uargs = Context.Rel.to_extended_vect EConstr.mkRel 0 ctx_uparams in
  let uparam_subst =
    List.init (List.length indl) EConstr.(fun i -> mkApp (mkRel (i + 1 + nuparams), uargs))
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
  let mie, pl = interp_mutual_inductive_constr ~template ~sigma ~ctx_params ~udecl ~arities ~arityconcl ~constructors ~env_ar_params ~poly ~finite ~cumulative ~private_ind ~indnames in
  (mie, pl, impls)


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

let do_mutual_inductive ~template udecl indl ~cumulative ~poly ~private_ind ~uniform finite =
  let (params,indl),coes,ntns = extract_mutual_inductive_declaration_components indl in
  (* Interpret the types *)
  let indl = match params with
    | uparams, Some params -> (uparams, params, indl)
    | params, None -> match uniform with
      | UniformParameters -> (params, [], indl)
      | NonUniformParameters -> ([], params, indl)
  in
  let mie,pl,impls = interp_mutual_inductive_gen (Global.env()) ~template udecl indl ntns ~cumulative ~poly ~private_ind finite in
  (* Declare the mutual inductive block with its associated schemes *)
  ignore (DeclareInd.declare_mutual_inductive_with_eliminations mie pl impls);
  (* Declare the possible notations of inductive types *)
  List.iter (Metasyntax.add_notation_interpretation (Global.env ())) ntns;
  (* Declare the coercions *)
  List.iter (fun qid -> ComCoercion.try_add_new_coercion (Nametab.locate qid) ~local:false ~poly) coes

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

let declare_mutual_inductive_with_eliminations = DeclareInd.declare_mutual_inductive_with_eliminations
