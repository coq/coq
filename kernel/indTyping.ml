(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Univ
open Term
open Constr
open Declarations
open Environ
open Entries
open Type_errors
open Context.Rel.Declaration

(** Check name unicity.
    Redundant with safe_typing's add_field checks -> to remove?. *)

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names =
  let rec check idset = function
    | [] -> idset
    | c::cl ->
        if Id.Set.mem c idset then
          raise (InductiveError (SameNamesConstructors c))
        else
          check (Id.Set.add c idset) cl
  in
  check

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds ->
        let id = ind.mind_entry_typename in
        let cl = ind.mind_entry_consnames in
        if Id.Set.mem id indset then
          raise (InductiveError (SameNamesTypes id))
        else
          let cstset' = check_constructors_names cstset cl in
          check (Id.Set.add id indset) cstset' inds
  in
  check Id.Set.empty Id.Set.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)


(************************************************************************)
(************************** Type checking *******************************)
(************************************************************************)

type univ_info = { ind_squashed : bool; ind_has_relevant_arg : bool;
                   ind_min_univ : Universe.t option; (* Some for template *)
                   ind_univ : Universe.t;
                   missing : Universe.Set.t; (* missing u <= ind_univ constraints *)
                 }

let check_univ_leq ?(is_real_arg=false) env u info =
  let ind_univ = info.ind_univ in
  let info = if not info.ind_has_relevant_arg && is_real_arg && not (Univ.Universe.is_sprop u)
    then {info with ind_has_relevant_arg=true}
    else info
  in
  (* Inductive types provide explicit lifting from SProp to other universes, so allow SProp <= any. *)
  if type_in_type env || Univ.Universe.is_sprop u || UGraph.check_leq (universes env) u ind_univ
  then { info with ind_min_univ = Option.map (Universe.sup u) info.ind_min_univ }
  else if is_impredicative_univ env ind_univ
       && Option.is_empty info.ind_min_univ then { info with ind_squashed = true }
  else {info with missing = Universe.Set.add u info.missing}

let check_context_univs ~ctor env info ctx =
  let check_one d (info,env) =
    let info = match d with
      | LocalAssum (_,t) ->
        (* could be retyping if it becomes available in the kernel *)
        let tj = Typeops.infer_type env t in
        check_univ_leq ~is_real_arg:ctor env (Sorts.univ_of_sort tj.utj_type) info
      | LocalDef _ -> info
    in
    info, push_rel d env
  in
  fst (Context.Rel.fold_outside ~init:(info,env) check_one ctx)

let check_indices_matter env_params info indices =
  if not (indices_matter env_params) then info
  else check_context_univs ~ctor:false env_params info indices

(* env_ar contains the inductives before the current ones in the block, and no parameters *)
let check_arity ~template env_params env_ar ind =
  let {utj_val=arity;utj_type=_} = Typeops.infer_type env_params ind.mind_entry_arity in
  let indices, ind_sort = Reduction.dest_arity env_params arity in
  let ind_min_univ = if template then Some Universe.type0m else None in
  let univ_info = {
    ind_squashed=false;
    ind_has_relevant_arg=false;
    ind_min_univ;
    ind_univ=Sorts.univ_of_sort ind_sort;
    missing=Universe.Set.empty;
  }
  in
  let univ_info = check_indices_matter env_params univ_info indices in
  (* We do not need to generate the universe of the arity with params;
     if later, after the validation of the inductive definition,
     full_arity is used as argument or subject to cast, an upper
     universe will be generated *)
  let arity = it_mkProd_or_LetIn arity (Environ.rel_context env_params) in
  let x = Context.make_annot (Name ind.mind_entry_typename) (Sorts.relevance_of_sort ind_sort) in
  push_rel (LocalAssum (x, arity)) env_ar,
  (arity, indices, univ_info)

let check_constructor_univs env_ar_par info (args,_) =
  (* We ignore the output, positivity will check that it's the expected inductive type *)
  check_context_univs ~ctor:true env_ar_par info args

let check_constructors env_ar_par isrecord params lc (arity,indices,univ_info) =
  let lc = Array.map_of_list (fun c -> (Typeops.infer_type env_ar_par c).utj_val) lc in
  let splayed_lc = Array.map (Reduction.dest_prod_assum env_ar_par) lc in
  let univ_info = match Array.length lc with
    (* Empty type: all OK *)
    | 0 -> univ_info

    (* SProp primitive records are OK, if we squash and become fakerecord also OK *)
    | 1 when isrecord -> univ_info

    (* Unit and identity types must squash if SProp *)
    | 1 -> check_univ_leq env_ar_par Univ.Universe.type0m univ_info

    (* More than 1 constructor: must squash if Prop/SProp *)
    | _ -> check_univ_leq env_ar_par Univ.Universe.type0 univ_info
  in
  let univ_info = Array.fold_left (check_constructor_univs env_ar_par) univ_info splayed_lc in
  (* generalize the constructors over the parameters *)
  let lc = Array.map (fun c -> Term.it_mkProd_or_LetIn c params) lc in
  (arity, lc), (indices, splayed_lc), univ_info

let check_record data =
  List.for_all (fun (_,(_,splayed_lc),info) ->
      (* records must have all projections definable -> equivalent to not being squashed *)
      not info.ind_squashed
      (* relevant records must have at least 1 relevant argument *)
      && (Univ.Universe.is_sprop info.ind_univ
          || info.ind_has_relevant_arg)
      && (match splayed_lc with
          (* records must have 1 constructor with at least 1 argument, and no anonymous fields *)
          | [|ctx,_|] ->
            let module D = Context.Rel.Declaration in
            List.exists D.is_local_assum ctx &&
            List.for_all (fun d -> not (D.is_local_assum d)
                                   || not (Name.is_anonymous (D.get_name d)))
              ctx
          | _ -> false))
    data

(* Allowed eliminations *)

(* Previous comment: *)
(* Unitary/empty Prop: elimination to all sorts are realizable *)
(* unless the type is large. If it is large, forbids large elimination *)
(* which otherwise allows simulating the inconsistent system Type:Type. *)
(* -> this is now handled by is_smashed: *)
(* - all_sorts in case of small, unitary Prop (not smashed) *)
(* - logical_sorts in case of large, unitary Prop (smashed) *)

let allowed_sorts {ind_squashed;ind_univ;ind_min_univ=_;ind_has_relevant_arg=_;missing=_} =
  if not ind_squashed then InType
  else Sorts.family (Sorts.sort_of_univ ind_univ)

(* For a level to be template polymorphic, it must be introduced
   by the definition (so have no constraint except lbound <= l)
   and not to be constrained from below, so any universe l' <= l
   can be used as an instance of l. All bounds from above, i.e.
   l <=/< r will be valid for any l' <= l. *)
let unbounded_from_below u cstrs =
  Univ.Constraint.for_all (fun (l, d, r) ->
      match d with
      | Eq -> not (Univ.Level.equal l u) && not (Univ.Level.equal r u)
      | Lt | Le -> not (Univ.Level.equal r u))
    cstrs

(* Returns the list [x_1, ..., x_n] of levels contributing to template
   polymorphism. The elements x_k is None if the k-th parameter
   (starting from the most recent and ignoring let-definitions) is not
   contributing to the inductive type's sort or is Some u_k if its level
   is u_k and is contributing. *)
let template_polymorphic_univs ~ctor_levels uctx paramsctxt concl =
  let check_level l =
    Univ.LSet.mem l (Univ.ContextSet.levels uctx) &&
    (let () = assert (not @@ Univ.Level.is_small l) in true) &&
    unbounded_from_below l (Univ.ContextSet.constraints uctx) &&
    not (Univ.LSet.mem l ctor_levels)
  in
  let univs = Univ.Universe.levels concl in
  let univs = Univ.LSet.filter (fun l -> check_level l) univs in
  let fold acc = function
    | (LocalAssum (_, p)) ->
      (let c = Term.strip_prod_assum p in
      match kind c with
        | Sort (Type u) ->
            (match Univ.Universe.level u with
             | Some l -> if Univ.LSet.mem l univs then Some l else None
             | None -> None)
        | _ -> None) :: acc
    | LocalDef _ -> acc
  in
  let params = List.fold_left fold [] paramsctxt in
  if Universe.is_type0m concl then Some (univs, params)
  else if not @@ Univ.LSet.is_empty univs then Some (univs, params)
  else None

let get_param_levels ctx params arity splayed_lc =
  let min_univ = match arity with
  | RegularArity _ ->
    CErrors.user_err
      Pp.(strbrk "Ill-formed template mutual inductive declaration: all types must be template.")
  | TemplateArity ar -> ar.template_level
  in
  let ctor_levels =
    let add_levels c levels = Univ.LSet.union levels (Vars.universes_of_constr c) in
    let param_levels =
      List.fold_left (fun levels d -> match d with
          | LocalAssum _ -> levels
          | LocalDef (_,b,t) -> add_levels b (add_levels t levels))
        Univ.LSet.empty params
    in
    Array.fold_left
      (fun levels (d,c) ->
          let levels =
            List.fold_left (fun levels d ->
                Context.Rel.Declaration.fold_constr add_levels d levels)
              levels d
          in
          add_levels c levels)
      param_levels
      splayed_lc
  in
  match template_polymorphic_univs ~ctor_levels ctx params min_univ with
  | None ->
    CErrors.user_err
      Pp.(strbrk "Ill-formed template inductive declaration: not polymorphic on any universe.")
  | Some (_, param_levels) ->
    param_levels

let get_template univs params data =
  let ctx = match univs with
      | Monomorphic ctx -> ctx
      | Polymorphic _ ->
        CErrors.anomaly ~label:"polymorphic_template_ind"
          Pp.(strbrk "Template polymorphism and full polymorphism are incompatible.") in
  (* For each type in the block, compute potential template parameters *)
  let params = List.map (fun ((arity, _), (_, splayed_lc), _) -> get_param_levels ctx params arity splayed_lc) data in
  (* Pick the lower bound of template parameters. Note that in particular, if
     one of the the inductive types from the block is Prop-valued, then no
     parameters are template. *)
  let fold min params =
    let map u v = match u, v with
    | (None, _) | (_, None) -> None
    | Some u, Some v ->
      let () = assert (Univ.Level.equal u v) in
      Some u
    in
    List.map2 map min params
  in
  let params = match params with
  | [] -> assert false
  | hd :: rem -> List.fold_left fold hd rem
  in
  { template_param_levels = params; template_context = ctx }

let abstract_packets usubst ((arity,lc),(indices,splayed_lc),univ_info) =
  if not (Universe.Set.is_empty univ_info.missing)
  then raise (InductiveError (MissingConstraints (univ_info.missing,univ_info.ind_univ)));
  let arity = Vars.subst_univs_level_constr usubst arity in
  let lc = Array.map (Vars.subst_univs_level_constr usubst) lc in
  let indices = Vars.subst_univs_level_context usubst indices in
  let splayed_lc = Array.map (fun (args,out) ->
      let args = Vars.subst_univs_level_context usubst args in
      let out = Vars.subst_univs_level_constr usubst out in
      args,out)
      splayed_lc
  in
  let ind_univ = Univ.subst_univs_level_universe usubst univ_info.ind_univ in

  let arity = match univ_info.ind_min_univ with
    | None -> RegularArity {mind_user_arity = arity; mind_sort = Sorts.sort_of_univ ind_univ}
    | Some min_univ -> TemplateArity { template_level = min_univ; }
  in

  let kelim = allowed_sorts univ_info in
  (arity,lc), (indices,splayed_lc), kelim

let typecheck_inductive env ~sec_univs (mie:mutual_inductive_entry) =
  let () = match mie.mind_entry_inds with
  | [] -> CErrors.anomaly Pp.(str "empty inductive types declaration.")
  | _ -> ()
  in
  (* Check unicity of names (redundant with safe_typing's add_field checks) *)
  mind_check_names mie;
  assert (List.is_empty (Environ.rel_context env));

  let has_template_poly = mie.mind_entry_template in

  (* universes *)
  let env_univs =
    match mie.mind_entry_universes with
    | Monomorphic_entry ctx ->
      if has_template_poly then
        (* For that particular case, we typecheck the inductive in an environment
           where the universes introduced by the definition are only [>= Prop] *)
        let env = set_universes_lbound env UGraph.Bound.Prop in
        push_context_set ~strict:false ctx env
      else
        (* In the regular case, all universes are [> Set] *)
        push_context_set ~strict:true ctx env
    | Polymorphic_entry (_, ctx) -> push_context ctx env
  in

  (* Params *)
  let env_params, params = Typeops.check_context env_univs mie.mind_entry_params in

  (* Arities *)
  let env_ar, data = List.fold_left_map (check_arity ~template:has_template_poly env_params) env_univs mie.mind_entry_inds in
  let env_ar_par = push_rel_context params env_ar in

  (* Constructors *)
  let isrecord = match mie.mind_entry_record with
    | Some (Some _) -> true
    | Some None | None -> false
  in
  let data = List.map2 (fun ind data ->
      check_constructors env_ar_par isrecord params ind.mind_entry_lc data)
      mie.mind_entry_inds data
  in

  let record = mie.mind_entry_record in
  let data, record = match record with
    | None | Some None -> data, record
    | Some (Some _) ->
      if check_record data then
        data, record
      else
        (* if someone tried to declare a record as SProp but it can't
           be primitive we must squash. *)
        let data = List.map (fun (a,b,univs) ->
            a,b,check_univ_leq env_ar_par Univ.Universe.type0m univs)
            data
        in
        data, Some None
  in

  let variance = if not mie.mind_entry_cumulative then None
    else match mie.mind_entry_universes with
      | Monomorphic_entry _ ->
        CErrors.user_err Pp.(str "Inductive cannot be both monomorphic and universe cumulative.")
      | Polymorphic_entry (_,uctx) ->
        let univs = Instance.to_array @@ UContext.instance uctx in
        let univs = match sec_univs with
          | None -> univs
          | Some sec_univs -> Array.append sec_univs univs
        in
        let variances = InferCumulativity.infer_inductive ~env_params univs mie.mind_entry_inds in
        Some variances
  in

  (* Abstract universes *)
  let usubst, univs = Declareops.abstract_universes mie.mind_entry_universes in
  let params = Vars.subst_univs_level_context usubst params in
  let data = List.map (abstract_packets usubst) data in
  let template =
    let check ((arity, _), _, _) = match arity with
    | TemplateArity _ -> true
    | RegularArity _ -> false
    in
    if List.exists check data then Some (get_template univs params data) else None
  in

  let env_ar_par =
    let ctx = Environ.rel_context env_ar_par in
    let ctx = Vars.subst_univs_level_context usubst ctx in
    let env = Environ.pop_rel_context (Environ.nb_rel env_ar_par) env_ar_par in
    Environ.push_rel_context ctx env
  in

  env_ar_par, univs, template, variance, record, params, Array.of_list data
