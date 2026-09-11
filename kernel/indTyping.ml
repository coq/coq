(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars
open Term
open Constr
open Declarations
open Environ
open Entries
open Type_errors
open Context.Rel.Declaration

type inductive_arity = { user_arity : Constr.types; sort : Sorts.t }

(** Check name unicity.
    Redundant with safe_typing's add_field checks -> to remove?. *)

(* [check_constructors_names id s cl] checks that all the constructors names
   appearing in [l] are not present in the set [s], and returns the new set
   of names. The name [id] is the name of the current inductive type, used
   when reporting the error. *)

let check_constructors_names env idset ids =
  let rec check idset = function
    | [] -> idset
    | c::cl ->
        if Id.Set.mem c idset then
          raise (InductiveError (env, SameNamesConstructors c))
        else
          check (Id.Set.add c idset) cl
  in
  check idset ids

(* [mind_check_names mie] checks the names of an inductive types declaration,
   and raises the corresponding exceptions when two types or two constructors
   have the same name. *)

let mind_check_names env mie =
  let rec check indset cstset = function
    | [] -> ()
    | ind::inds ->
        let id = ind.mind_entry_typename in
        let cl = ind.mind_entry_consnames in
        if Id.Set.mem id indset then
          raise (InductiveError (env, SameNamesTypes id))
        else
          let cstset' = check_constructors_names env cstset cl in
          check (Id.Set.add id indset) cstset' inds
  in
  check Id.Set.empty Id.Set.empty mie.mind_entry_inds
(* The above verification is not necessary from the kernel point of
  vue since inductive and constructors are not referred to by their
  name, but only by the name of the inductive packet and an index. *)


(************************************************************************)
(************************** Type checking *******************************)
(************************************************************************)

type record_arg_info =
  | NoRelevantArg
  | MaybeRelevantArg
  (** At least one arg with variable relevance. *)
  | HasRelevantArg
  (** HasRelevantArg means when the record is relevant at least one arg is relevant.
      When the record is in a polymorphic sort this can mean one arg is in the same sort. *)

type univ_info =
  { ind_squashed : squash_info option
  ; record_arg_info : record_arg_info
  ; ind_template : bool
  ; ind_univ : Sorts.t
  ; missing : Sorts.t list (* missing u <= ind_univ constraints *)
  ; uses_impredicative_set : bool
  }

let add_squash q info =
  match q, Sorts.quality info.ind_univ with
  | Sorts.Quality.QVar _, _ | _, QVar _ ->
    begin match info.ind_squashed with
    | None -> { info with ind_squashed = Some (SometimesSquashed (Sorts.Quality.Set.singleton q)) }
    | Some AlwaysSquashed -> info
    | Some (SometimesSquashed qs) ->
      (* XXX dedup insertion *)
      { info with ind_squashed = Some (SometimesSquashed (Sorts.Quality.Set.add q qs)) }
    end
  | _ ->
    (* no qvar involved: no instantiation can resolve this constraint *)
    { info with ind_squashed = Some AlwaysSquashed }

let compute_elim_squash ?(is_real_arg=false) env u info =
  let open Sorts.Quality in
  let info = if not is_real_arg then info
    else match info.record_arg_info with
      | HasRelevantArg -> info
      | NoRelevantArg | MaybeRelevantArg ->
        match Sorts.relevance_of_sort u with
        | Irrelevant -> info
        | Relevant -> { info with record_arg_info = HasRelevantArg }
        | RelevanceVar q ->
          if Environ.Internal.is_above_prop env q
          || equal (QVar q) (Sorts.quality info.ind_univ)
          then { info with record_arg_info = HasRelevantArg }
          else { info with record_arg_info = MaybeRelevantArg }
  in
  if Environ.ignore_elim_constraints env then info else
  let indu = info.ind_univ in

  if not @@ UGraph.check_leq (universes env) (Sorts.univ_of_sort u) (Sorts.univ_of_sort indu) then
    if Environ.is_impredicative_sort env indu then
      let info = add_squash (Sorts.quality u) info in
      if Sorts.is_set indu then { info with uses_impredicative_set = true }
      else info
    else { info with missing = u :: info.missing }
  else if Inductive.eliminates_to (Environ.qualities env) (Sorts.quality indu) (Sorts.quality u) then
    info
  else match indu, u with
    (* XXX add a constraint q -> Prop in push_template_context,
       then we don't need this above_prop test *)
    | VSort (q, _), (SProp | Prop) when Environ.Internal.is_above_prop env q -> info
    | _ -> add_squash (Sorts.quality u) info

let check_context_univs ~ctor env info ctx =
  let check_one d (info,env) =
    let info = match d with
      | LocalAssum (_,t) ->
        (* could be retyping if it becomes available in the kernel *)
        let tj = Typeops.infer_type env t in
        compute_elim_squash ~is_real_arg:ctor env tj.utj_type info
      | LocalDef _ -> info
    in
    info, push_rel d env
  in
  fst (Context.Rel.fold_outside ~init:(info,env) check_one ctx)

let eq_squashed a b =
  match a, b with
  | SometimesSquashed a, SometimesSquashed b -> Sorts.Quality.Set.equal a b
  | AlwaysSquashed, AlwaysSquashed -> true
  | (SometimesSquashed _ | AlwaysSquashed), _ -> false

let check_indices_matter env_params info indices =
  let with_indices = check_context_univs ~ctor:false env_params info indices in
  let relies_on_indices_not_mattering =
    not (Option.equal eq_squashed info.ind_squashed with_indices.ind_squashed)
    || not (List.equal Sorts.equal info.missing with_indices.missing)
  in
  if indices_matter env_params then
    (* indices constraints are enforced, so this inductive does not
       rely on indices not mattering *)
    (with_indices, false)
  else
    (info, relies_on_indices_not_mattering)

(* env_ar contains the inductives before the current ones in the block, and no parameters *)
let check_arity ~template env_params env_ar (na, arity) =
  let {utj_val=arity;utj_type=_} = Typeops.infer_type env_params arity in
  let indices, ind_sort = Reduction.dest_arity env_params arity in
  let univ_info = {
    ind_squashed=None;
    record_arg_info=NoRelevantArg;
    ind_template = template;
    ind_univ=ind_sort;
    missing=[];
    uses_impredicative_set=false;
  }
  in
  (* We do not need to generate the universe of the arity with params;
     if later, after the validation of the inductive definition,
     full_arity is used as argument or subject to cast, an upper
     universe will be generated *)
  let arity = it_mkProd_or_LetIn arity (Environ.rel_context env_params) in
  let x = Context.make_annot (Name na) (Sorts.relevance_of_sort ind_sort) in
  push_rel (LocalAssum (x, arity)) env_ar,
  (arity, indices, univ_info)

let check_constructor_univs env_ar_par info (args,_) =
  (* We ignore the output, positivity will check that it's the expected inductive type *)
  check_context_univs ~ctor:true env_ar_par info args

(* Detect reliance on impredicative [Set] beyond what the main analysis
   already recorded in [univ_info.uses_impredicative_set] (a constructor
   argument fitting its [Set]-sorted inductive only impredicatively):
   - the arity or the types of the constructors may fail to typecheck at
     all in a predicative environment (e.g. when a subterm needs to fit
     in [Set]);
   - the squashing/elimination analysis may differ in a predicative
     environment. *)
let check_uses_impredicative_set env_ar_par isrecord params indices arity lc splayed_lc univ_info =
  if not (Environ.is_impredicative_set env_ar_par)
     || univ_info.uses_impredicative_set
  then univ_info
  else
    let env_pred = Environ.set_impredicative_set false env_ar_par in
    let fresh_info = { univ_info with ind_squashed = None; missing = []; uses_impredicative_set = false } in
    let analyze env =
      let info =
        if isrecord then fresh_info
        else match Array.length splayed_lc with
        | 0 -> compute_elim_squash env Sorts.sprop fresh_info
        | 1 ->
          if (Environ.typing_flags env).allow_uip
               && fst (splayed_lc.(0)) = []
               && List.for_all Context.Rel.Declaration.is_local_assum params
               && List.for_all Context.Rel.Declaration.is_local_assum indices
               && Sorts.is_sprop fresh_info.ind_univ
          then fresh_info
          else compute_elim_squash env Sorts.prop fresh_info
        | _ -> compute_elim_squash env Sorts.set fresh_info
      in
      Array.fold_left (check_constructor_univs env) info splayed_lc
    in
    match
      (* The full arity re-binds the parameters and indices, so their
         types are covered here; the constructor types are checked
         without generalization, in the environment where the
         parameters and the block's inductives are bound. *)
      let () = ignore (Typeops.infer_type env_pred arity) in
      let () = Array.iter (fun c -> ignore (Typeops.infer_type env_pred c)) lc in
      analyze env_pred
    with
    | exception e when CErrors.noncritical e ->
      { univ_info with uses_impredicative_set = true }
    | pred_info ->
      let imp_info = analyze env_ar_par in
      let differs =
        not (Option.equal eq_squashed pred_info.ind_squashed imp_info.ind_squashed)
        || not (List.equal Sorts.equal pred_info.missing imp_info.missing)
      in
      if differs then { univ_info with uses_impredicative_set = true }
      else univ_info

let check_constructors ~env_params ~env_ar_par isrecord params lc (arity,indices,univ_info) =
  let lc = Array.map_of_list (fun c -> (Typeops.infer_type env_ar_par c).utj_val) lc in
  let splayed_lc = Array.map (Reduction.whd_decompose_prod_decls env_ar_par) lc in
  let univ_info =
    (* SProp and sort poly primitive records are OK, if we squash and become fakerecord also OK *)
    if isrecord then univ_info
    else match Array.length lc with
    (* Empty type: sort poly must squash *)
    | 0 -> compute_elim_squash env_ar_par Sorts.sprop univ_info

    | 1 ->
      (* 1 constructor with no arguments also OK in SProp (to make
         things easier on ourselves when reducing we forbid letins)
         unless ind_univ is sort polymorphic (for ease of implementation) *)
      if (Environ.typing_flags env_ar_par).allow_uip
           && fst (splayed_lc.(0)) = []
           && List.for_all Context.Rel.Declaration.is_local_assum params
           && List.for_all Context.Rel.Declaration.is_local_assum indices
           && Sorts.is_sprop univ_info.ind_univ
      then univ_info
      (* 1 constructor with arguments must squash if SProp / sort poly
         (we could allow arguments in SProp but the reduction rule is a pain) *)
      else compute_elim_squash env_ar_par Sorts.prop univ_info

    (* More than 1 constructor: must squash if Prop/SProp *)
    | _ -> compute_elim_squash env_ar_par Sorts.set univ_info
  in
  let univ_info = Array.fold_left (check_constructor_univs env_ar_par) univ_info splayed_lc in
  let () = if univ_info.ind_template then match univ_info.ind_squashed with
      | None | Some AlwaysSquashed -> ()
      | Some (SometimesSquashed _) ->
      CErrors.user_err Pp.(str "Cannot handle sometimes squashed template polymorphic type.")
  in
  let univ_info = check_uses_impredicative_set env_ar_par isrecord params indices arity lc splayed_lc univ_info in
  (* generalize the constructors over the parameters *)
  let lc = Array.map (fun c -> Term.it_mkProd_or_LetIn c params) lc in
  let univ_info, relies_on_indices_not_mattering = check_indices_matter env_params univ_info indices in
  (arity, lc), (indices, splayed_lc), univ_info, relies_on_indices_not_mattering

module NotPrimRecordReason = struct

  type t =
    | MustNotBeSquashed
    | MustHaveRelevantProj
    | MustHaveProj
    | MustNotHaveAnonProj

end

(* Checks whether the record can have primitive projections, and if so, whether it has eta *)
let check_record ~ignore_elim data =
  let open NotPrimRecordReason in
  List.fold_left (fun res (_, (_, splayed_lc), info, _) ->
      if Result.is_error res then res
      else if Option.has_some info.ind_squashed
      (* records must have all projections definable -> equivalent to not being squashed *)
      then Result.Error MustNotBeSquashed
      else
        let res = match splayed_lc with
          (* records must have 1 constructor with at least 1 argument, and no anonymous fields *)
          (* XXX MustHaveProj is redundant with MustHaveRelevantProj except for SProp records,
             but the condition does not seem useful for SProp records.
             Should we allow 0-projection SProp records? *)
          (* XXX if we stop needing compatibility constants we could allow anonymous projections *)
          | [|ctx,_|] ->
            let module D = Context.Rel.Declaration in
            if not @@ List.exists D.is_local_assum ctx
            then Some MustHaveProj
            else if List.exists (fun d -> D.is_local_assum d && Name.is_anonymous (D.get_name d)) ctx
            then Some MustNotHaveAnonProj
            else None
          | _ -> CErrors.anomaly ~label:"Indtyping.check_record" Pp.(str "not 1 constructor")
        in
        match res with
        | Some reason -> Result.Error reason
        | None -> (* Otherwise, we allow primitive projections but check if it has eta *)
            if ignore_elim then Result.Ok AlwaysEta else
            match info.record_arg_info with
            | HasRelevantArg -> Result.Ok AlwaysEta
            | MaybeRelevantArg ->
              begin match info.ind_univ with
              | SProp -> Result.Ok AlwaysEta
              | _ -> Result.Ok MaybeEta
              end
            | NoRelevantArg ->
              (* If there is no relevant projection, then we consider the sort of the record to decide if it has eta *)
              match info.ind_univ with
              | SProp -> Result.Ok AlwaysEta
              | GSort _ | Set | Type _ | Prop -> Result.Ok NoEta (* relevant sorts don't have eta *)
              | VSort _ ->  Result.Ok MaybeEta (* For sort variables it depends on the instantiation *)
    )
    (Result.Ok NoEta)
    data

(* Template univs must be unbounded from below for subject reduction
   (with partially applied template poly, cf RFC 90).

   We also forbid strict bounds from above because they lead
   to problems when instantiated with algebraic universes
   (template_u < v can become w+1 < v which we cannot yet handle). *)
let check_unbounded_from_below (univs, csts) =
  Univ.UnivConstraints.iter (fun (l,d,r) ->
      let bad = match d with
        | UnivConstraint.Eq | UnivConstraint.Lt ->
          if Level.Set.mem l univs then Some l
          else if Level.Set.mem r univs then Some r
          else None
        | UnivConstraint.Le -> if Level.Set.mem r univs then Some r else None
      in
      bad |> Option.iter (fun bad ->
          CErrors.user_err Pp.(str "Universe level " ++ Level.raw_pr bad ++
                               str " cannot be template because it appears in constraint " ++
                               Level.raw_pr l ++ UnivConstraint.pr_kind d ++ Level.raw_pr r)))
    csts

let check_not_appearing_univs ~template_univs univs =
  let univs = Level.Set.inter template_univs univs in
  if Level.Set.is_empty univs then ()
  else
    CErrors.user_err
      Pp.(str "Template " ++
          str (CString.plural (Level.Set.cardinal univs) "universe") ++
          spc() ++ Level.Set.pr Level.raw_pr univs ++ spc() ++
          str "appear in illegal positions.")

let get_template_binding_arity ~template_univs c =
  let decls, c = Term.decompose_prod_decls c in
  let check_level u = match Universe.level u with
    | None ->
      let () = check_not_appearing_univs ~template_univs (Universe.levels u) in
      None
    | Some l -> if Level.Set.mem l template_univs then Some l else None
  in
  match kind c with
  | Sort (Type u as s) ->
    Some (decls, None, check_level u, s)
  | Sort (VSort (q, u) as s) ->
    (* XXX check if q is a template qvar in anticipation of global qvars existing *)
    Some (decls, Some q, check_level u, s)
  | _ -> None

let check_no_increment ~template_univs u =
  (* forbid template poly with an increment on a template univ in the conclusion
     otherwise repeatedly applying it can generate universes with +2
     which we cannot yet handle. *)
  let has_increment =
    Universe.exists (fun (u,n) ->
        if Level.Set.mem u template_univs then
          not (Int.equal n 0)
        else false) u
  in
  if has_increment then
    CErrors.user_err
      Pp.(str "Template polymorphism with conclusion strictly larger than a bound universe not supported.")

let get_template template_context default_univs params arity lc =
  let ((template_qvars, _), (template_univs, _ as template_uctx)) =
    UVars.UContext.to_context_set (AbstractContext.repr template_context)
  in
  let () = check_unbounded_from_below template_uctx in

  (* Template univs must only appear in the conclusion of the
     inductive and linearly in the conclusion of parameters.
     This makes them Irrelevant for conversion and also makes them easy to substitute.
     The inductive and binding parameter types must be syntactically arities. *)
  let check_not_appearing c =
    let qs, us = Vars.sort_and_universes_of_constr c in
    let qappearing =
      Sorts.QVar.Set.filter (fun qv -> Sorts.Quality.Set.mem (QVar qv) qs)
        template_qvars
    in
    if not (Sorts.QVar.Set.is_empty qappearing) then
      CErrors.user_err
        Pp.(str "Template " ++
            str (if Int.equal 1 (Sorts.QVar.Set.cardinal qappearing) then "quality" else "qualities") ++
            spc() ++ prlist_with_sep spc Sorts.QVar.raw_pr (Sorts.QVar.Set.elements qappearing) ++ spc() ++
            str "appear in illegal positions.")
    else check_not_appearing_univs ~template_univs us
  in
  let check_not_appearing_rel_ctx ctx =
    List.iter (Context.Rel.Declaration.iter_constr check_not_appearing) ctx
  in

  (** params *)
  (* for each non-letin param, find whether it binds a template univ or qvar *)
  let template_params =
    CList.map (fun param ->
        match param with
        | LocalDef (_,b,t) ->
          check_not_appearing b;
          check_not_appearing t;
          None
        | LocalAssum (_,t) ->
          match get_template_binding_arity ~template_univs t with
          | None | Some (_, None, None, _) ->
            check_not_appearing t;
            Some None
          | Some (decls, qopt, lopt, s) ->
            let () = check_not_appearing_rel_ctx decls in
            Some (Some (qopt, lopt, s)))
      params
  in
  let qbound, ubound =
    List.fold_left (fun (qbound, ubound as bound_in_params) -> function
        | None | Some None -> bound_in_params
        | Some (Some (qopt,lopt,_)) ->
          let ubound = match lopt with
            | None -> ubound
            | Some l ->
              if Level.Set.mem l ubound then
                CErrors.user_err Pp.(str "Non-linear template level " ++ Level.raw_pr l)
              else Level.Set.add l ubound
          in
          let qbound = Option.fold_right Sorts.QVar.Set.add qopt qbound in
          qbound, ubound)
      (Sorts.QVar.Set.empty,Level.Set.empty)
      template_params
  in
  let q_unbound = Sorts.QVar.Set.diff template_qvars qbound in
  let () = if not (Sorts.QVar.Set.is_empty q_unbound) then
      CErrors.user_err
        Pp.(str "Template " ++
            str (if Int.equal 1 (Sorts.QVar.Set.cardinal q_unbound) then "quality" else "qualities") ++ spc() ++
            prlist_with_sep spc Sorts.QVar.raw_pr (Sorts.QVar.Set.elements q_unbound) ++ spc() ++
            str "not bound by parameters.")

  in
  let u_unbound = Level.Set.diff template_univs ubound in
  let () = if not (Level.Set.is_empty u_unbound) then
      CErrors.user_err
        Pp.(str "Template " ++
            str (CString.plural (Level.Set.cardinal u_unbound) "universe") ++
            spc() ++ Level.Set.pr Level.raw_pr u_unbound ++ spc() ++
            str "not bound by parameters.")

  in

  (** arity *)
  let template_concl =
    (* don't use get_template_binding_arity, we allow constant template poly (eg eq) *)
    let (decls, s) = Term.decompose_prod_decls arity in
    let () = if not (isSort s) then
        CErrors.user_err Pp.(str "Template polymorphic inductive's type must be a syntactic arity.")
    in
    check_not_appearing_rel_ctx decls;
    let s = destSort s in
    let () = match s with
    | SProp | Prop | Set -> ()
    | VSort (_, u) ->
      (* typechecking will fail with "unbound qvar" if the quality isn't in template_qvars *)
      check_no_increment ~template_univs u;
      ()
    | GSort (_, u) | Type u ->
      check_no_increment ~template_univs u;
      ()
    in
    s
  in

  (** ctors *)
  let () = List.iter check_not_appearing lc in

  let template_param_arguments =
    let assums = CList.filter_map (fun x -> x) template_params in
    List.rev_map (Option.map (fun (_, _, s) -> s)) assums
  in

  (* don't forget to check the default_univs qualities are all QType *)
  let () =
    let () = if not UVars.(eq_sizes (AbstractContext.size template_context) (Instance.length default_univs))
      then CErrors.anomaly Pp.(str "Incorrect default template universes declaration.")
    in
    let default_qs, _ = UVars.Instance.to_array default_univs in
    assert (Array.for_all Sorts.Quality.is_qtype default_qs)
  in

  {
    template_param_arguments;
    template_context;
    template_concl;
    template_defaults = default_univs;
  }

let typecheck_inductive env ~sec_univs (mie:mutual_inductive_entry) =
  let () = match mie.mind_entry_inds with
  | [] -> CErrors.anomaly Pp.(str "empty inductive types declaration.")
  | _ -> ()
  in
  (* Check unicity of names (redundant with safe_typing's add_field checks) *)
  mind_check_names env mie;
  assert (List.is_empty (Environ.rel_context env));

  (* Abstract universes *)
  let env_univs, usubst, univs, template = match mie.mind_entry_universes with
  | Monomorphic_ind_entry ->
    env, UVars.empty_sort_subst, Monomorphic, None
  | Template_ind_entry { uctx; default_univs } ->
    let () =
      let bind_instance = UVars.UContext.instance uctx in
      let _, bind_us = UVars.Instance.to_array bind_instance in
      (* XXX should be checked by UVars.abstract_universes instead *)
      assert (Array.for_all (fun bind_u -> not @@ Level.is_set bind_u) bind_us)
    in
    let (inst, auctx) = UVars.abstract_universes uctx in
    let usubst = UVars.make_instance_subst inst in
    let env = Environ.Internal.push_template_context (AbstractContext.repr auctx) env in
    env, usubst, Monomorphic, Some (default_univs, auctx)
  | Polymorphic_ind_entry uctx ->
    let (inst, auctx) = UVars.abstract_universes uctx in
    let usubst = UVars.make_instance_subst inst in
    let () = check_ucontext (AbstractContext.repr auctx) env in
    let env = Environ.push_context (AbstractContext.repr auctx) env in
    env, usubst, Polymorphic auctx, None
  in

  let params = Vars.subst_univs_level_context usubst mie.mind_entry_params in
  let map mip =
    let arity = Vars.subst_univs_level_constr usubst mip.mind_entry_arity in
    let lc = List.map (fun c -> Vars.subst_univs_level_constr usubst c) mip.mind_entry_lc in
    (mip.mind_entry_typename, arity, lc)
  in
  let blocks = List.map map mie.mind_entry_inds in

  let template = match template with
  | None -> None
  | Some (default_univs, template_context) ->
    let arity, lc = match blocks with
    | [_, arity, lc] -> arity, lc
    | _ -> CErrors.user_err Pp.(str "Template-polymorphism not allowed with mutual inductives.")
    in
    let template = get_template template_context default_univs params arity lc in
    Some template
  in

  let has_template_poly = Option.has_some template in

  (* Params *)
  let env_params, params = Typeops.check_context env_univs params in

  (* Arities *)
  let check_arity env_univs (name, arity, _) =
    check_arity ~template:has_template_poly env_params env_univs (name, arity)
  in
  let env_ar, data = List.fold_left_map check_arity env_univs blocks in
  let env_ar_par = push_rel_context params env_ar in

  (* Constructors *)
  let isrecord = match mie.mind_entry_record with
    | Some (Some _) -> true
    | Some None | None -> false
  in
  let map (_, _, ctyp) data =
    check_constructors ~env_params ~env_ar_par isrecord params ctyp data
  in
  let data = List.map2 map blocks data in

  let record = mie.mind_entry_record in
  let data, record, not_prim_reason_or_has_eta = match record with
    | None | Some None -> data, record, None (* NotRecord or FakeRecord *)
    | Some (Some _) -> (* PrimRecord *)
      (* We check if it can actually have primitive projections & eta *)
      match check_record ~ignore_elim:(Environ.ignore_elim_constraints env_ar_par) data with
      | Result.Ok has_eta ->
        let has_eta = match mie.mind_entry_finite with
          | BiFinite -> has_eta
          | Finite | CoFinite -> NoEta
        in
        data, record, Some (Result.Ok has_eta)
      | Result.Error _ as reason ->
        (* if someone tried to declare a record as SProp but it can't
           be primitive we must squash. *)
        let map (a, b, univs, im) =
          let univs = compute_elim_squash env_ar_par Sorts.prop univs in
          (a, b, univs, im)
        in
        let data = List.map map data in
        data, Some None, Some reason (* back to FakeRecord with a reason why *)
  in

  let variance = match mie.mind_entry_variance with
    | None -> None
    | Some variances ->
      match mie.mind_entry_universes with
      | Monomorphic_ind_entry | Template_ind_entry _ ->
        CErrors.user_err Pp.(str "Inductive cannot be both monomorphic and universe cumulative.")
      | Polymorphic_ind_entry uctx ->
        (* no variance for qualities *)
        let _qualities, univs = Instance.to_array @@ subst_sort_level_instance usubst @@ UContext.instance uctx in
        let univs = Array.map2 (fun a b -> a,b) univs variances in
        let univs = match sec_univs with
          | None -> univs
          | Some sec_univs ->
            (* no variance for qualities *)
            let _, sec_univs = UVars.Instance.to_array sec_univs in
            let sec_univs = Array.map (fun u -> u, None) sec_univs in
            Array.append sec_univs univs
        in
        let arities, ctors = List.split @@ List.map (fun (_, arity, lc) -> (arity, lc)) blocks in
        let variances = InferCumulativity.infer_inductive ~env_params ~env_ar_par ~arities ~ctors univs in
        Some variances
  in

  let check_packet env (_, _, univ_info, _) =
    if not (List.is_empty univ_info.missing)
    then raise (InductiveError (env, MissingUnivConstraints (univ_info.missing,univ_info.ind_univ)));
  in
  let () = List.iter (fun pkt -> check_packet env pkt) data in
  let map ((arity, lc), b, univs, relies_on_indices_not_mattering) =
    let arity = { user_arity = arity; sort = univs.ind_univ } in
    ((arity, lc), b, univs.ind_squashed, relies_on_indices_not_mattering, univs.uses_impredicative_set)
  in
  let data = List.map map data in

  env_ar_par, univs, template, variance, record, not_prim_reason_or_has_eta, params, Array.of_list data
