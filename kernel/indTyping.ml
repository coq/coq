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
  | HasRelevantArg
  (** HasRelevantArg means when the record is relevant at least one arg is relevant.
      When the record is in a polymorphic sort this can mean one arg is in the same sort. *)

type univ_info =
  { ind_squashed : squash_info option
  ; record_arg_info : record_arg_info
  ; ind_template : bool
  ; ind_univ : Sorts.t
  ; missing : Sorts.t list (* missing u <= ind_univ constraints *)
  }

let add_squash q info =
  match info.ind_squashed with
  | None -> { info with ind_squashed = Some (SometimesSquashed (Sorts.Quality.Set.singleton q)) }
  | Some AlwaysSquashed -> info
  | Some (SometimesSquashed qs) ->
    (* XXX dedup insertion *)
    { info with ind_squashed = Some (SometimesSquashed (Sorts.Quality.Set.add q qs)) }

(* This code can probably be simplified but I can't quite see how right now. *)
let check_univ_leq ?(is_real_arg=false) env u info =
  let open Sorts.Quality in
  let info = if not is_real_arg then info
    else match info.record_arg_info with
      | HasRelevantArg -> info
      | NoRelevantArg -> match u with
        | Sorts.SProp -> info
        | QSort (q,_) ->
          if Environ.Internal.is_above_prop env q
          || Sorts.Quality.equal (QVar q) (Sorts.quality info.ind_univ)
          then { info with record_arg_info = HasRelevantArg }
          else info
        | Prop | Set | Type _ -> { info with record_arg_info = HasRelevantArg }
  in
  if (Environ.type_in_type env) then info
  else match u, info.ind_univ with
  | SProp, (SProp | Prop | Set | Type _) ->
    (* Inductive types provide explicit lifting from SProp to other universes,
       so allow SProp <= any. *)
    info

  | Prop, SProp -> { info with ind_squashed = Some AlwaysSquashed }
  | (SProp|Prop), QSort (q,_) ->
    if Environ.Internal.is_above_prop env q then info
    else add_squash (Sorts.quality u) info
  | Prop, (Prop | Set | Type _) -> info

  | Set, (SProp | Prop) -> { info with ind_squashed = Some AlwaysSquashed }
  | Set, QSort (q, indu) ->
    if Environ.Internal.is_above_prop env q then info
    else if UGraph.check_leq (universes env) Universe.type0 indu (* XXX always true *)
    then add_squash qtype info
    else { info with missing = u :: info.missing }
  | Set, Set -> info
  | Set, Type indu ->
    if UGraph.check_leq (universes env) Universe.type0 indu
    then info
    else { info with missing = u :: info.missing }

  | QSort (q,_), (SProp | Prop) -> add_squash (QVar q) info
  | QSort (cq, uu), QSort (indq, indu) ->
    if UGraph.check_leq (universes env) uu indu
    then begin if Sorts.QVar.equal cq indq then info
      else add_squash (QVar cq) info
    end
    else { info with missing = u :: info.missing }
  | QSort (_, uu), Set ->
    if UGraph.check_leq (universes env) uu Universe.type0
    then info
    else if is_impredicative_set env
    then (* imprecise but we don't handle complex impredicative set squashings  *)
      { info with ind_squashed = Some AlwaysSquashed }
    else { info with missing = u :: info.missing }
  | QSort (_,uu), Type indu ->
    if UGraph.check_leq (universes env) uu indu
    then info
    else { info with missing = u :: info.missing }

  | Type _, (SProp | Prop) -> { info with ind_squashed = Some AlwaysSquashed }
  | Type uu, Set ->
    if UGraph.check_leq (universes env) uu Universe.type0
    then info
    else if is_impredicative_set env
    then { info with ind_squashed = Some AlwaysSquashed }
    else { info with missing = u :: info.missing }
  | Type uu, QSort (_, indu) ->
    if UGraph.check_leq (universes env) uu indu
    then add_squash qtype info
    else { info with missing = u :: info.missing }
  | Type uu, Type indu ->
    if UGraph.check_leq (universes env) uu indu
    then info
    else { info with missing = u :: info.missing }

let check_context_univs ~ctor env info ctx =
  let check_one d (info,env) =
    let info = match d with
      | LocalAssum (_,t) ->
        (* could be retyping if it becomes available in the kernel *)
        let tj = Typeops.infer_type env t in
        check_univ_leq ~is_real_arg:ctor env tj.utj_type info
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
  let univ_info = {
    ind_squashed=None;
    record_arg_info=NoRelevantArg;
    ind_template = template;
    ind_univ=ind_sort;
    missing=[];
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
  let splayed_lc = Array.map (Reduction.whd_decompose_prod_decls env_ar_par) lc in
  let univ_info = match Array.length lc with
    (* Empty type: sort poly must squash *)
    | 0 -> check_univ_leq env_ar_par Sorts.sprop univ_info

    | 1 ->
      (* SProp and sort poly primitive records are OK, if we squash and become fakerecord also OK *)
      if isrecord then univ_info
      (* 1 constructor with no arguments also OK in SProp (to make
         things easier on ourselves when reducing we forbid letins)
         unless ind_univ is sort polymorphic (for ease of implementation) *)
      else if (Environ.typing_flags env_ar_par).allow_uip
           && fst (splayed_lc.(0)) = []
           && List.for_all Context.Rel.Declaration.is_local_assum params
           && Sorts.is_sprop univ_info.ind_univ
      then univ_info
      (* 1 constructor with arguments must squash if SProp / sort poly
         (we could allow arguments in SProp but the reduction rule is a pain) *)
      else check_univ_leq env_ar_par Sorts.prop univ_info

    (* More than 1 constructor: must squash if Prop/SProp *)
    | _ -> check_univ_leq env_ar_par Sorts.set univ_info
  in
  let univ_info = Array.fold_left (check_constructor_univs env_ar_par) univ_info splayed_lc in
  let () = if univ_info.ind_template then match univ_info.ind_squashed with
      | None | Some AlwaysSquashed -> ()
      | Some (SometimesSquashed _) ->
      CErrors.user_err Pp.(str "Cannot handle sometimes squashed template polymorphic type.")
  in
  (* generalize the constructors over the parameters *)
  let lc = Array.map (fun c -> Term.it_mkProd_or_LetIn c params) lc in
  (arity, lc), (indices, splayed_lc), univ_info

module NotPrimRecordReason = struct

  type t =
    | MustNotBeSquashed
    | MustHaveRelevantProj
    | MustHaveProj
    | MustNotHaveAnonProj

end

let check_record data =
  let open NotPrimRecordReason in
  List.find_map (fun (_,(_,splayed_lc),info) ->
      if Option.has_some info.ind_squashed
      (* records must have all projections definable -> equivalent to not being squashed *)
      then Some MustNotBeSquashed
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
        if Option.has_some res then res
        else (* relevant records must have at least 1 relevant argument *)
        if (match info.record_arg_info with
            | HasRelevantArg -> false
            | NoRelevantArg -> not @@ Sorts.is_sprop info.ind_univ)
        then Some MustHaveRelevantProj
        else None)
    data

(* Template univs must be unbounded from below for subject reduction
   (with partially applied template poly, cf RFC 90).

   We also forbid strict bounds from above because they lead
   to problems when instantiated with algebraic universes
   (template_u < v can become w+1 < v which we cannot yet handle). *)
let check_unbounded_from_below (univs,csts) =
  Univ.Constraints.iter (fun (l,d,r) ->
      let bad = match d with
        | Eq | Lt ->
          if Level.Set.mem l univs then Some l
          else if Level.Set.mem r univs then Some r
          else None
        | Le -> if Level.Set.mem r univs then Some r else None
      in
      bad |> Option.iter (fun bad ->
          CErrors.user_err Pp.(str "Universe level " ++ Level.raw_pr bad ++
                               str " cannot be template because it appears in constraint " ++
                               Level.raw_pr l ++ pr_constraint_type d ++ Level.raw_pr r)))
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
  | Sort (QSort (q, u) as s) ->
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

let make_template_univ_names (u:UVars.Instance.t) : UVars.bound_names =
  let qlen, ulen = UVars.Instance.length u in
  Array.make qlen Anonymous, Array.make ulen Anonymous

let get_template (mie:mutual_inductive_entry) = match mie.mind_entry_universes with
| Monomorphic_ind_entry | Polymorphic_ind_entry _ -> mie, None, None
| Template_ind_entry {uctx; default_univs} ->
  let template_qvars, (template_univs, _ as template_context) =
    UVars.UContext.to_context_set uctx
  in
  let params = mie.mind_entry_params in
  let ind =
    match mie.mind_entry_inds with
    | [ind] -> ind
    | _ -> CErrors.user_err Pp.(str "Template-polymorphism not allowed with mutual inductives.")
  in
  let () = check_unbounded_from_below template_context in

  let template_context =
    UVars.UContext.of_context_set make_template_univ_names
      template_qvars
      template_context
  in
  let template_abstract, template_context =
    let inst, ctx = UVars.abstract_universes template_context in
    UVars.make_instance_subst inst, ctx
  in

  (* Template univs must only appear in the conclusion of the
     inductive and linearly in the conclusion of parameters.
     This makes them Irrelevant for conversion and also makes them easy to substitute.
     The inductive and binding parameter types must be syntactically arities. *)
  let check_not_appearing c =
    let qs, us = Vars.sort_and_universes_of_constr c in
    let qappearing = Sorts.QVar.Set.inter qs template_qvars in
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
    let (decls, s) = Term.decompose_prod_decls ind.mind_entry_arity in
    let () = if not (isSort s) then
        CErrors.user_err Pp.(str "Template polymorphic inductive's type must be a syntactic arity.")
    in
    check_not_appearing_rel_ctx decls;
    let s = destSort s in
    let () = match s with
    | SProp | Prop | Set -> ()
    | QSort (_, u) ->
      (* typechecking will fail with "unbound qvar" if the quality isn't in template_qvars *)
      check_no_increment ~template_univs u;
      ()
    | Type u ->
      check_no_increment ~template_univs u;
      ()
    in
    UVars.subst_sort_level_sort template_abstract s
  in

  (** ctors *)
  let () = List.iter check_not_appearing ind.mind_entry_lc in

  let template_param_arguments =
    let assums = CList.filter_map (fun x -> x) template_params in
    List.rev_map
      (Option.map (fun (_, _, s) ->
           UVars.subst_sort_level_sort template_abstract s))
      assums
  in

  (* Substitution from the template binders to the default univs (and qtype for the qvars)
     XXX can this be simplified by composing template_abstract and default_univs?
     don't forget to check the default_univs qualities are all QType if so *)
  let template_usubst : UVars.sort_level_subst =
    let bind_instance = UVars.UContext.instance uctx in
    let () = if not UVars.(eq_sizes (Instance.length bind_instance) (Instance.length default_univs))
      then CErrors.anomaly Pp.(str "Inorrect default template universes declaration.")
    in
    let bind_qs, bind_us = UVars.Instance.to_array bind_instance in
    let default_qs, default_us = UVars.Instance.to_array default_univs in
    let qsubst = Array.fold_left2 (fun qsubst bind_q default_q ->
        let open Sorts.Quality in
        match bind_q, default_q with
        | QConstant _, _ -> assert false
        | QVar bind_q, QConstant QType ->
          Sorts.QVar.Map.add bind_q default_q qsubst
        | QVar _, _ -> CErrors.anomaly Pp.(str "Default template quality must be QType."))
        Sorts.QVar.Map.empty
        bind_qs default_qs
    in
    let usubst = Array.fold_left2 (fun usubst bind_u default_u ->
        assert (not @@ Level.is_set bind_u);
        Level.Map.add bind_u default_u usubst)
        Level.Map.empty
        bind_us default_us
    in
    qsubst, usubst
  in

  mie, Some template_usubst, Some {
    template_param_arguments;
    template_context;
    template_concl;
    template_defaults = default_univs;
  }

let abstract_packets env usubst ((arity,lc),(indices,splayed_lc),univ_info) =
  if not (List.is_empty univ_info.missing)
  then raise (InductiveError (env, MissingConstraints (univ_info.missing,univ_info.ind_univ)));
  let arity = Vars.subst_univs_level_constr usubst arity in
  let lc = Array.map (Vars.subst_univs_level_constr usubst) lc in
  let indices = Vars.subst_univs_level_context usubst indices in
  let splayed_lc = Array.map (fun (args,out) ->
      let args = Vars.subst_univs_level_context usubst args in
      let out = Vars.subst_univs_level_constr usubst out in
      args,out)
      splayed_lc
  in
  let ind_univ = UVars.subst_sort_level_sort usubst univ_info.ind_univ in

  let arity = {user_arity = arity; sort = ind_univ} in

  let squashed = Option.map (function
      | AlwaysSquashed -> AlwaysSquashed
      | SometimesSquashed qs ->
        let qs = Sorts.Quality.Set.fold (fun q qs ->
            Sorts.Quality.Set.add (UVars.subst_sort_level_quality usubst q) qs)
            qs
            Sorts.Quality.Set.empty
        in
        SometimesSquashed qs)
      univ_info.ind_squashed
  in

  (arity,lc), (indices,splayed_lc), squashed

let typecheck_inductive env ~sec_univs (mie:mutual_inductive_entry) =
  let () = match mie.mind_entry_inds with
  | [] -> CErrors.anomaly Pp.(str "empty inductive types declaration.")
  | _ -> ()
  in
  (* Check unicity of names (redundant with safe_typing's add_field checks) *)
  mind_check_names env mie;
  assert (List.is_empty (Environ.rel_context env));

  (* universes *)
  let mie, template_usubst, template = get_template mie in

  let env_univs =
    match mie.mind_entry_universes with
    | Template_ind_entry {uctx; default_univs=_} ->
      Environ.Internal.push_template_context uctx env
    | Monomorphic_ind_entry -> env
    | Polymorphic_ind_entry ctx -> push_context ctx env
  in

  let has_template_poly = match mie.mind_entry_universes with
  | Template_ind_entry _ -> true
  | Monomorphic_ind_entry | Polymorphic_ind_entry _ -> false
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
  let data, record, why_not_prim_record = match record with
    | None | Some None -> data, record, None
    | Some (Some _) ->
      match check_record data with
      | None -> data, record, None
      | Some _ as reason ->
        (* if someone tried to declare a record as SProp but it can't
           be primitive we must squash. *)
        let data = List.map (fun (a,b,univs) ->
            a,b,check_univ_leq env_ar_par Sorts.prop univs)
            data
        in
        data, Some None, reason
  in

  let variance = match mie.mind_entry_variance with
    | None -> None
    | Some variances ->
      match mie.mind_entry_universes with
      | Monomorphic_ind_entry | Template_ind_entry _ ->
        CErrors.user_err Pp.(str "Inductive cannot be both monomorphic and universe cumulative.")
      | Polymorphic_ind_entry uctx ->
        (* no variance for qualities *)
        let _qualities, univs = Instance.to_array @@ UContext.instance uctx in
        let univs = Array.map2 (fun a b -> a,b) univs variances in
        let univs = match sec_univs with
          | None -> univs
          | Some sec_univs ->
            (* no variance for qualities *)
            let _, sec_univs = UVars.Instance.to_array sec_univs in
            let sec_univs = Array.map (fun u -> u, None) sec_univs in
            Array.append sec_univs univs
        in
        let variances = InferCumulativity.infer_inductive ~env_params ~env_ar_par
            ~arities:(List.map (fun e -> e.mind_entry_arity) mie.mind_entry_inds)
            ~ctors:(List.map (fun e -> e.mind_entry_lc) mie.mind_entry_inds)
            univs
        in
        Some variances
  in

  (* Abstract universes *)
  let usubst, univs = match mie.mind_entry_universes with
  | Monomorphic_ind_entry ->
    UVars.empty_sort_subst, Monomorphic
  | Template_ind_entry _ ->
    let usubst = Option.get template_usubst in
    usubst, Monomorphic
  | Polymorphic_ind_entry uctx ->
    let (inst, auctx) = UVars.abstract_universes uctx in
    let inst = UVars.make_instance_subst inst in
    (inst, Polymorphic auctx)
  in
  let params = Vars.subst_univs_level_context usubst params in
  let data = List.map (abstract_packets env usubst) data in

  let env_ar_par =
    let ctx = Environ.rel_context env_ar_par in
    let ctx = Vars.subst_univs_level_context usubst ctx in
    let env = Environ.pop_rel_context (Environ.nb_rel env_ar_par) env_ar_par in
    Environ.push_rel_context ctx env
  in

  env_ar_par, univs, template, variance, record, why_not_prim_record, params, Array.of_list data
