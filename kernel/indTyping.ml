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
open UVars
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


let no_sort_variable () =
  CErrors.user_err (Pp.str "Sort variables not yet supported for the inductive's sort.")

type record_arg_info =
  | NoRelevantArg
  | HasRelevantArg
  | HasVariableRelevanceArg

type univ_info =
  { ind_squashed : bool
  ; record_arg_info : record_arg_info
  ; ind_template : bool
  ; ind_univ : Sorts.t
  ; missing : Sorts.t list (* missing u <= ind_univ constraints *)
  }

(* TODO squash depending on the instance
   (so eg in the "QSort(q, _), Prop" case, "@{q:=Prop|}" is not squashed
    but "@{q:=Type|}" does need squashing)
   Cases which will be modified are annotated with "imprecise".

   This code can probably be simplified but I can't quite see how right now. *)
let check_univ_leq ?(is_real_arg=false) env u info =
  let info = if not is_real_arg then info
    else match info.record_arg_info with
    | HasVariableRelevanceArg -> info
    | NoRelevantArg | HasRelevantArg -> match u with
      | Sorts.SProp -> info
      | Prop | Set | Type _ -> { info with record_arg_info = HasRelevantArg }
      | QSort _ ->
        { info with record_arg_info = HasVariableRelevanceArg }
  in
  (* If we would squash (eg Prop, SProp case) we still need to check the type in type flag. *)
  let ind_squashed = not (Environ.type_in_type env) in
  match u, info.ind_univ with
  | SProp, (SProp | Prop | Set | QSort _ | Type _) ->
    (* Inductive types provide explicit lifting from SProp to other universes,
       so allow SProp <= any. *)
    info

  | Prop, SProp -> { info with ind_squashed }
  | Prop, QSort _ -> { info with ind_squashed } (* imprecise *)
  | Prop, (Prop | Set | Type _) -> info

  | Set, (SProp | Prop) -> { info with ind_squashed }
  | Set, QSort (_, indu) ->
    if UGraph.check_leq (universes env) Universe.type0 indu
    then { info with ind_squashed } (* imprecise *)
    else { info with missing = u :: info.missing }
  | Set, Set -> info
  | Set, Type indu ->
    if UGraph.check_leq (universes env) Universe.type0 indu
    then info
    else { info with missing = u :: info.missing }

  | QSort _, (SProp | Prop) -> { info with ind_squashed } (* imprecise *)
  | QSort (cq, uu), QSort (indq, indu) ->
    if UGraph.check_leq (universes env) uu indu
    then begin if Sorts.QVar.equal cq indq then info
      else { info with ind_squashed } (* imprecise *)
    end
    else { info with missing = u :: info.missing }
  | QSort (_, uu), Set ->
    if UGraph.check_leq (universes env) uu Universe.type0
    then info
    else if is_impredicative_set env
    then { info with ind_squashed } (* imprecise *)
    else { info with missing = u :: info.missing }
  | QSort (_,uu), Type indu ->
    if UGraph.check_leq (universes env) uu indu
    then info
    else { info with missing = u :: info.missing }

  | Type _, (SProp | Prop) -> { info with ind_squashed }
  | Type uu, Set ->
    if UGraph.check_leq (universes env) uu Universe.type0
    then info
    else if is_impredicative_set env
    then { info with ind_squashed }
    else { info with missing = u :: info.missing }
  | Type uu, QSort (_, indu) ->
    if UGraph.check_leq (universes env) uu indu
    then { info with ind_squashed } (* imprecise *)
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
    ind_squashed=false;
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
    (* Empty type: all OK *)
    | 0 -> univ_info

    | 1 ->
      (* SProp primitive records are OK, if we squash and become fakerecord also OK *)
      if isrecord then univ_info
      (* 1 constructor with no arguments also OK in SProp (to make
         things easier on ourselves when reducing we forbid letins) *)
      else if (Environ.typing_flags env_ar_par).allow_uip
           && fst (splayed_lc.(0)) = []
           && List.for_all Context.Rel.Declaration.is_local_assum params
      then univ_info
      (* 1 constructor with arguments must squash if SProp
         (we could allow arguments in SProp but the reduction rule is a pain) *)
      else check_univ_leq env_ar_par Sorts.prop univ_info

    (* More than 1 constructor: must squash if Prop/SProp *)
    | _ -> check_univ_leq env_ar_par Sorts.set univ_info
  in
  let univ_info = Array.fold_left (check_constructor_univs env_ar_par) univ_info splayed_lc in
  (* generalize the constructors over the parameters *)
  let lc = Array.map (fun c -> Term.it_mkProd_or_LetIn c params) lc in
  (arity, lc), (indices, splayed_lc), univ_info

let check_record data =
  List.for_all (fun (_,(_,splayed_lc),info) ->
      (* records must have all projections definable -> equivalent to not being squashed *)
      not info.ind_squashed
      (* relevant records must have at least 1 relevant argument,
         and we don't yet support variable relevance projections *)
      && (match info.record_arg_info with
          | HasVariableRelevanceArg -> false
          | HasRelevantArg -> true
          | NoRelevantArg -> Sorts.is_sprop info.ind_univ)
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

let allowed_sorts {ind_squashed;ind_univ;ind_template=_;record_arg_info=_;missing=_} =
  if not ind_squashed then InType
  else Sorts.family ind_univ

(* For a level to be template polymorphic, it must be introduced
   by the definition (so have no constraint except lbound <= l)
   and not to be constrained from below, so any universe l' <= l
   can be used as an instance of l. All bounds from above, i.e.
   l <=/< r will be valid for any l' <= l. *)
let unbounded_from_below u cstrs =
  Univ.Constraints.for_all (fun (l, d, r) ->
      match d with
      | Eq -> not (Univ.Level.equal l u) && not (Univ.Level.equal r u)
      | Lt | Le -> not (Univ.Level.equal r u))
    cstrs

let get_template univs ~env_params ~env_ar_par ~params entries =
  match univs with
  | Polymorphic_ind_entry _ | Monomorphic_ind_entry -> None
  | Template_ind_entry ctx ->
    let entry = match entries with
      | [entry] -> entry
      | _ -> CErrors.user_err Pp.(str "Template-polymorphism not allowed with mutual inductives.")
    in
    (* Compute potential template parameters *)
    let map decl = match decl with
    | LocalAssum (_, p) ->
      let c = Term.strip_prod_decls p in
      let s = match kind c with
      | Sort (Type u) ->
        begin match Universe.level u with
        | Some l -> if Level.Set.mem l (fst ctx) then Some l else None
        | None -> None
        end
      | _ -> None
      in
      Some s
    | LocalDef _ -> None
    in
    let params = List.map_filter map params in
    let fold accu u = match u with None -> accu | Some u -> Level.Set.add u accu in
    let plevels = List.fold_left fold Level.Set.empty params in
    let unbound = Level.Set.diff (fst ctx) plevels in
    let plevels =
      if not (Level.Set.is_empty unbound) then
        CErrors.user_err Pp.(strbrk "The following template universes are not \
          bound by parameters: " ++ pr_sequence Level.raw_pr (Level.Set.elements unbound))
      else Level.Set.elements plevels
    in
    let check_bound l =
      if not (unbounded_from_below l (snd ctx)) then
        CErrors.user_err Pp.(strbrk "Universe level " ++ Level.raw_pr l ++ strbrk " has a lower bound")
    in
    let () = List.iter check_bound plevels in
    (* We reuse the same code as the one for variance inference. *)
    let init_variance = Array.map_of_list (fun l -> l, Some Variance.Irrelevant) plevels in
    let _variance = InferCumulativity.infer_inductive ~env_params ~env_ar_par init_variance
        ~arities:[entry.mind_entry_arity]
        ~ctors:[entry.mind_entry_lc]
    in
    let params = List.rev params in
    Some { template_param_levels = params; template_context = ctx }

let abstract_packets usubst ((arity,lc),(indices,splayed_lc),univ_info) =
  if not (List.is_empty univ_info.missing)
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
  let ind_univ = match univ_info.ind_univ with
    | QSort _ -> no_sort_variable ()
    | _ ->
      UVars.subst_sort_level_sort usubst univ_info.ind_univ
  in

  let arity =
    if univ_info.ind_template then
      TemplateArity { template_level = univ_info.ind_univ; }
    else
      RegularArity {mind_user_arity = arity; mind_sort = ind_univ}
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

  (* universes *)
  let env_univs =
    match mie.mind_entry_universes with
    | Template_ind_entry ctx ->
        (* For that particular case, we typecheck the inductive in an environment
           where the universes introduced by the definition are only [>= Prop] *)
        let env = set_universes_lbound env UGraph.Bound.Prop in
        push_context_set ~strict:false ctx env
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
  let data, record = match record with
    | None | Some None -> data, record
    | Some (Some _) ->
      if check_record data then
        data, record
      else
        (* if someone tried to declare a record as SProp but it can't
           be primitive we must squash. *)
        let data = List.map (fun (a,b,univs) ->
            a,b,check_univ_leq env_ar_par Sorts.prop univs)
            data
        in
        data, Some None
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

  let template = get_template mie.mind_entry_universes ~env_params ~env_ar_par ~params mie.mind_entry_inds in

  (* Abstract universes *)
  let usubst, univs = match mie.mind_entry_universes with
  | Monomorphic_ind_entry | Template_ind_entry _ ->
    UVars.empty_sort_subst, Monomorphic
  | Polymorphic_ind_entry uctx ->
    let (inst, auctx) = UVars.abstract_universes uctx in
    let inst = UVars.make_instance_subst inst in
    (inst, Polymorphic auctx)
  in
  let params = Vars.subst_univs_level_context usubst params in
  let data = List.map (abstract_packets usubst) data in

  let env_ar_par =
    let ctx = Environ.rel_context env_ar_par in
    let ctx = Vars.subst_univs_level_context usubst ctx in
    let env = Environ.pop_rel_context (Environ.nb_rel env_ar_par) env_ar_par in
    Environ.push_rel_context ctx env
  in

  env_ar_par, univs, template, variance, record, params, Array.of_list data
