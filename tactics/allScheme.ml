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

open Declarations
open Util
open Names
open Nameops
open Constr
open Vars
open Environ
open Reduction
open Context.Rel.Declaration

(** Generalize parameters for template and univ poly, and split uniform and non-uniform parameters *)
let split_uparams_nuparams mib params =
  let (uparams, nuparams) = Context.Rel.chop_nhyps mib.mind_nparams_rec (List.rev params) in
  (List.rev uparams, List.rev nuparams)

(** {6 Strictly Positive Uniform Parameters } *)

let dbg_strpos = CDebug.create ~name:"strpos" ()

let pp_strpos l = Pp.(str "[" ++ prlist_with_sep (fun () -> str ";" ++ spc()) bool l ++ str "]")

(** Iterate [&&] on [f x] for an array [ar] *)
let andl_array f default ar =
  Array.fold_right (fun x acc -> (List.map2 (&&)) acc (f x)) ar default

(** Check which uniform parameters are arity, unfolding Let-ins, and returns
    the updated environment and the initial value of strictly positivity     *)
let init_value env uparams =
  let rec aux env (tel : Constr.rel_context) =
    match tel with
    | [] -> (env, [])
    | decl::tel ->
      match get_value decl with
      | Some _ ->
          aux (push_rel decl env) tel
      | None   ->
          let (env, init_value) = aux (push_rel decl env) tel in
          (env, Reduction.is_arity env (get_type decl) :: init_value)
    in
    aux env (List.rev uparams)

(** Check if the uniform parameters appear in a term *)
let check_strpos env uparams t =
  let nenv = List.length @@ Environ.rel_context env in
  let rec aux i tel =
    match tel with
    | [] -> []
    | decl::tel ->
      match get_value decl with
      | Some _ -> aux (i+1) tel
      | None   -> noccur_between (nenv - i) 1 t :: aux (i+1) tel
  in
  aux 0 (List.rev uparams)

(** Check if the uniform parameters appear in a context  *)
let check_strpos_context env uparams default cxt =
  let rec aux env strpos tel =
    match tel with
    | [] -> (env, strpos)
    | decl::tel ->
      if Option.has_some @@ get_value decl then
        aux (push_rel decl env) strpos tel
      else
        let ty = whd_all env @@ get_type decl in
        let strpos_decl = check_strpos env uparams ty in
        aux (push_rel decl env) (List.map2 (&&) strpos_decl strpos) tel
  in aux env default (List.rev cxt)

let get_inductive_sort (mib, mip) u = match mib.mind_template with
| None -> UVars.subst_instance_sort u mip.mind_sort
| Some templ ->
  let () = assert (UVars.Instance.is_empty u) in
  UVars.subst_instance_sort templ.template_defaults mip.mind_sort

module Cache =
struct

type t = { mutable uniform : bool list Mindmap.t }

let empty () = { uniform = Mindmap.empty }

end

(** Computes which uniform parameters are strictly positive in an argument *)
let rec compute_params_rec_strpos_arg cache env kn uparams nparams_rec nparams init_value arg =
  (* strictly positive uniform parameters do not appear on the left of an arrow *)
  let (local_vars, hd) = Reduction.whd_decompose_prod_decls env arg in
  let (env, strpos_local) = check_strpos_context env uparams init_value local_vars in
  (* check the head *)
  let (hd, inst_args) = decompose_app hd in
  let strpos_hd =
    match kind hd with
    | Rel k ->
        (* Check if it is the inductive *)
        if List.length (Environ.rel_context env) < k then
        (* If it is the inductive, then they should not appear in the instantiation
        of the non-uniform parameters and indices of the inductive type being defined *)
          let (_, iargs) = Array.chop nparams_rec inst_args in
          andl_array (check_strpos env uparams) init_value iargs
        (* Otherwise, they should not appear in the arguments *)
        else
          andl_array (check_strpos env uparams) init_value inst_args
    | Ind ((kn_nested, _), _) ->
        (* Check if it is the inductive or nested *)
        if QMutInd.equal env kn kn_nested then
        (* If it is the inductive, then they should not appear in the instantiation
          of the non-uniform parameters and indices of the inductive type being defined *)
          let (_, iargs) = Array.chop nparams_rec inst_args in
          andl_array (check_strpos env uparams) init_value iargs
        (* For nested arguments, they should: *)
        else begin
          let mib_nested = lookup_mind kn_nested env in
          let mib_nested_strpos = compute_params_rec_strpos cache env kn_nested mib_nested in
          let (inst_uparams, inst_nuparams_indices) =
            Array.chop mib_nested.mind_nparams_rec inst_args in
          let uparams_nested = List.rev @@ fst @@
                Context.Rel.chop_nhyps mib_nested.mind_nparams_rec @@
                List.rev mib_nested.mind_params_ctxt in
          let inst_uparams = Termops.eta_expand_instantiation env inst_uparams uparams_nested in
          (* - appear strictly positively in the instantiation of the uniform parameters
               that are strictly postive themselves
             - not appear in uniform parameters that are not strictly postive *)
          let strpos_inst_uparams = Array.fold_right_i (fun i x acc ->
            if List.nth mib_nested_strpos i
            then List.map2 (&&) acc @@ compute_params_rec_strpos_arg cache env kn uparams nparams_rec nparams init_value x
            else List.map2 (&&) acc @@ check_strpos env uparams x
            ) inst_uparams init_value  in
          (* - not appear in the instantiation of the non-uniform parameters and indices *)
          let strpos_inst_nuparams_indices = andl_array (check_strpos env uparams) init_value inst_nuparams_indices in
          List.map2 (&&) strpos_inst_uparams strpos_inst_nuparams_indices
        end
    | Const (c, _) ->
      if is_array_type env c then
        andl_array (compute_params_rec_strpos_arg cache env kn uparams nparams_rec nparams init_value) init_value inst_args
      else
        check_strpos env uparams hd
    | _ -> check_strpos env uparams hd
  in
  List.map2 (&&) strpos_local strpos_hd

(** Computes which uniform parameters are strictly positive in a constructor *)
and compute_params_rec_strpos_ctor cache env kn uparams nparams_rec nparams init_value (args, hd) =
  (* They must not appear on the left of an arrow in each argument *)
  let (env, strpos_args) =
    List.fold_right (
        fun arg (env, acc) ->
        if Option.has_some @@ get_value arg then
          push_rel arg env, acc
        else
          let strpos_arg = compute_params_rec_strpos_arg cache env kn uparams nparams_rec nparams init_value (get_type arg) in
          (push_rel arg env, List.map2 (&&) acc strpos_arg)
      ) args (env, init_value)
  in
  (* They must not appear in the instantiation of the indices *)
  let (_, xs) = decompose_app hd in
  let inst_indices = Array.sub xs nparams (Array.length xs - nparams) in
  let str_inst_indices = andl_array (check_strpos env uparams) strpos_args inst_indices in
  let res_ctor = List.map2 (&&) strpos_args str_inst_indices in
  res_ctor

(** Computes which uniform parameters are strictly positive in an inductive block *)
and compute_params_rec_strpos_ind cache env kn uparams nparams_rec nparams init_value (indices, ctors) =
  (* They must not appear in indices *)
  let (_, strpos_indices) = check_strpos_context env uparams init_value indices in
  (* They must be strictly positive in each constructor *)
  let strpos_ctors = andl_array (compute_params_rec_strpos_ctor cache env kn uparams nparams_rec nparams init_value) init_value ctors in
  let res_ind = List.map2 (&&) strpos_indices strpos_ctors in
  res_ind

(** Computes which uniform parameters are strictly positive in a mutual inductive block.
    [inds : (rel_context * (rel_declaration list * types) array) array] contains
    the context of indices, then for each constructor the telescope of arguments, and the hd.
    This function can be used whether the inductive is refered using [Rel] or [Ind].
    This particular data representation is the one of indtypes.
    *)
and compute_params_rec_strpos_aux cache env kn uparams nuparams nparams_rec nparams inds =
  if nparams_rec = 0 then [] else
  (* They must be arities [forall ..., sort X] *)
  let (env, init_value) = init_value env uparams in
  (* They must not appear in non-uniform parameters *)
  let (env, strpos_nuparams) = check_strpos_context env uparams init_value nuparams in
  (* They must be strictly positive in each inductive block *)
  let strpos_inds = andl_array (compute_params_rec_strpos_ind cache env kn uparams nparams_rec nparams init_value) init_value inds in
  let res = List.map2 (&&) strpos_nuparams strpos_inds in
  dbg_strpos Pp.(fun () -> MutInd.print kn ++ str ": Final Result = " ++ pp_strpos res);
  res

and compute_params_rec_strpos cache env kn mib =
  match Mindmap.find_opt kn cache.Cache.uniform with
| None ->
  (* reset the context *)
  let env = set_rel_context_val empty_rel_context_val env in
  (* compute the data expected *)
  let inds = Array.map (fun ind ->
      let (indices, _) = List.chop (List.length ind.mind_arity_ctxt - mib.mind_nparams) ind.mind_arity_ctxt in
      let ctors = Array.map (fun (args, hd) ->
                      let (args,_) = List.chop (List.length args - mib.mind_nparams) args in
                      (args, hd)
                    ) ind.mind_nf_lc
                  in
      (indices, ctors)
    ) mib.mind_packets
  in
  let (uparams, nuparams) = map_pair List.rev @@ Context.Rel.chop_nhyps mib.mind_nparams_rec @@
                            List.rev mib.mind_params_ctxt in
  let ans = compute_params_rec_strpos_aux cache env kn uparams nuparams mib.mind_nparams_rec mib.mind_nparams inds in
  let () = cache.Cache.uniform <- Mindmap.add kn ans cache.Cache.uniform in
  ans
| Some unf -> unf

(** {6 Lookup All Predicate and its Theorem } *)

(** Suffix and register key for the [all] predicate and its theorem  *)
let default_suffix = (("_all", "_all_forall"), ("All", "AllForall"))

let rec bool_list_to_string lb =
  match lb with
  | [] -> ""
  | true::l  -> "1" ^ bool_list_to_string l
  | false::l -> "0" ^ bool_list_to_string l

(** Suffix and register key for partial version of the [all] predicate and its theorem  *)
let partial_suffix strpos =
  let ((a, b), (c, d)) = default_suffix in
  let s = "_" ^ bool_list_to_string strpos in
  ((a^s, b^s), (c^s, d^s))

let rec compute_user_strpos_aux user_names allowed_uparams strpos =
  match user_names with
  | [] -> strpos
  | name::user_names ->
      let i =
          try CList.index0 (fun i n -> Name.equal i n) name allowed_uparams with
          | Not_found ->
            let allowed_uparams = List.filter Name.is_name allowed_uparams in
            CErrors.user_err Pp.(
              fmt "The variable %t is not included in the uniform parameters that are strictly positive and can be nested on"
                (fun () -> Name.print name) ++
              if List.is_empty allowed_uparams then
                strbrk " because there are no such parameters."
            else
              fmt ".@ Allowed parameters are %t." (fun () -> pr_enum Name.print allowed_uparams)
            )
      in
      dbg_strpos Pp.(fun () -> str "POSITION IS =" ++ int i);
      compute_user_strpos_aux user_names allowed_uparams (List.assign strpos i true)

let compute_user_strpos mib user_id default_strpos =
  let user_names = List.map (fun i -> Name i) user_id in
  let uparams = fst @@ split_uparams_nuparams mib mib.mind_params_ctxt in
  let uparams_decl = List.filter is_local_assum uparams in
  let uparams_decl_name = List.map get_name uparams_decl in
  let allowed_uparams = List.map (fun (name, i) -> if i then name else Anonymous)
                          @@ List.combine (List.rev uparams_decl_name) default_strpos in
  let strpos = List.map (fun _ -> false) uparams_decl in
  compute_user_strpos_aux user_names allowed_uparams strpos

let compute_params_rec_strpos env kn mib =
  let cache = Cache.empty () in
  compute_params_rec_strpos cache env kn mib

(** Compute the default positivity of the uniform parameters, and generates the suffix
    for naming the [all] predicate, and its theorem, as well as the key for registering.
    If a positivity specification is given by users [bool list option], it is
    checked to be included in the default one, and the suffix are modified accordingly. *)
let compute_positive_uparams_and_suffix env kn mib user_id =
  let default_strpos = compute_params_rec_strpos env kn mib in
  match user_id with
  | None ->
      (default_strpos, fst default_suffix, snd default_suffix)
  | Some user_id ->
      let user_strpos = compute_user_strpos mib user_id default_strpos in
      let partial_suffix = partial_suffix user_strpos in
      (user_strpos, fst partial_suffix, snd partial_suffix)

module Warning_scheme_all = struct
  type cache = GlobRef.Set.t ref
  type t = string * inductive * GlobRef.t

  let empty_cache () = ref GlobRef.Set.empty

(** Warning for looking up the [all] predicate and its theorem  *)
  let warn_lookup_not_found =
    CWarnings.create ~name:"register-all" ~category:CWarnings.CoreCategories.automation
    Pp.(fun (key, ind, nested_container) ->
        let generic_message =
          Nametab.XRefs.pr (TrueGlobal (IndRef ind))
        ++ strbrk " is nested using "
        ++ Nametab.XRefs.pr (TrueGlobal nested_container)
        ++ strbrk ". "
        ++ strbrk "No scheme for "
        ++ Nametab.XRefs.pr (TrueGlobal nested_container)
        ++ strbrk " is registered as "
        ++ strbrk key ++  strbrk ". " in
        let inductive_message =
        strbrk "It can be generated using command \"Scheme All\" e.g. \"Scheme All for "
        ++ Nametab.XRefs.pr (TrueGlobal nested_container)
        ++ str ".\"." in
        match nested_container with
        | GlobRef.IndRef _ -> generic_message ++ inductive_message
        | _ -> generic_message
      )

  (** Warning for looking up the [all] predicate and its theorem
      If this warning is alredy in the cache do nothing, oterwise
      warn and add it to the cache *)
  let warn warn cache =
    let (_,_,container) = warn in
    let () = if not (GlobRef.Set.mem container !cache) then
      let () = warn_lookup_not_found warn in
      cache := GlobRef.Set.add container !cache
    in ()

end

(** Lookup the partial [all] predicate for [nested_container] for [args_are_nested].
    If they are not found, lookup the general [all] predicate.
    Returns if the partial [all] was found, and the global references.
    Return [Error] if none is found. *)
let lookup_all ind nested_container args_are_nested =
    let (_, (pred, _)) = partial_suffix args_are_nested in
    match DeclareScheme.lookup_scheme_opt pred nested_container with
    | Some ref_pred ->
        Ok (true, ref_pred)
    | None ->
        let (_, (pred, _)) = default_suffix in
        match DeclareScheme.lookup_scheme_opt pred nested_container with
        | Some ref_pred -> Ok (false, ref_pred)
        | None -> Error (pred, ind, nested_container)

(** Lookup the [all] predicate, and its theorem *)
let lookup_all_theorem_aux ind nested_container =
  let (_, (pred, thm)) = default_suffix in
  match DeclareScheme.lookup_scheme_opt pred nested_container with
  | None -> Error (pred, ind, nested_container)
  | Some ref_pred ->
      match DeclareScheme.lookup_scheme_opt thm nested_container with
      | None -> Error (thm, ind, nested_container)
      | Some ref_thm -> Ok (false, ref_pred, ref_thm)

(** Lookup the partial [all] predicate and its theorem for [nested_container] for [args_are_nested].
    If they are not found, lookup the general [all] predicate and its theorem.
    Returns if the partial [all] was found, and the global references.
    Return [nested_container] if none is found. *)
let lookup_all_theorem  ind nested_container args_are_nested =
  let (_, (pred, thm)) = partial_suffix args_are_nested in
  match DeclareScheme.lookup_scheme_opt pred nested_container with
  | None -> lookup_all_theorem_aux ind nested_container
  | Some ref_pred ->
      match DeclareScheme.lookup_scheme_opt thm nested_container with
      | Some ref_thm ->
          Ok (true, ref_pred, ref_thm)
      | None -> lookup_all_theorem_aux ind nested_container


  (** {6 Instantiate the All Predicate and its Theorem } *)

open EConstr
open Context
open Inductive
open LibBinding
open State
open Retyping
open Rel.Declaration

let (let@) x f = x f
let (let*) x f = State.bind x f
let dbg = CDebug.create ~name:"scheme-all" ()

let mkFunUnit x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.type"), EInstance.empty)

let instantiate_all_uparams ~partial_nesting strpos inst_uparams inst_preds =
  let inst_preds = Array.to_list inst_preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let* sigma = get_sigma in
  let inst_sparam =
    List.fold_right (fun (positive, inst_uparam, pred) acc ->
      if not positive then
        inst_uparam :: acc
      else
        match pred with
        | Some pred ->
            inst_uparam :: pred :: acc
        | None ->
            if partial_nesting
            then inst_uparam :: acc
            else inst_uparam :: (snd @@ run_state s sigma @@ mkFunUnit inst_uparam) :: acc
      )
    (List.combine3 strpos inst_uparams inst_preds) []
  in
  return @@ Array.of_list inst_sparam

(** Make the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate [constr option array], using [fun ... => True]
      if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
let make_all_predicate ~partial_nesting ref_all strpos inst_uparams inst_preds inst_nuparams_indices arg =
  let* ref_ind = fresh_global ref_all in
  let* inst_uparams = instantiate_all_uparams ~partial_nesting strpos inst_uparams inst_preds in
  typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]]

let mkFuntt x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.unit.tt"), EInstance.empty)

let instantiate_all_theorem_uparams ~partial_nesting strpos inst_uparams preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let* sigma = get_sigma in
  let inst_lfth =
    List.fold_right (fun (positive, inst_uparam, (pred, pred_hold)) acc ->
      if not positive then inst_uparam :: acc else
      match pred, pred_hold with
      | Some pred, Some pred_hold ->
          inst_uparam :: pred :: pred_hold :: acc
      | None, None ->
          if partial_nesting
          then inst_uparam :: acc
          else inst_uparam :: (snd @@ run_state s sigma @@ mkFunUnit inst_uparam) ::
                  (snd @@ run_state s sigma @@ mkFuntt inst_uparam) :: acc
      | _, _ -> assert false
    )
    (List.combine3 strpos inst_uparams @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth

(** Make the theorem for the [all] predicate for a fresh instance and using [Typing.checked_appvect], given:
    - whether the [all] predicate is the partial one, or the general one [partial_nesting:bool]
    - the positivity of each uniform parameter [bool list]
    - the instantiation of the uniform parameter of the inductive type [constr array]
    - the instation of the fresh predicate and the proofs they hold [constr option array],
      using [fun ... => True] and [fun _ => I] if the values are none, and [all] is the general predicate
    - the instantiation of the non-uniform parameters and indices
    - the argument to apply it to
*)
let make_all_theorem ~partial_nesting ref_all_thm strpos inst_uparams inst_preds inst_preds_hold inst_nuparams_indices arg =
  let* ref_ind = fresh_global ref_all_thm in
  let* inst_uparams = instantiate_all_theorem_uparams ~partial_nesting strpos inst_uparams inst_preds inst_preds_hold in
  typing_checked_appvect ref_ind @@ Array.concat [inst_uparams; inst_nuparams_indices; [|arg|]]


  (** {6 View for Arguments } *)

type head_argument =
  | ArgIsSPUparam of int * constr array
  (** position of the uniform parameter, args *)
  | ArgIsInd of int * constr array * constr array
  (** position of the one_inductive body, inst_nuparams, inst_indices *)
  | ArgIsNested of GlobRef.t * bool list
                    * rel_context * constr array * constr array
  (** nested_container, strict positivity of its uniform parameters,
      uniform parameters, their instantiation, and that of both non_uniform parameters and indices *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, ainstantiate_all nested argument or a constant. *)
type argument = rel_context * head_argument

(** Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is a uniform parameter, Ind, nested or a constant *)
let view_argument kn mib key_uparams strpos t =
  let* (cxt, hd) = whd_decompose_prod_decls t in
  let@ _ = add_context Old naming_id cxt in
  let* (hd, iargs) = decompose_app hd in
  let* sigma = get_sigma in
  match kind sigma hd with
  | Rel k ->
    begin
      (* Check if the debruijn variable corresponds to a strictly positive uniform parameter *)
      let* pos_up = check_key_in k key_uparams in
      match pos_up with
      | None   -> return @@ (cxt, ArgIsCst)
      | Some i ->
          if List.nth strpos i then
            return @@ (cxt, ArgIsSPUparam (i, iargs))
          else
            return @@ (cxt, ArgIsCst)
    end
  | Ind ((kn_ind, pos_ind as ind), _) ->
    (* If it is the inductive *)
    if kn = kn_ind then
      let (_, local_nuparams_indices) = Array.chop mib.mind_nparams_rec iargs in
      let nb_nuparams = mib.mind_nparams - mib.mind_nparams_rec in
      let (local_nuparams, local_indices) = Array.chop nb_nuparams local_nuparams_indices in
      return @@ (cxt, ArgIsInd (pos_ind, local_nuparams, local_indices))
    (* if there is no argument, it cannot be nested *)
    else if Array.length iargs = 0 then return @@ (cxt, ArgIsCst)
    else
      (* If it may be nested *)
      let* env = get_env in
      let (mib_nested, ind_nested) = lookup_mind_specif env ind in
      let mib_nested_strpos = compute_params_rec_strpos env kn_ind mib_nested in
      (* Check if at least one parameter can be nested upon *)
      if List.exists (fun a -> a) mib_nested_strpos then
        let uparams_nested = of_rel_context @@ fst @@
              split_uparams_nuparams mib_nested mib_nested.mind_params_ctxt in
        let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
        return @@ (cxt, ArgIsNested (GlobRef.IndRef ind, mib_nested_strpos,
                          uparams_nested, inst_uparams, inst_nuparams_indices))
      else
        return @@ (cxt, ArgIsCst)
  | Const (c, _) ->
      let* env = get_env in
      if is_array_type env c then
        let uparam_annot = Context.make_annot (Name (Id.of_string "A")) ERelevance.relevant in
        let uparam_type =  mkType (Univ.Universe.make (Univ.Level.var 0)) in
        assert (Array.length iargs = 1);
        return @@ (cxt, ArgIsNested (GlobRef.ConstRef c, [true],
                          [LocalAssum (uparam_annot, uparam_type)], iargs, [||]))
      else return @@ (cxt, ArgIsCst)
  | _ -> return @@ (cxt, ArgIsCst)


  (** {6 Generate All Predicate } *)

(* To build sparse parametricity:
- For each positive uniform parameter [A : Type] add a predicate [PA : A -> Type]
- For each argument [a : A] add [PA a], for each inductive a recursion hypothesis
- Replace [tInd] by the corresponding [rel]
*)

  (** {7 Functions on Parameters } *)

let get_params_sep sigma mib u =
  let (sigma, params, sub_temp) = Inductiveops.paramdecls_fresh_template sigma (mib, u) in
  let (uparams, nuparams) = split_uparams_nuparams mib params in
  (sigma, uparams, nuparams, sub_temp)

(** Closure of non-uniform parameters if [b], forgetting letins  *)
let closure_nuparams m binder naming_scheme nuparams =
  closure_context m binder Old naming_scheme nuparams

let add_context_nuparams naming_scheme nuparams =
  add_context Old naming_scheme nuparams

(** Closure for indices. They are considered as [Fresh] as they are not in the context of the arguments *)
let closure_indices m binder freshness naming_scheme indb u f =
  let* i = get_indices indb u in
  closure_context m binder freshness naming_scheme i f

    (** {7 Create Fresh Sorts } *)

(** Create a fresh quality and level for each positive uniform parameter *)
let create_fresh_sorts_ql strpos =
  let nb_sorts = List.fold_right (fun a b -> a + b) (List.map Bool.to_int strpos) 0 in
  let init = List.make nb_sorts 0 in
  list_mapi (fun _ _ -> fresh_sort_ql ~sort_rigid:true UnivRigid) init

(** Create a fresh sort for each positive uniform parameter *)
let create_fresh_sorts strpos =
  let nb_sorts = List.fold_right (fun a b -> a + b) (List.map Bool.to_int strpos) 0 in
  let init = List.make nb_sorts 0 in
  list_mapi (fun _ _ ->
      let* (q,l) = fresh_sort_ql ~sort_rigid:true UnivRigid in
      return @@ ESorts.make @@ Sorts.vsort q l
    ) init


    (** {7 Compute the Return Sort} *)

(* Compute if an inductive is nested including for positive parameters to
  be able to create a fresh universe to handle the constrains created due to
  the lack of algebraic universes. *)

let rec is_nested_arg_nested kn mib key_uparams strpos arg : bool t =
  let* (locs, hd) = view_argument kn mib key_uparams strpos arg in
  let@ _ = add_context Old naming_id locs in
  match hd with
  | ArgIsNested (_, _, uparams_nested, inst_uparams, _) ->
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      let is_nested_arg_nested arg =
        let* (loc, hd) = decompose_lambda_decls arg in
        let@ _ = add_context Old naming_hd loc in
        is_nested_arg_nested kn mib key_uparams strpos hd
      in
      let* inst_uparams = array_mapi (fun _ -> is_nested_arg_nested) inst_uparams in
      return @@ Array.exists (fun x -> x) inst_uparams
  | ArgIsSPUparam  _ | ArgIsInd _ -> return true
  | _ -> return false

let is_nested_arg kn mib key_uparams strpos arg =
  let* (locs, hd) = view_argument kn mib key_uparams strpos arg in
  let@ _ = add_context Old naming_id locs in
  match hd with
  | ArgIsNested (_, _, uparams_nested, inst_uparams, _) ->
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      let is_nested_arg_nested arg =
        let* (loc, hd) = decompose_lambda_decls arg in
        let@ _ = add_context Old naming_hd loc in
        is_nested_arg_nested kn mib key_uparams strpos hd
      in
      let* inst_uparams = array_mapi (fun _ -> is_nested_arg_nested) inst_uparams in
      return @@ Array.exists (fun x -> x) inst_uparams
  | _ -> return false

(** Compute if an inductive is nested including for positive uniform parameters *)
let is_nested_ind kn mib ind uparams nuparams strpos : bool t =
  let@ key_uparams = add_context Old naming_id uparams in
  let@ _ = add_context Old naming_id nuparams in
  let* s = get_state in
  let* sigma = get_sigma in
  return @@
  Array.exists (fun ctor ->
      snd @@ run_state s sigma @@
      let* (args, _) = get_args mib EInstance.empty ctor in
      fold_left_state (fun a l -> a::l) args (fun _ arg cc ->
          let* arg_is_nested = is_nested_arg kn mib key_uparams strpos (get_type arg) in
          let@ key_arg  = add_decl Old naming_id arg in
          let* b = cc key_arg in
          return (arg_is_nested || b)
        ) (fun _ -> return false)
    ) ind.mind_nf_lc

(** Compute the return sort of the [all] predicate by adding to the sort of the
    original inductive type:
    - the level of the fresh sort of each fresh predicate,
    - if the inductive is nested including with a positive uniform parameter,
      add a new universe level [ualg] to accumulates constrains coming from
      the instantation of the [all] predicates for nested arguments.
      This is needed due to the lack of algebraic universes.
    *)
let compute_one_return_sort mib ind is_nested u sub_temp fresh_sorts_ql =
  let open Sorts in
  (* Recover the sort of the original inductive type *)
  let* sigma = get_sigma in
  let u = EInstance.kind sigma u in
  let ind_sort = get_inductive_sort (mib, ind) u in
  let ind_sort =
    match sub_temp, Declareops.inductive_template mib with
    | Some sub_temp, Some temp -> Template.template_subst_sort sub_temp temp.template_concl
    | _, _ -> ind_sort
  in
  (* Sup of the original levels + a fresh universe if it is nested.
     Returns the new universe, if there is one, and the return sort *)
  let sort_if_nested is_nested make_sort u =
    let mkSort u = mkSort @@ ESorts.make @@ make_sort u in
    let fresh_sorts_levels = List.map snd fresh_sorts_ql in
    let new_u = List.fold_right Univ.Universe.sup fresh_sorts_levels u in
    if not is_nested then
      return (None, mkSort new_u)
    else
      let* l_alg = new_univ_level_variable UnivRigid in
      let u_alg = Univ.Universe.make l_alg in
      let u_return_sort = Univ.Universe.sup new_u u_alg in
      return (Some (mkSort u_alg), mkSort u_return_sort)
  in
  (* Compute the new sort, preserving impredicativity *)
  let* env = get_env in
  if Environ.is_impredicative_sort env ind_sort then
    return (None, mkSort @@ ESorts.make ind_sort)
  else sort_if_nested is_nested (Sorts.make (Sorts.quality ind_sort)) (univ_of_sort ind_sort)

(** Compute the return sort of each [one_inductive_body], and a a fresh sort to
    handle algebraic constrains if the [one_inductive_body] is nested *)
let compute_return_sort kn u sub_temp mib uparams nuparams strpos fresh_sorts_ql =
  array_mapi (fun pos_ind ind ->
      let* ind_is_nested = is_nested_ind kn mib ind uparams nuparams strpos in
      compute_one_return_sort mib ind ind_is_nested u sub_temp fresh_sorts_ql
    ) mib.mind_packets


    (** {7 Generate the Type of All } *)

let rebind_applied_arity m naming_scheme key_arg cc =
  (* decompose the arity *)
  let* arg_ty = State.get_type key_arg in
  let* (locs, hd) = whd_decompose_prod_decls arg_ty in
  let@ key_locs = closure_context fid Prod Fresh naming_scheme locs in
  (* make args *)
  let* locs_tm = get_terms key_locs in
  let* arg_tm = get_term key_arg in
  let head = mkApp (arg_tm, locs_tm) in
  (* rebind the arity apply to the local variables*)
  let* sigma = get_sigma in
  let head_rev = ESorts.relevance_of_sort @@ destSort sigma hd in
  let head_name = make_annot Anonymous head_rev in
  let@ key_head = build_binder fid Prod Fresh naming_scheme @@ LocalAssum (head_name, head) in
  (* continuation *)
  cc (key_locs, key_head)

(** Create a fresh predicate [PA : A -> Type] given a variable that is an arity *)
let mkPred key_arg sort =
  let@ _ = rebind_applied_arity fid naming_hd key_arg in
  return sort

(** Create the assumption that a predicate [PA : A -> Type] hold [forall a, PA a]
    given a variable that is an arity *)
let mkPredHold key_arg key_pred =
  let@ (key_locs, key_head) = rebind_applied_arity fid naming_hd key_arg in
  (* Return PA x1 ... xn a *)
  let* locs = get_terms key_locs in
  let* head = get_term key_head in
  let* pred = get_term key_pred in
  return @@ mkApp (pred, Array.concat [locs; [|head|]])

(** Given the position of uniform parameter that is positive, return the
    position among the positive uniform parameters *)
let pos_uparams_to_pos_spuparams j strpos =
  let rec aux i n l =
    match l with
    | [] -> assert false
    | x::_ when x && i = j -> n
    | x::l when x -> aux (i+1) (n+1) l
    | _ :: l -> aux (i+1) n l
  in
  aux 0 0 strpos

(** Take the closure of the uniform parameters adding fresh predicates for
    strictly positive uniform parameters [PA : A -> Type], and that it holds
    [forall a, PA a] if [pred_hold = true] *)
let closure_uparams_preds_hold_gen ~mk_pred_hold binder uparams strpos fresh_sorts cc =
  (* let open Sorts in *)
  let rec aux i key_uparams key_preds key_uparams_preds key_preds_hold tel cc =
    match tel with
    | [] -> cc (((List.rev key_uparams), (List.rev key_preds), (List.rev key_uparams_preds)), (List.rev key_preds_hold))
    | decl :: tel ->
        let@ key_up = binder Old naming_id decl in
        if (Option.has_some @@ get_value decl) then
          aux i key_uparams key_preds key_uparams_preds key_preds_hold tel cc
        else if not (List.nth strpos i) then
          aux (i+1) (key_up::key_uparams) key_preds (key_up::key_uparams_preds) key_preds_hold tel cc
        else
          let pred_sort = List.nth fresh_sorts @@ pos_uparams_to_pos_spuparams i strpos in
          (* create (PA : A -> s) *)
          let pred_id = Name.map (fun id -> Id.of_string @@ "P" ^ Id.to_string id) (get_name decl) in
          let pred_name = make_annot pred_id ERelevance.relevant in
          let* pred_type = mkPred key_up (mkSort pred_sort) in
          let@ key_pred = binder Fresh naming_id @@ LocalAssum (pred_name, pred_type) in
          (* create (HPA : forall a, PA a) *)
          if not mk_pred_hold then
              aux (i+1) (key_up::key_uparams) (key_pred::key_preds) (key_pred::key_up::key_uparams_preds) [] tel cc
          else
            let pred_hold_id = Name.map (fun id -> Id.of_string @@ "HP" ^ Id.to_string id) (get_name decl) in
            let pred_hold_rev = ESorts.relevance_of_sort @@ pred_sort in
            let pred_hold_name = make_annot pred_hold_id pred_hold_rev in
            let* pred_hold_type = mkPredHold key_up key_pred in
            let@ key_pred_hold = binder Fresh naming_id @@ LocalAssum (pred_hold_name, pred_hold_type) in
            aux (i+1) (key_up::key_uparams) (key_pred::key_preds) (key_pred::key_up::key_uparams_preds)
                  (key_pred_hold::key_preds_hold) tel cc
  in
  aux 0 [] [] [] [] (List.rev uparams) cc

let closure_uparams_preds m binder uparams strpos fresh_sorts cc =
  closure_uparams_preds_hold_gen ~mk_pred_hold:false (build_binder m binder) uparams strpos fresh_sorts
    (fun (x,_) -> cc x)

let context_uparams_preds uparams strpos fresh_sorts cc =
  closure_uparams_preds_hold_gen ~mk_pred_hold:false add_decl uparams strpos fresh_sorts
    (fun (x,_) -> cc x)


(** {7 Generate the Type of the [all] predicate } *)

(** Generate the type of the [all] predicate provided the parameters have already been quantified *)
let gen_all_type_param kn pos_ind u mib key_uparams key_nuparams return_sort =
  (* Closure uparams and predicates, nuparams and indices *)
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fid Prod Fresh naming_hd ind u in
  (* Bind the inductive *)
  let* ind_rev = ind_relevance ind u in
  let ind_name = make_annot Anonymous ind_rev in
  let* ind_term = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ _ = make_binder fid Prod naming_hd_fresh ind_name ind_term in
  return return_sort

(** Generate the type of the [all] predicate *)
let gen_all_type kn pos_ind u mib uparams strpos fresh_sorts nuparams return_sort =
  let@ (key_uparams, _, _) = closure_uparams_preds fid Prod uparams strpos fresh_sorts in
  let@ key_nuparams = closure_nuparams fid Prod naming_id nuparams in
  gen_all_type_param kn pos_ind u mib key_uparams key_nuparams return_sort

(** Add the [one_inductive_body] of the [all] predicate in the context *)
let add_inductive kn u mib return_sorts uparams strpos fresh_sorts nuparams cc =
  let* cxt = array_map2i (fun pos_ind ind return_sort ->
      let* ind_rev = ind_relevance ind u in
      let* ind_type = gen_all_type kn pos_ind u mib uparams strpos fresh_sorts nuparams return_sort in
      return (LocalAssum (make_annot Anonymous ind_rev, ind_type))
    ) mib.mind_packets return_sorts in
  add_context Fresh naming_id (List.rev @@ Array.to_list cxt) cc


(** {7 Generate the Type of the New Constructors } *)

(** Recursively compute the predicate, returns [None] if it is not nested *)
let compute_pred to_compute f i x : (constr option) t =
  if to_compute then
    let* (locs, head) = decompose_lambda_decls x in
    let@ key_loc = closure_context fopt Lambda Fresh naming_id locs in
    (* create new variable *)
    let* head_sort = retyping_sort_of head in
    let arg_rev = relevance_of_sort head_sort in
    let arg_name = make_annot Anonymous arg_rev in
    (* let name_var = make_annot Anonymous ERelevance.relevant in *)
    let@ key_arg = make_binder fopt Lambda naming_id arg_name head in
    let* arg_type = State.get_type key_arg in
    (* compute rec call *)
    let* res = f key_arg arg_type in
    return @@ res
else
  return None

(** Recursively compute the predicate, returns [None] if it is not nested *)
let compute_pred_eta to_compute f i x =
  let* res = compute_pred to_compute f i x in
  let* sigma = get_sigma in
  let res = Option.map (Reductionops.shrink_eta sigma) res in
  return res

(** Internal type to be able to refer to inductive blocks either through
    variables or through [MutInd.t] *)
type ('a, 'b) vars_or_kn = IndIsVars of 'a | IndIsKn of 'b

(** Compute the new argument *)
let rec make_rec_call_hyp cache kn pos_ind mib rep_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos ualg key_arg arg_type =
  (* Decompose the argument, rebind local variables and compute the argument *)
  let* (locs, head) = view_argument kn mib key_uparams strpos arg_type in
  let@ key_locals = closure_context fopt Prod Fresh naming_id locs in
  let* arg_term = get_term key_arg in
  let* locs_term = get_terms key_locals in
  let inst_arg = mkApp (arg_term, locs_term) in
  (* Match head *)
  match head with
  | ArgIsSPUparam (pos_uparam, iargs) ->
      let pos_in_keys = pos_uparams_to_pos_spuparams pos_uparam strpos in
      let* pred_tm = geti_term key_preds pos_in_keys in
      let pred = mkApp (pred_tm, Array.concat [ iargs; [|inst_arg|] ]) in
      return @@ Some pred
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
    begin
      let* inst_uparams_preds = get_terms key_uparams_preds in
      let ind_args = Array.concat [inst_uparams_preds; inst_nuparams; inst_indices; [|inst_arg|]] in
      match rep_inds with
      | IndIsVars key_inds ->
          let* ind = geti_term key_inds pos_ind_block in
          return @@ Some (mkApp (ind, ind_args))
      | IndIsKn (kn_all, u_all) ->
          return @@ Some (mkApp (mkIndU ((kn_all, pos_ind), u_all), ind_args))
    end
  | ArgIsNested (nested_container, nested_strpos,
                  uparams_nested, inst_uparams, inst_nuparams_indices) ->
      (* eta expand arguments *)
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates *)
      let compute_pred i x b = compute_pred_eta b
            (make_rec_call_hyp cache kn pos_ind mib rep_inds key_up strpos ualg) i x in
      let* rec_preds = array_map2i compute_pred inst_uparams (Array.of_list nested_strpos) in
      (* If at least one argument is nested, lookup the sparse parametricity *)
      let args_are_nested = Array.map Option.has_some rec_preds in
      if Array.for_all not args_are_nested then
        return None
      else begin
        match lookup_all (kn, pos_ind) nested_container (Array.to_list args_are_nested) with
        | Error warn ->
            let () = Warning_scheme_all.warn warn cache in
            return None
        | Ok (partial_nesting, ref_pred) ->
            (* Create: all A0 PA0 ... An PAn B0 ... Bm i0 ... il (arg a0 ... an) *)
            let* rec_hyp = make_all_predicate ~partial_nesting ref_pred nested_strpos
                            inst_uparams rec_preds inst_nuparams_indices inst_arg in
            (* Add constrains with return sort *)
            match ualg with
            | None ->
                return (Some rec_hyp)
            | Some ualg ->
                let* jud = retyping_judgment_of rec_hyp in
                let* () = typing_check_actual_type jud ualg in
                return (Some rec_hyp)
    end
  | _ -> return None

(** Create and bind the recursive call *)
let make_rec_call_cc cache kn pos_ind mib key_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos ualg _ key_arg cc =
  let* arg_type = State.get_type key_arg in
  let* rec_call = make_rec_call_hyp cache kn pos_ind mib (IndIsVars key_inds) key_up strpos ualg key_arg arg_type in
  match rec_call with
  | None ->
      cc [key_arg]
  | Some rec_hyp ->
      (* Compute the relevance after the instantiation *)
      let* rec_hyp_sort = retyping_sort_of rec_hyp in
      let rec_hyp_rev = relevance_of_sort rec_hyp_sort in
      let rec_hyp_name = make_annot Anonymous rec_hyp_rev in
      let@ _ = make_binder fid Prod naming_id rec_hyp_name rec_hyp in
      cc [key_arg]

(** Closure of the args, and of the rec call if [rec_hyp], and if any *)
let closure_args_and_rec_call cache kn pos_ind mib key_inds key_up strpos ualg args =
  read_by_decl args
    (build_binder fid Prod Old naming_hd)
    (fun _ _ cc -> cc [])
    (make_rec_call_cc cache kn pos_ind mib key_inds key_up strpos ualg)

(** Generate the type of the constructors of the [all] predicate supposing
    parameters have already been quantified:
    [ ∀ [args + rec], Indε (UP+PRED) NUP IND (cst up nup args) ] *)
let gen_all_type_ctor cache kn pos_ind u mib key_inds ((key_uparams, key_preds, key_uparams_preds) as key_up) strpos key_nuparams ualg pos_ctor ctor =
  let* (args, indices) = get_args mib u ctor in
  let@ key_args = closure_args_and_rec_call cache kn pos_ind mib key_inds key_up strpos ualg args in
  (* Build the new inductive *)
  let* ind = geti_term key_inds pos_ind in
  let* inst_uparams_preds = get_terms key_uparams_preds in
  let* inst_nuparams = get_terms key_nuparams in
  let* inst_indices = array_mapi (fun _ -> weaken) indices in
  let ind = mkApp (ind, Array.concat [inst_uparams_preds; inst_nuparams; inst_indices]) in
  (* Builds the constructor *)
  let* cst_args = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams cst_args in
  (* Return *)
  return @@ mkApp (ind, [|cst|])


  (** {7 Make Entries } *)

open Entries

(** Generate the [one_inductive_entry] of the [all] predicate *)
let gen_all_one_ind cache suffix kn pos_ind ind u mib return_sorts key_inds key_up strpos key_nuparams : one_inductive_entry t =
  let ulag, return_sort = return_sorts.(pos_ind) in
  let ind_id = add_suffix ind.mind_typename suffix in
  let* ind_type = gen_all_type_param kn pos_ind u mib ((fun (a,_,_) -> a) key_up) key_nuparams return_sort in
  let ctors_id = Array.map (fun x -> add_suffix x suffix) ind.mind_consnames in
  let* ctors_type = array_mapi (gen_all_type_ctor cache kn pos_ind u mib key_inds key_up strpos key_nuparams ulag) ind.mind_nf_lc in
  let* sigma = get_sigma in
  return {
    mind_entry_typename = ind_id ;
    mind_entry_arity = to_constr sigma ind_type ;
    mind_entry_consnames = Array.to_list ctors_id;
    mind_entry_lc = Array.to_list @@ Array.map (to_constr sigma) ctors_type;
  }

let generate_all_aux cache ~poly ~udecl suffix kn u sub_temp mib uparams strpos nuparams =
  (* create fresh sorts, and return types *)
  let* fresh_sorts_ql = create_fresh_sorts_ql strpos in
  let* return_sorts = compute_return_sort kn u sub_temp mib uparams nuparams strpos fresh_sorts_ql in
  let fresh_sorts = List.map (fun (a,b) -> ESorts.make @@ Sorts.vsort a b) fresh_sorts_ql in
  (*uparams + preds, nuparams and recover the context of parameters *)
  let@ key_inds = add_inductive kn u mib (Array.map snd return_sorts) uparams strpos fresh_sorts nuparams in
  let@ key_up = context_uparams_preds uparams strpos fresh_sorts in
  let@ key_nuparams = add_context_nuparams naming_id nuparams in
  let* current_context = get_context in
  let ctxt_params = fst @@ List.chop (List.length current_context - Array.length mib.mind_packets) current_context in
  (* create the inductive body *)
  let* ind_bodies = array_mapi (fun pos_ind ind ->
        gen_all_one_ind cache suffix kn pos_ind ind u mib return_sorts key_inds key_up strpos key_nuparams
      )  mib.mind_packets
  in
  (* universes *)
  let* sigma = get_sigma in
  let* env = get_env in
  let sigma = UnivVariances.register_universe_variances_of_inductive env sigma ~udecl ~cumulative:(PolyFlags.cumulative poly)
                ~params:ctxt_params
                ~arities:(Array.map_to_list (fun x -> EConstr.of_constr x.mind_entry_arity) ind_bodies)
                ~constructors:(Array.map_to_list (fun x -> x.mind_entry_consnames,  List.map EConstr.of_constr x.mind_entry_lc) ind_bodies)
  in
  let uctx = Evd.ustate sigma in
  dbg Pp.(fun () -> str "Before Simpl, Ustate.t = " ++ UState.pr (Evd.ustate sigma) ++ str "\n");
  let uctx = UState.collapse_sort_variables ~only_above_prop:true uctx in
  let uctx = UState.normalize_variables uctx in
  let uctx = UState.minimize ~partial:(false) uctx in
  dbg Pp.(fun () -> str "After Simpl, Ustate.t = " ++ UState.pr (Evd.ustate sigma) ++ str "\n");
  let (inst, auctx) = UVars.abstract_universes @@ UState.context uctx in
  let usubst = UVars.make_instance_subst inst in
  let nf_univs c = CVars.subst_univs_level_constr usubst (UState.nf_universes uctx c) in
  let ind_bodies = Array.map (fun ind ->
    { ind with
    mind_entry_arity = nf_univs ind.mind_entry_arity;
    mind_entry_lc = List.map nf_univs ind.mind_entry_lc
    }
    ) ind_bodies
  in
  (* build mentry *)
  let mie =
    let mind_entry_params = CVars.subst_univs_level_context usubst (EConstr.to_rel_context sigma ctxt_params) in
    {
      mind_entry_record = None;
      mind_entry_finite = mib.mind_finite;
      mind_entry_params;
      mind_entry_inds = Array.to_list ind_bodies;
      mind_entry_universes = Polymorphic_ind_entry (auctx, Some Infer_variances);
      mind_entry_private = mib.mind_private;
      }
  in
  (* DEBUG FUNCTIONS *)
  let* env = get_env in
  let sigma = Evd.set_ustate sigma uctx in
  let () = dbg Pp.(fun () ->
    let params = EConstr.of_rel_context mie.mind_entry_params in
    let ind = List.hd @@ mie.mind_entry_inds in
    let ind_ty = EConstr.of_constr @@ ind.mind_entry_arity in
    let ctors_ty = List.map EConstr.of_constr ind.mind_entry_lc in
    let open Termops.Internal in
        str "Type Sparse Parametricity = "
    ++ (print_constr_env env sigma (it_mkProd_or_LetIn ind_ty params))
    ++ fnl ()
    ++ prlist_with_sep (fun () -> fnl ()) (fun ty_cst ->
         str "Type Constructor " ++ str " = "
      ++ print_constr_env env sigma (it_mkProd_or_LetIn ty_cst params)
      ++ fnl ()
      ) ctors_ty
    )
  in
  (* RETURN *)
  return (uctx, mie)

let generate_all_predicate env sigma kn u mib strpos suffix =
  let cache = Warning_scheme_all.empty_cache () in
  let (sigma, uparams, nuparams, sub_temp) = get_params_sep sigma mib u in
  let open Declareops in
  let univ_poly = inductive_is_polymorphic mib in
  let poly = PolyFlags.make ~univ_poly ~cumulative:(inductive_is_cumulative mib)
               ~collapse_sort_variables:(not univ_poly) in
  let udecl = UState.default_univ_decl in
  dbg Pp.(fun () -> str "strpos = " ++ prlist_with_sep (fun () -> str ", ") bool strpos);
  let (sigma, (uctx, mie)) = run env sigma @@ generate_all_aux cache ~poly ~udecl suffix kn u sub_temp mib uparams strpos nuparams in
  (uctx, mie)


(** {6 Generate the Theorem for the All Predicate } *)

let make_ind_typing (kn, pos_ind) u key_uparams key_nuparams key_indices =
  let tInd = mkIndU ((kn, pos_ind), u)  in
  let* inst_ind = get_terms (key_uparams @ key_nuparams @ key_indices) in
  let* ind = typing_checked_appvect tInd inst_ind in
  return ind

let make_ccl kn_nested pos_ind u_all key_uparams_preds key_nuparams key_indices key_VarMatch =
  make_ind_typing (kn_nested, pos_ind) u_all key_uparams_preds key_nuparams (key_indices @ [key_VarMatch])

let return_type kn kn_nested pos_ind u u_all mib key_uparams key_uparams_preds nuparams =
  let@ key_nuparams = closure_nuparams fid Prod naming_id nuparams in
  (* Closure uparams and predicates, nuparams and indices *)
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fid Prod Fresh naming_hd ind u in
  (* Bind the inductive *)
  let* ind_rev = ind_relevance ind u in
  let ind_name = make_annot Anonymous ind_rev in
  let* ind_term = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fid Prod naming_hd_fresh ind_name ind_term in
  (* Return the sort of the inductive *)
  make_ccl kn_nested pos_ind u_all key_uparams_preds key_nuparams key_indices key_VarMatch

let rec make_rec_call_proof cache kn knu pos_ind mib ((key_uparams, _, _) as key_up) key_preds_hold key_fixs strpos key_arg arg_type =
  (* Decompose the argument, rebind local variables and compute the argument *)
  let* (locs, head) = view_argument kn mib key_uparams strpos arg_type in
  let@ key_locals = closure_context fopt Lambda Fresh naming_id locs in
  let* arg_term = get_term key_arg in
  let* locs_term = get_terms key_locals in
  let inst_arg = mkApp (arg_term, locs_term) in
  (* match head *)
  match head with
  | ArgIsSPUparam (pos_uparam, iargs) ->
      let pos_in_keys = pos_uparams_to_pos_spuparams pos_uparam strpos in
      let* pred_hold_tm = geti_term key_preds_hold pos_in_keys in
      let rec_hyp_proof = mkApp (pred_hold_tm, Array.concat [ iargs; [|inst_arg|] ]) in
      return @@ Some rec_hyp_proof
  | ArgIsInd (pos_ind_block, inst_nuparams, inst_indices) ->
      (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
      let* fix = geti_term key_fixs pos_ind_block in
      return @@ Some (mkApp (fix, Array.concat [inst_nuparams; inst_indices; [|inst_arg|]]))
  | ArgIsNested (nested_container, nested_strpos,
                  uparams_nested, inst_uparams, inst_nuparams_indices) ->
      (* eta expand arguments *)
      let* inst_uparams = eta_expand_instantiation inst_uparams uparams_nested in
      (* Compute the recursive predicates, and their proofs *)
      let compute_pred_preds i x b = compute_pred_eta b (make_rec_call_hyp cache kn pos_ind mib (IndIsKn knu) key_up strpos None) i x in
      let* rec_preds = array_map2i compute_pred_preds inst_uparams (Array.of_list nested_strpos) in
      let compute_pred_holds i x b = compute_pred_eta b (make_rec_call_proof cache kn knu pos_ind mib key_up key_preds_hold key_fixs strpos) i x in
      let* rec_preds_hold = array_map2i compute_pred_holds inst_uparams (Array.of_list nested_strpos) in
      (* If at least one argument is nested, lookup the local fundamental theorem *)
      let args_are_nested = Array.map Option.has_some rec_preds_hold in
      if Array.for_all not args_are_nested then
        return None
      else begin
        match lookup_all_theorem (kn, pos_ind) nested_container (Array.to_list args_are_nested) with
        | Error warn ->
            let () = Warning_scheme_all.warn warn cache in
            return None
        | Ok (partial_nesting, _, ref_thm) ->
            let* rec_hyp_proof = make_all_theorem ~partial_nesting ref_thm nested_strpos inst_uparams
                            rec_preds rec_preds_hold inst_nuparams_indices inst_arg in
            return @@ Some rec_hyp_proof
      end
  | _ -> return None

let compute_args_fix cache kn knu pos_ind mib key_up key_preds_hold key_fixs strpos key_args =
  CList.fold_right_i (fun pos_arg key_arg acc ->
    let* acc = acc in
    let* arg_term = get_term key_arg in
      let* arg_type = State.get_type key_arg in
      let* rec_call_proof = make_rec_call_proof cache kn knu pos_ind mib key_up key_preds_hold key_fixs strpos key_arg arg_type in
      match rec_call_proof with
        | Some rec_call_proof -> return @@ arg_term :: rec_call_proof :: acc
        | None -> return @@ arg_term :: acc
  ) 0 key_args (return [])

let make_cst_typing ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams args =
  let tCst = mkConstructU (((kn, pos_ind), 1+pos_ctor), u) in
  let* params = get_terms (key_uparams @ key_nuparams) in
  typing_checked_appvect tCst (Array.concat [params; args])

let generate_all_theorem_aux cache kn kn_nested focus u mib uparams strpos nuparams : constr t =
  (* 1. Create fresh sorts + new unfiform parameters *)
  let* fresh_sorts = create_fresh_sorts strpos in
  let@ ((key_uparams, key_preds, key_uparams_preds) as key_up, key_preds_hold) =
    closure_uparams_preds_hold_gen ~mk_pred_hold:true (build_binder fid Lambda) uparams strpos fresh_sorts in
  (* Evd.ustate 2. Fixpoint *)
  let* u_all = array_mapi (fun pos_ind _ -> fresh_inductive_instance (kn_nested, pos_ind)) mib.mind_packets in
  let* sigma = get_sigma in
  let relevance_ind ind = relevance_of_sort @@ ESorts.make (get_inductive_sort (mib, ind) (EInstance.kind sigma u)) in
  let fix_name pos_ind ind = make_annot (Name (Id.of_string "F")) (relevance_ind ind) in
  let fix_type pos_ind ind = return_type kn kn_nested pos_ind u u_all.(pos_ind) mib key_uparams key_uparams_preds nuparams in
  let fix_rarg pos_ind ind = (mib.mind_nparams - mib.mind_nparams_rec) + ind.mind_nrealargs in
  let is_rec = Array.length mib.mind_packets > 1 || (Inductiveops.mis_is_recursive mib.mind_packets.(0)) in
  let@ (key_fixs, pos_ind, ind) =
    (* Doe not create a fix if it is not-recursive and only has one inductive body *)
    if is_rec then
      make_fix (Array.to_list mib.mind_packets) focus fix_rarg fix_name fix_type
    else
      fun cc -> cc ([], 0, mib.mind_packets.(0))
  in
    (* 3. Closure Nuparams / Indices / Var *)
  let@ key_nuparams = closure_nuparams fid Lambda naming_id nuparams in
  let ind = mib.mind_packets.(pos_ind) in
  let@ key_indices = closure_indices fid Lambda Fresh naming_hd ind u in
  let* ind_rev = ind_relevance ind u in
  let ind_name = make_annot Anonymous ind_rev in
  let* ind_term = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder fid Lambda naming_hd_fresh ind_name ind_term in
  (* 4 Match to prove P ... x *)
  let case_pred = make_ccl kn_nested pos_ind u_all.(pos_ind) key_uparams_preds key_nuparams in
  let* inst_params = get_terms (key_uparams @ key_nuparams )in
  let* var_match = get_term key_VarMatch in
  let* inst_indices = get_terms key_indices in
  let case_rev = relevance_ind ind in
  let@ (key_args, _, _, pos_ctor) =
    make_case_or_projections naming_hd_fresh mib (kn, pos_ind) ind u key_uparams key_nuparams inst_params
      inst_indices case_pred case_rev var_match in
  (* 5 Body of the branch *)
  let* args = compute_args_fix cache kn (kn_nested, u_all.(pos_ind)) pos_ind mib key_up key_preds_hold key_fixs strpos key_args in
  make_cst_typing ((kn_nested, pos_ind), u_all.(pos_ind)) pos_ctor key_uparams_preds key_nuparams (Array.of_list args)

let generate_all_theorem env sigma kn kn_nested focus u mib strpos =
  let cache = Warning_scheme_all.empty_cache () in
  let (sigma, uparams, nuparams, _) = get_params_sep sigma mib u in
  dbg Pp.(fun () -> str "strpos = " ++ prlist_with_sep (fun () -> str ", ") bool strpos);
  let (sigma, tm) = run env sigma @@ generate_all_theorem_aux cache kn kn_nested focus u mib uparams strpos nuparams in
  dbg Pp.(fun () -> str "All Theorem = " ++ Termops.Internal.print_constr_env env sigma tm ++ fnl ());
  dbg Pp.(fun () -> str "UState = " ++ UState.pr (Evd.ustate sigma) ++ fnl ());
  (sigma, tm)
