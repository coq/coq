(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ
open UVars
open UnivMinim

let debug = CDebug.create ~name:"UnivVariances" ()

let variance_opp x =
  let open Variance in
  match x with
  | Invariant -> Invariant
  | Irrelevant -> Irrelevant
  | Covariant -> Contravariant
  | Contravariant -> Covariant

let position_variance_sup ({ in_binder; in_term; in_type } as o) (position, variance) =
  let open Variance in
  match variance with
  | Irrelevant -> o (* The new variance is irrelevant, we keep record of the last relevant positions *)
  | _ ->
    match position with
    | InBinder i ->
      (match in_binder with
      | Some (i', old_variance) ->
        { o with in_binder = Some (max i i', Variance.sup old_variance variance) }
      | None -> { o with in_binder = Some (i, variance) })
    | InType ->
        (match in_type with
        | Some old_variance -> { o with in_type = Some (Variance.sup variance old_variance) }
        | None -> { o with in_type = Some variance })
    | InTerm ->
      (match in_term with
      | Some old_variance -> { o with in_term = Some (Variance.sup variance old_variance) }
      | None -> { o with in_term = Some variance })

let global_variances env gr =
  let open Names.GlobRef in
  let open Environ in
  match gr with
  | ConstRef cst ->
    if not (mem_constant cst env) then None
    else let cb = lookup_constant cst env in Declareops.universes_variances cb.const_universes
  | IndRef ind ->
    if not (mem_mind (fst ind) env) then None
    else let mib = lookup_mind (fst ind) env in Declareops.universes_variances mib.mind_universes
  | ConstructRef cstr ->
    if not (mem_mind (fst (fst cstr)) env) then None
    else let mib = lookup_mind (fst (fst cstr)) env in Declareops.universes_variances mib.mind_universes
  | VarRef _id -> None

let occurrence_of (position, variance) =
  match position with
  | InBinder i -> { in_binder = Some (i, variance); in_type = None; in_term = None}
  | InType -> { in_binder = None; in_type = Some variance; in_term = None}
  | InTerm -> { in_binder = None; in_type = None; in_term = Some variance}

let compute_variances_constr env sigma status position variance c =
  let update_variance position variance level status =
    let upd old_variance =
      match old_variance with
      | None -> Some (occurrence_of (position, variance))
      | Some old -> Some (position_variance_sup old (position, variance))
    in
    Level.Map.update level upd status
  in
  let update_variances position variance levels status =
    Level.Set.fold (update_variance position variance) levels status
  in
  let update_instance_variances position inst status =
    let _qs, us = Instance.levels inst in
    update_variances position Invariant us status
  in
  let refined_variance pos variance =
    let open Variance in
    match pos, variance with
    | Covariant, Covariant -> Covariant
    | Contravariant, Contravariant -> Covariant
    | Covariant, Contravariant -> Contravariant
    | Contravariant, Covariant -> Contravariant
    | _, (Irrelevant | Invariant) -> variance
    | Irrelevant, _ | Invariant, _ -> assert false
  in
  let update_cumul_instance_variances ~nargs position variance variances inst status =
    let _qs, us = Instance.to_array inst in
    let variances = UVars.Variances.repr variances in
    if Array.length variances = Array.length us then
      let update_cumul_var status uvariance u =
        let open Variance in
        let uvariance = VariancePos.variance nargs uvariance in
        match uvariance with
        | Irrelevant -> status (* That's our min *)
        | _ -> let us = Universe.levels u in
          update_variances position (refined_variance variance uvariance) us status
      in
      CArray.fold_left2 update_cumul_var status variances us
    else (* FIXME in case of mismatch, we default to Invariance for everything *)
      update_instance_variances position inst status
  in
  let aux_grapp status position variance hd nargs =
    let gr, u = Constr.destRef hd in
    let gvariance = global_variances env gr in
    (match gvariance with
    | None -> update_instance_variances position u status
    | Some gvariance -> update_cumul_instance_variances ~nargs:(UVars.NumArgs nargs) position variance gvariance u status)
  in
  let rec aux status position variance c =
    let open Constr in
    match kind c with
    | Sort u ->
      let levels = Sorts.levels u in
      update_variances position variance levels status
    | Prod (na, dom, codom) ->
      let status = aux status position (variance_opp variance) dom in
      aux status position variance codom
    | Const _ | Ind _ | Construct _ -> aux_grapp status position variance c 0
    | App (f, args) ->
      if Constr.isRef f then
        let status = aux_grapp status position variance f (Array.length args) in
        Array.fold_left (fun status c -> aux status position variance c) status args
      else
        fold_constr_with_binders (fun acc -> acc) (fun ctx status c -> aux status position variance c) () status c
    | Lambda (na, dom, codom) ->
      let status = aux status position (variance_opp variance) dom in
      aux status position variance codom
    | LetIn (na, b, dom, codom) ->
      aux status position variance (Vars.subst1 b codom)
    | _ -> fold_constr_with_binders (fun acc -> acc) (fun ctx status c -> aux status position variance c) () status c
  in
  aux status position variance c

let compute_variances_constr env sigma status position variance c =
  let status = compute_variances_constr env sigma status position variance c in
  debug Pp.(fun () -> str"Variances of " ++ Termops.Internal.print_constr_env env sigma (EConstr.of_constr c) ++ fnl () ++
    UnivMinim.pr_variances (Evd.pr_level sigma) status);
  status

let compute_variances env sigma status position variance c =
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  compute_variances_constr env sigma status position variance c

let compute_variances_context_constr env sigma ?(variance=Variance.Contravariant) status ctx =
  let fold_binder i binder status =
    let open Context.Rel.Declaration in
    compute_variances_constr env sigma status (InBinder i) variance (get_type binder)
  in
  let variances = CList.fold_right_i fold_binder 0 ctx status in
  variances

let compute_variances_context env sigma ?(variance=Variance.Contravariant) status ctx =
  let fold_binder i binder status =
    let open Context.Rel.Declaration in
    compute_variances env sigma status (InBinder i) variance (get_type binder)
  in
  let variances = CList.fold_right_i fold_binder 0 ctx status in
  debug Pp.(fun () -> str"Variances in context: " ++ UnivMinim.pr_variances (Evd.pr_level sigma) variances);
  variances

let compute_variances_body_constr env sigma status c =
  let ctx, c = Term.decompose_lambda_decls c in
  let status = compute_variances_context_constr env sigma status ctx in
  compute_variances_constr env sigma status InTerm Variance.Covariant c

let compute_variances_body env sigma status c =
  compute_variances_body_constr env sigma status (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let compute_variances_type_constr env sigma ?(ctx_variance=Variance.Contravariant) status c =
  let ctx, c = Term.decompose_prod_decls c in
  let status = compute_variances_context_constr env sigma ~variance:ctx_variance status ctx in
  compute_variances_constr env sigma status InType Variance.Covariant c

let compute_variances_type env sigma ?(ctx_variance=Variance.Contravariant) status c =
  compute_variances_type_constr env sigma status ~ctx_variance
    (EConstr.to_constr ~abort_on_undefined_evars:false sigma c)

let init_status _sigma = Level.Map.empty

let universe_variances env sigma ?typ body =
  let status = init_status sigma in
  let status = Option.fold_left (compute_variances_type env sigma) status typ in
  let variances = compute_variances_body env sigma status body in
  debug Pp.(fun () -> UnivMinim.pr_variances (Evd.pr_level sigma) variances ++ fnl () ++
    str "Computed from body " ++ Termops.Internal.print_constr_env env sigma body ++ fnl () ++
    str " and type: " ++ Option.cata (Termops.Internal.print_constr_env env sigma) (mt()) typ);
  variances

let universe_variances_constr env sigma ?typ body =
  let status = init_status sigma in
  let status = Option.fold_left (compute_variances_type_constr env sigma) status typ in
  compute_variances_body_constr env sigma status body


let universe_variances_of_type env sigma typ =
  let status = init_status sigma in
  let variances = compute_variances_type env sigma status typ in
  debug Pp.(fun () -> UnivMinim.pr_variances (Evd.pr_level sigma) variances ++ fnl () ++
    str "Computed from type " ++ Termops.Internal.print_constr_env env sigma typ);
  variances


let universe_variances_of_inductive env sigma ~params ~arities ~constructors =
  let status = init_status sigma in
  let status = compute_variances_context env sigma status params in
  let status = List.fold_left (compute_variances_type env sigma) status arities in
  let status = List.fold_left (fun status (_nas, tys) ->
    List.fold_left (fun status ty ->
      compute_variances_type env sigma status ~ctx_variance:Covariant ty) status tys) status constructors in
  status

let universe_variances_of_record env sigma ~params ~fields ~types =
  let status = init_status sigma in
  let status = compute_variances_context env sigma status params in
  let status = List.fold_left (compute_variances_context env sigma ~variance:Variance.Covariant) status fields in
  let status = List.fold_left (compute_variances_type env sigma) status types in
  status

let universe_variances_of_fix env sigma types bodies =
  let status = init_status sigma in
  List.fold_left2 (fun status typ body ->
    let status = compute_variances_type env sigma status typ in
    Option.fold_left (compute_variances_body env sigma) status body) status types bodies

let universe_variances_of_proofs env sigma proofs =
  let status = init_status sigma in
  List.fold_left (fun status (body, typ) ->
    let status = compute_variances_body_constr env sigma status body in
    compute_variances_type_constr env sigma status typ) status proofs

let universe_variances_of_named_context env sigma ?(variance=Variance.Contravariant) ctx =
  let status = init_status sigma in
  let fold_binder i binder status =
    let open Context.Named.Declaration in
    let status = compute_variances env sigma status (InBinder i) variance (get_type binder) in
    Option.cata (compute_variances env sigma status (InBinder i) variance) status (get_value binder)
  in
  let variances = CList.fold_right_i fold_binder 0 ctx status in
  debug Pp.(fun () -> str"Variances in named context: " ++ UnivMinim.pr_variances (Evd.pr_level sigma) variances);
  variances
