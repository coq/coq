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

let position_variance_sup (old_position, old_variance as o) (position, variance) =
  let open Variance in
  match variance with
  | Irrelevant -> o (* The new variance is irrelevant, we keep record of the first relevant position *)
  | _ -> (position, Variance.sup old_variance variance)

let compute_variances env sigma status position variance c =
  let update_variance position variance level status =
    let upd old_variance =
      match old_variance with
      | None -> None
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
  let update_cumul_instance_variances position variance variances inst status =
    let _qs, us = Instance.to_array inst in
    if Array.length variances = Array.length us then
      let update_cumul_var status uvariance u =
        let open Variance in
        match uvariance with
        | Irrelevant -> status (* That's our min *)
        | _ -> let us = Universe.levels u in
          update_variances position (refined_variance variance uvariance) us status
      in
      CArray.fold_left2 update_cumul_var status variances us
    else (* FIXME in case of mismatch, we default to Invariance for everything *)
      update_instance_variances position inst status
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
    | Const _ | Ind _ | Construct _ ->
      let gr, u = Constr.destRef c in
      let gvariance = Environ.variance env gr in
      (match gvariance with
      | None -> update_instance_variances position u status
      | Some gvariance -> update_cumul_instance_variances position variance gvariance u status)
    | Lambda (na, dom, codom) ->
      let status = aux status position (variance_opp variance) dom in
      aux status position variance codom
    | LetIn (na, b, dom, codom) ->
      aux status position variance (Vars.subst1 b codom)
    | _ -> fold_constr_with_binders (fun acc -> acc) (fun ctx status c -> aux status position variance c) () status c
  in
  let c = EConstr.to_constr ~abort_on_undefined_evars:false sigma c in
  aux status position variance c

let compute_variances_context env sigma ?(variance=Variance.Contravariant) status ctx =
  let fold_binder i binder status =
    let open Context.Rel.Declaration in
    compute_variances env sigma status (InBinder i) variance (get_type binder)
  in
  let variances = CList.fold_right_i fold_binder 0 ctx status in
  debug Pp.(fun () -> str"Variances in context: " ++ UnivMinim.pr_variances (Evd.pr_level sigma) variances);
  variances

let compute_variances_body env sigma status c =
  let ctx, c = EConstr.decompose_lambda_decls sigma c in
  let status = compute_variances_context env sigma status ctx in
  compute_variances env sigma status InTerm Variance.Covariant c

let compute_variances_type env sigma status c =
  let ctx, c = EConstr.decompose_prod_decls sigma c in
  let status = compute_variances_context env sigma status ctx in
 compute_variances env sigma status InType Variance.Covariant c

let init_status sigma =
  let ustate = Evd.ustate sigma in
  let uctx = UState.context_set ustate in
  let fn l acc = Level.Map.add l (InTerm, Variance.Irrelevant) acc in
  Level.Set.fold fn (ContextSet.levels uctx) Level.Map.empty

let universe_variances env sigma ?typ body =
  let status = init_status sigma in
  let status = Option.fold_left (compute_variances_type env sigma) status typ in
  let variances = compute_variances_body env sigma status body in
  debug Pp.(fun () -> UnivMinim.pr_variances (Evd.pr_level sigma) variances ++ fnl () ++
    str "Computed from body " ++ Termops.Internal.print_constr_env env sigma body ++ fnl () ++
    str " and type: " ++ Option.cata (Termops.Internal.print_constr_env env sigma) (mt()) typ);
  variances

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
  let status = List.fold_left (fun status (_nas, tys) -> List.fold_left (compute_variances_type env sigma) status tys) status constructors in
  status

let universe_variances_of_record env sigma ~params ~fields ~types =
  let status = init_status sigma in
  let status = compute_variances_context env sigma status params in
  let status = List.fold_left (compute_variances_context env sigma ~variance:Variance.Covariant) status fields in
  let status = List.fold_left (compute_variances_type env sigma) status types in
  status

let universe_variances_of_proofs env sigma proofs =
  let status = init_status sigma in
  List.fold_left (fun status (_, body, typ) ->
    let status = compute_variances_body env sigma status body in
    compute_variances_type env sigma status typ) status proofs

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
