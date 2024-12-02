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
open EConstr

let variance_opp x =
  let open Variance in
  match x with
  | Invariant -> Invariant
  | Irrelevant -> Irrelevant
  | Covariant -> Contravariant
  | Contravariant -> Covariant

let compute_variances env sigma status c =
  let update_variance variance level status =
    let upd old_variance =
      match old_variance with
      | None -> None
      | Some old_variance -> Some (Variance.sup variance old_variance)
    in
    Level.Map.update level upd status
  in
  let update_variances variance levels status =
    Level.Set.fold (update_variance variance) levels status
  in
  let update_instance_variances inst status =
    let _qs, us = Instance.levels inst in
    update_variances Invariant us status
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
  let update_cumul_instance_variances variance variances inst status =
    let _qs, us = Instance.to_array inst in
    if Array.length variances = Array.length us then
      let update_cumul_var status uvariance u =
        let open Variance in
        match uvariance with
        | Irrelevant -> status (* That's our min *)
        | _ -> let us = Universe.levels u in
          update_variances (refined_variance variance uvariance) us status
      in
      CArray.fold_left2 update_cumul_var status variances us
    else (* FIXME in case of mismatch, we default to Invariance for everything *)
      update_instance_variances inst status
  in
  let rec aux status variance c =
    match kind sigma c with
    | Sort u ->
      let es = ESorts.kind sigma u in
      let levels = Sorts.levels es in
      update_variances variance levels status
    | Prod (na, dom, codom) ->
      let status = aux status (variance_opp variance) dom in
      aux status variance codom
    | Const _ | Ind _ | Construct _ ->
      let gr, u = EConstr.destRef sigma c in
      let u = EInstance.kind sigma u in
      let gvariance = Environ.variance env gr in
      (match gvariance with
      | None -> update_instance_variances u status
      | Some gvariance -> update_cumul_instance_variances variance gvariance u status)
    | Lambda (na, dom, codom) ->
      let status = aux status (variance_opp variance) dom in
      aux status variance codom
    | LetIn (na, b, dom, codom) ->
        aux status variance (Vars.subst1 b codom)
    | _ -> Termops.fold_constr_with_full_binders env sigma (fun rel acc -> acc) (fun ctx status c -> aux status variance c) () status c
  in aux status Variance.Covariant c

let universe_variances env sigma cs =
  let ustate = Evd.ustate sigma in
  let uctx = UState.context_set ustate in
  let status =
    let fn l acc = Level.Map.add l Variance.Irrelevant acc in
    Level.Set.fold fn (ContextSet.levels uctx) Level.Map.empty
  in
  List.fold_left (compute_variances env sigma) status cs
