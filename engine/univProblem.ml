(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

type t =
  | QEq of Sorts.Quality.t * Sorts.Quality.t
  | QLeq of Sorts.Quality.t * Sorts.Quality.t
  | ULe of Sorts.t * Sorts.t
  | UEq of Sorts.t * Sorts.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t


let is_trivial = function
  | QLeq (QConstant QProp, QConstant QType) -> true
  | QLeq (a,b) | QEq (a, b) -> Sorts.Quality.equal a b
  | ULe (u, v) | UEq (u, v) -> Sorts.equal u v
  | ULub (u, v) | UWeak (u, v) -> Level.equal u v

let force = function
  | QEq _ | QLeq _ | ULe _ | UEq _ | UWeak _ as cst -> cst
  | ULub (u,v) -> UEq (Sorts.sort_of_univ @@ Universe.make u, Sorts.sort_of_univ @@ Universe.make v)

let check_eq_level g u v = UGraph.check_eq_level g u v

module Set = struct
  module S = Set.Make(
  struct
    type nonrec t = t

    let compare x y =
      match x, y with
      | QEq (a, b), QEq (a', b') ->
        let i = Sorts.Quality.compare a a' in
        if i <> 0 then i
        else Sorts.Quality.compare b b'
      | QLeq (a, b), QLeq (a', b') ->
        let i = Sorts.Quality.compare a a' in
        if i <> 0 then i
        else Sorts.Quality.compare b b'
      | ULe (u, v), ULe (u', v') ->
        let i = Sorts.compare u u' in
        if Int.equal i 0 then Sorts.compare v v'
        else i
      | UEq (u, v), UEq (u', v') ->
        let i = Sorts.compare u u' in
        if Int.equal i 0 then Sorts.compare v v'
        else if Sorts.equal u v' && Sorts.equal v u' then 0
        else i
      | ULub (u, v), ULub (u', v') | UWeak (u, v), UWeak (u', v') ->
        let i = Level.compare u u' in
        if Int.equal i 0 then Level.compare v v'
        else if Level.equal u v' && Level.equal v u' then 0
        else i
      | QEq _, _ -> -1
      | _, QEq _ -> 1
      | QLeq _, _ -> -1
      | _, QLeq _ -> 1
      | ULe _, _ -> -1
      | _, ULe _ -> 1
      | UEq _, _ -> -1
      | _, UEq _ -> 1
      | ULub _, _ -> -1
      | _, ULub _ -> 1
  end)

  include S

  let add cst s =
    if is_trivial cst then s
    else add cst s

  let pr_one = let open Pp in function
    | QEq (a, b) -> Sorts.Quality.raw_pr a ++ str " = " ++ Sorts.Quality.raw_pr b
    | QLeq (a, b) -> Sorts.Quality.raw_pr a ++ str " <= " ++ Sorts.Quality.raw_pr b
    | ULe (u, v) -> Sorts.debug_print u ++ str " <= " ++ Sorts.debug_print v
    | UEq (u, v) -> Sorts.debug_print u ++ str " = " ++ Sorts.debug_print v
    | ULub (u, v) -> Level.raw_pr u ++ str " /\\ " ++ Level.raw_pr v
    | UWeak (u, v) -> Level.raw_pr u ++ str " ~ " ++ Level.raw_pr v

  let pr c =
    let open Pp in
    fold (fun cst pp_std ->
        pp_std ++ pr_one cst ++ fnl ()) c (str "")

  let equal x y =
    x == y || equal x y

  let force s = map force s
end

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

let enforce_eq_instances_univs strict x y c =
  let mkU u = Sorts.sort_of_univ @@ Universe.make u in
  let mk u v = if strict then ULub (u, v) else UEq (mkU u, mkU v) in
  if not (UVars.eq_sizes (UVars.Instance.length x) (UVars.Instance.length y)) then
    CErrors.anomaly Pp.(str "Invalid argument: enforce_eq_instances_univs called with" ++
                        str " instances of different lengths.");
  let xq, xu = UVars.Instance.to_array x and yq, yu = UVars.Instance.to_array y in
  let c = CArray.fold_left2
      (* TODO strict? *)
      (fun c x y -> if Sorts.Quality.equal x y then c else Set.add (QEq (x,y)) c)
      c xq yq
  in
  let c = CArray.fold_left2
      (fun c x y -> Set.add (mk x y) c)
      c xu yu
  in
  c

let enforce_eq_qualities qs qs' cstrs =
  CArray.fold_left2 (fun c a b ->
      if Sorts.Quality.equal a b then c else Set.add (QEq (a, b)) c)
    cstrs qs qs'

let compare_cumulative_instances  cv_pb variances u u' cstrs =
  let make u = Sorts.sort_of_univ @@ Univ.Universe.make u in
  let qs, us = UVars.Instance.to_array u
  and qs', us' = UVars.Instance.to_array u' in
  let cstrs = enforce_eq_qualities qs qs' cstrs in
  CArray.fold_left3
    (fun cstrs v u u' ->
       let open UVars.Variance in
       match v with
       | Irrelevant -> Set.add (UWeak (u,u')) cstrs
       | Covariant ->
         (match cv_pb with
          | Conversion.CONV -> Set.add (UEq (make u, make u')) cstrs
          | Conversion.CUMUL -> Set.add (ULe (make u, make u')) cstrs)
       | Invariant ->
         Set.add (UEq (make u, make u')) cstrs)
    cstrs variances us us'
