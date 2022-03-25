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

type t =
  | ULe of Sorts.t * Sorts.t
  | UEq of Sorts.t * Sorts.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t


let is_trivial = function
  | ULe (u, v) | UEq (u, v) -> Sorts.equal u v
  | ULub (u, v) | UWeak (u, v) -> Level.equal u v

let force = function
  | ULe _ | UEq _ | UWeak _ as cst -> cst
  | ULub (u,v) -> UEq (Sorts.sort_of_univ @@ Universe.make u, Sorts.sort_of_univ @@ Universe.make v)

let check_eq_level g u v = UGraph.check_eq_level g u v

let check g = function
  | ULe (u,v) -> UGraph.check_leq_sort g u v
  | UEq (u,v) -> UGraph.check_eq_sort g u v
  | ULub (u,v) -> check_eq_level g u v
  | UWeak _ -> true

module Set = struct
  module S = Set.Make(
  struct
    type nonrec t = t

    let compare x y =
      match x, y with
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
    | ULe (u, v) -> Sorts.debug_print u ++ str " <= " ++ Sorts.debug_print v
    | UEq (u, v) -> Sorts.debug_print u ++ str " = " ++ Sorts.debug_print v
    | ULub (u, v) -> Level.pr u ++ str " /\\ " ++ Level.pr v
    | UWeak (u, v) -> Level.pr u ++ str " ~ " ++ Level.pr v

  let pr c =
    let open Pp in
    fold (fun cst pp_std ->
        pp_std ++ pr_one cst ++ fnl ()) c (str "")

  let equal x y =
    x == y || equal x y

  let force s = map force s

  let check g s = for_all (check g) s
end

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

let enforce_eq_instances_univs strict x y c =
  let mkU u = Sorts.sort_of_univ @@ Universe.make u in
  let mk u v = if strict then ULub (u, v) else UEq (mkU u, mkU v) in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly Pp.(str "Invalid argument: enforce_eq_instances_univs called with" ++
                          str " instances of different lengths.");
    CArray.fold_right2
      (fun x y -> Set.add (mk x y))
      ax ay c
