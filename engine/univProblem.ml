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
  | ULe of Universe.t * Universe.t
  | UEq of Universe.t * Universe.t
  | ULub of Level.t * Level.t
  | UWeak of Level.t * Level.t


let is_trivial = function
  | ULe (u, v) | UEq (u, v) -> Universe.equal u v
  | ULub (u, v) | UWeak (u, v) -> Level.equal u v

module Set = struct
  module S = Set.Make(
  struct
    type nonrec t = t

    let compare x y =
      match x, y with
      | ULe (u, v), ULe (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else i
      | UEq (u, v), UEq (u', v') ->
        let i = Universe.compare u u' in
        if Int.equal i 0 then Universe.compare v v'
        else if Universe.equal u v' && Universe.equal v u' then 0
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
    | ULe (u, v) -> Universe.pr u ++ str " <= " ++ Universe.pr v
    | UEq (u, v) -> Universe.pr u ++ str " = " ++ Universe.pr v
    | ULub (u, v) -> Level.pr u ++ str " /\\ " ++ Level.pr v
    | UWeak (u, v) -> Level.pr u ++ str " ~ " ++ Level.pr v

  let pr c =
    let open Pp in
    fold (fun cst pp_std ->
        pp_std ++ pr_one cst ++ fnl ()) c (str "")

  let equal x y =
    x == y || equal x y
end

type 'a accumulator = Set.t -> 'a -> 'a option
type 'a constrained = 'a * Set.t

type 'a constraint_function = 'a -> 'a -> Set.t -> Set.t

let enforce_eq_instances_univs strict x y c =
  let mk u v = if strict then ULub (u, v) else UEq (Universe.make u, Universe.make v) in
  let ax = Instance.to_array x and ay = Instance.to_array y in
    if Array.length ax != Array.length ay then
      CErrors.anomaly Pp.(str "Invalid argument: enforce_eq_instances_univs called with" ++
                          str " instances of different lengths.");
    CArray.fold_right2
      (fun x y -> Set.add (mk x y))
      ax ay c

let to_constraints ~force_weak g s =
  let invalid () =
    raise (Invalid_argument "to_constraints: non-trivial algebraic constraint between universes")
  in
  let tr cst acc =
    match cst with
    | ULub (l, l') -> Constraint.add (l, Eq, l') acc
    | UWeak (l, l') when force_weak -> Constraint.add (l, Eq, l') acc
    | UWeak  _-> acc
    | ULe (l, l') ->
      begin match Universe.level l, Universe.level l' with
        | Some l, Some l' -> Constraint.add (l, Le, l') acc
        | None, Some _ -> enforce_leq l l' acc
        | _, None ->
          if UGraph.check_leq g l l'
          then acc
          else invalid ()
      end
    | UEq (l, l') ->
      begin match Universe.level l, Universe.level l' with
        | Some l, Some l' -> Constraint.add (l, Eq, l') acc
        | None, _ | _, None ->
          if UGraph.check_eq g l l'
          then acc
          else invalid ()
      end
  in
  Set.fold tr s Constraint.empty
