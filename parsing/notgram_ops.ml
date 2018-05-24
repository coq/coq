(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util
open Extend
open Notation_gram

(* Uninterpreted notation levels *)

let notation_level_map = Summary.ref ~name:"notation_level_map" String.Map.empty

let declare_notation_level ?(onlyprint=false) ntn level =
  if String.Map.mem ntn !notation_level_map then
    anomaly (str "Notation " ++ str ntn ++ str " is already assigned a level.");
  notation_level_map := String.Map.add ntn (level,onlyprint) !notation_level_map

let level_of_notation ?(onlyprint=false) ntn =
  let (level,onlyprint') = String.Map.find ntn !notation_level_map in
  if onlyprint' && not onlyprint then raise Not_found;
  level

(**********************************************************************)
(* Operations on scopes *)

let parenRelation_eq t1 t2 = match t1, t2 with
| L, L | E, E | Any, Any -> true
| Prec l1, Prec l2 -> Int.equal l1 l2
| _ -> false

let production_level_eq l1 l2 = true (* (l1 = l2) *)

let production_position_eq pp1 pp2 = true (* pp1 = pp2 *) (* match pp1, pp2 with
| NextLevel, NextLevel -> true
| NumLevel n1, NumLevel n2 -> Int.equal n1 n2
| (NextLevel | NumLevel _), _ -> false *)

let constr_entry_key_eq eq v1 v2 = match v1, v2 with
| ETName, ETName -> true
| ETReference, ETReference -> true
| ETBigint, ETBigint -> true
| ETBinder b1, ETBinder b2 -> b1 == b2
| ETConstr lev1, ETConstr lev2 -> eq lev1 lev2
| ETConstrAsBinder (bk1,lev1), ETConstrAsBinder (bk2,lev2) -> eq lev1 lev2 && bk1 = bk2
| ETPattern (b1,n1), ETPattern (b2,n2) -> b1 = b2 && Option.equal Int.equal n1 n2
| ETOther (s1,s1'), ETOther (s2,s2') -> String.equal s1 s2 && String.equal s1' s2'
| (ETName | ETReference | ETBigint | ETBinder _ | ETConstr _ | ETPattern _ | ETOther _ | ETConstrAsBinder _), _ -> false

let level_eq_gen strict (l1, t1, u1) (l2, t2, u2) =
  let tolerability_eq (i1, r1) (i2, r2) = Int.equal i1 i2 && parenRelation_eq r1 r2 in
  let prod_eq (l1,pp1) (l2,pp2) =
    if strict then production_level_eq l1 l2 && production_position_eq pp1 pp2
    else production_level_eq l1 l2 in
  Int.equal l1 l2 && List.equal tolerability_eq t1 t2
  && List.equal (constr_entry_key_eq prod_eq) u1 u2

let level_eq = level_eq_gen false
