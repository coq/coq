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
open Notation
open Notation_gram

(* Uninterpreted notation levels *)

let notation_level_map = Summary.ref ~name:"notation_level_map" NotationMap.empty

let declare_notation_level ?(onlyprint=false) ntn level =
  try
    let (level,onlyprint) = NotationMap.find ntn !notation_level_map in
    if not onlyprint then anomaly (str "Notation " ++ pr_notation ntn ++ str " is already assigned a level.")
  with Not_found ->
  notation_level_map := NotationMap.add ntn (level,onlyprint) !notation_level_map

let level_of_notation ?(onlyprint=false) ntn =
  let (level,onlyprint') = NotationMap.find ntn !notation_level_map in
  if onlyprint' && not onlyprint then raise Not_found;
  level

(**********************************************************************)
(* Equality *)

open Extend

let parenRelation_eq t1 t2 = match t1, t2 with
| L, L | E, E | Any, Any -> true
| Prec l1, Prec l2 -> Int.equal l1 l2
| _ -> false

let production_position_eq pp1 pp2 = match (pp1,pp2) with
| BorderProd (side1,assoc1), BorderProd (side2,assoc2) -> side1 = side2 && assoc1 = assoc2
| InternalProd, InternalProd -> true
| (BorderProd _ | InternalProd), _ -> false

let production_level_eq l1 l2 = match (l1,l2) with
| NextLevel, NextLevel -> true
| NumLevel n1, NumLevel n2 -> Int.equal n1 n2
| (NextLevel | NumLevel _), _ -> false

let constr_entry_key_eq eq v1 v2 = match v1, v2 with
| ETIdent, ETIdent -> true
| ETGlobal, ETGlobal -> true
| ETBigint, ETBigint -> true
| ETBinder b1, ETBinder b2 -> b1 == b2
| ETConstr (s1,bko1,lev1), ETConstr (s2,bko2,lev2) ->
   notation_entry_eq s1 s2 && eq lev1 lev2 && Option.equal (=) bko1 bko2
| ETPattern (b1,n1), ETPattern (b2,n2) -> b1 = b2 && Option.equal Int.equal n1 n2
| (ETIdent | ETGlobal | ETBigint | ETBinder _ | ETConstr _ | ETPattern _), _ -> false

let level_eq_gen strict (s1, l1, t1, u1) (s2, l2, t2, u2) =
  let tolerability_eq (i1, r1) (i2, r2) = Int.equal i1 i2 && parenRelation_eq r1 r2 in
  let prod_eq (l1,pp1) (l2,pp2) =
    not strict ||
    (production_level_eq l1 l2 && production_position_eq pp1 pp2) in
  notation_entry_eq s1 s2 && Int.equal l1 l2 && List.equal tolerability_eq t1 t2
  && List.equal (constr_entry_key_eq prod_eq) u1 u2

let level_eq = level_eq_gen false
