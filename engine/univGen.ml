(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Names
open Constr
open Univ

type univ_unique_id = int
(* Generator of levels *)
let new_univ_id, set_remote_new_univ_id =
  RemoteCounter.new_counter ~name:"Universes" 0 ~incr:((+) 1)
    ~build:(fun n -> n)

let new_univ_global dp = Univ.Level.UGlobal.make dp (new_univ_id ())
let fresh_level dp = Univ.Level.make (new_univ_global dp)

let fresh_instance dp auctx =
  let inst = Array.init (AUContext.size auctx) (fun _ -> fresh_level dp) in
  let ctx = Array.fold_right LSet.add inst LSet.empty in
  let inst = Instance.of_array inst in
  inst, (ctx, AUContext.instantiate inst auctx)

let existing_instance ?loc auctx inst =
  let () =
    let len1 = Array.length (Instance.to_array inst)
    and len2 = AUContext.size auctx in
      if not (len1 == len2) then
        CErrors.user_err ?loc ~hdr:"Universes"
          Pp.(str "Universe instance should have length " ++ int len2 ++ str ".")
      else ()
  in
  inst, (LSet.empty, AUContext.instantiate inst auctx)

let fresh_instance_from ?loc dp ctx = function
  | Some inst -> existing_instance ?loc ctx inst
  | None -> fresh_instance dp ctx

(** Fresh universe polymorphic construction *)

open Globnames

let fresh_global_instance ?loc ?names dp env gr =
  let auctx = Environ.universes_of_global env gr in
  let u, ctx = fresh_instance_from ?loc dp auctx names in
  u, ctx

let fresh_constant_instance dp env c =
  let u, ctx = fresh_global_instance dp env (ConstRef c) in
  (c, u), ctx

let fresh_inductive_instance dp env ind =
  let u, ctx = fresh_global_instance dp env (IndRef ind) in
  (ind, u), ctx

let fresh_constructor_instance dp env c =
  let u, ctx = fresh_global_instance dp env (ConstructRef c) in
  (c, u), ctx

let fresh_global_instance ?loc ?names dp env gr =
  let u, ctx = fresh_global_instance ?loc ?names dp env gr in
  mkRef (gr, u), ctx

let constr_of_monomorphic_global dp gr =
  if not (Global.is_polymorphic gr) then
    fst (fresh_global_instance dp (Global.env ()) gr)
  else CErrors.user_err ~hdr:"constr_of_global"
      Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
          str " would forget universes.")

let fresh_global_or_constr_instance dp env = function
  | IsConstr c -> c, ContextSet.empty
  | IsGlobal gr -> fresh_global_instance dp env gr

let global_of_constr c =
  match kind c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, Instance.empty
  | _ -> raise Not_found

let fresh_sort_in_family dp = function
  | InSProp -> Sorts.sprop, ContextSet.empty
  | InProp -> Sorts.prop, ContextSet.empty
  | InSet -> Sorts.set, ContextSet.empty
  | InType ->
    let u = fresh_level dp in
      sort_of_univ (Univ.Universe.make u), ContextSet.singleton u

let new_global_univ dp =
  let u = fresh_level dp in
  (Univ.Universe.make u, ContextSet.singleton u)

let fresh_universe_context_set_instance dp ctx =
  if ContextSet.is_empty ctx then LMap.empty, ctx
  else
    let (univs, cst) = ContextSet.levels ctx, ContextSet.constraints ctx in
    let univs',subst = LSet.fold
      (fun u (univs',subst) ->
        let u' = fresh_level dp in
          (LSet.add u' univs', LMap.add u u' subst))
      univs (LSet.empty, LMap.empty)
    in
    let cst' = subst_univs_level_constraints subst cst in
      subst, (univs', cst')
