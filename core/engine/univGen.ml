(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Sorts
open Names
open Constr
open Univ

(* Generator of levels *)
let new_univ_id =
  let cnt = ref 0 in
  fun () -> incr cnt; !cnt

let new_univ_global () =
  let s = if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else "" in
  Univ.Level.UGlobal.make (Global.current_dirpath ()) s (new_univ_id ())

let fresh_level () =
  Univ.Level.make (new_univ_global ())

let fresh_instance auctx =
  let inst = Array.init (AbstractContext.size auctx) (fun _ -> fresh_level()) in
  let ctx = Array.fold_right Level.Set.add inst Level.Set.empty in
  let inst = Instance.of_array inst in
  inst, (ctx, AbstractContext.instantiate inst auctx)

let existing_instance ?loc auctx inst =
  let () =
    let len1 = Array.length (Instance.to_array inst)
    and len2 = AbstractContext.size auctx in
      if not (len1 == len2) then
        CErrors.user_err ?loc ~hdr:"Universes"
          Pp.(str "Universe instance should have length " ++ int len2 ++ str ".")
      else ()
  in
  inst, (Level.Set.empty, AbstractContext.instantiate inst auctx)

let fresh_instance_from ?loc ctx = function
  | Some inst -> existing_instance ?loc ctx inst
  | None -> fresh_instance ctx

(** Fresh universe polymorphic construction *)

let fresh_global_instance ?loc ?names env gr =
  let auctx = Environ.universes_of_global env gr in
  let u, ctx = fresh_instance_from ?loc auctx names in
  u, ctx

let fresh_constant_instance env c =
  let u, ctx = fresh_global_instance env (GlobRef.ConstRef c) in
  (c, u), ctx

let fresh_inductive_instance env ind =
  let u, ctx = fresh_global_instance env (GlobRef.IndRef ind) in
  (ind, u), ctx

let fresh_constructor_instance env c =
  let u, ctx = fresh_global_instance env (GlobRef.ConstructRef c) in
  (c, u), ctx

let fresh_array_instance env =
  let auctx = CPrimitives.typ_univs CPrimitives.PT_array in
  let u, ctx = fresh_instance_from auctx None in
  u, ctx

let fresh_global_instance ?loc ?names env gr =
  let u, ctx = fresh_global_instance ?loc ?names env gr in
  mkRef (gr, u), ctx

let constr_of_monomorphic_global gr =
  if not (Global.is_polymorphic gr) then
    fst (fresh_global_instance (Global.env ()) gr)
  else CErrors.user_err ~hdr:"constr_of_global"
      Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
          str " would forget universes.")

let fresh_sort_in_family = function
  | InSProp -> Sorts.sprop, ContextSet.empty
  | InProp -> Sorts.prop, ContextSet.empty
  | InSet -> Sorts.set, ContextSet.empty
  | InType ->
    let u = fresh_level () in
      sort_of_univ (Univ.Universe.make u), ContextSet.singleton u

let new_global_univ () =
  let u = fresh_level () in
  (Univ.Universe.make u, ContextSet.singleton u)

let fresh_universe_context_set_instance ctx =
  if ContextSet.is_empty ctx then Level.Map.empty, ctx
  else
    let (univs, cst) = ContextSet.levels ctx, ContextSet.constraints ctx in
    let univs',subst = Level.Set.fold
      (fun u (univs',subst) ->
        let u' = fresh_level () in
          (Level.Set.add u' univs', Level.Map.add u u' subst))
      univs (Level.Set.empty, Level.Map.empty)
    in
    let cst' = subst_univs_level_constraints subst cst in
      subst, (univs', cst')
