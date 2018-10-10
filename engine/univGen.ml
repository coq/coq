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

(* Generator of levels *)
type universe_id = DirPath.t * int

let new_univ_id, set_remote_new_univ_id =
  RemoteCounter.new_counter ~name:"Universes" 0 ~incr:((+) 1)
    ~build:(fun n -> Global.current_dirpath (), n)

let new_univ_level () =
  let dp, id = new_univ_id () in
  Univ.Level.make dp id

let fresh_level () = new_univ_level ()

(* TODO: remove *)
let new_univ dp = Univ.Universe.make (new_univ_level dp)
let new_Type dp = mkType (new_univ dp)
let new_Type_sort dp = Type (new_univ dp)

let fresh_universe_instance ctx =
  let init _ = new_univ_level () in
  Instance.of_array (Array.init (AUContext.size ctx) init)

let fresh_instance_from_context ctx =
  let inst = fresh_universe_instance ctx in
  let constraints = AUContext.instantiate inst ctx in
    inst, constraints

let fresh_instance ctx =
  let ctx' = ref LSet.empty in
  let init _ =
    let u = new_univ_level () in
    ctx' := LSet.add u !ctx'; u
  in
  let inst = Instance.of_array (Array.init (AUContext.size ctx) init)
  in !ctx', inst

let existing_instance ?loc ctx inst =
  let () =
    let len1 = Array.length (Instance.to_array inst)
    and len2 = AUContext.size ctx in
      if not (len1 == len2) then
        CErrors.user_err ?loc ~hdr:"Universes"
          Pp.(str "Universe instance should have length " ++ int len2 ++ str ".")
      else ()
  in LSet.empty, inst

let fresh_instance_from ?loc ctx inst =
  let ctx', inst =
    match inst with
    | Some inst -> existing_instance ?loc ctx inst
    | None -> fresh_instance ctx
  in
  let constraints = AUContext.instantiate inst ctx in
    inst, (ctx', constraints)

(** Fresh universe polymorphic construction *)

open Globnames

let fresh_global_instance ?loc ?names env gr =
  let auctx = Environ.universes_of_global env gr in
  let u, ctx = fresh_instance_from ?loc auctx names in
  u, ctx

let fresh_constant_instance env c =
  let u, ctx = fresh_global_instance env (ConstRef c) in
  (c, u), ctx

let fresh_inductive_instance env ind =
  let u, ctx = fresh_global_instance env (IndRef ind) in
  (ind, u), ctx

let fresh_constructor_instance env c =
  let u, ctx = fresh_global_instance env (ConstructRef c) in
  (c, u), ctx

let fresh_global_instance ?loc ?names env gr =
  let u, ctx = fresh_global_instance ?loc ?names env gr in
  mkRef (gr, u), ctx

let constr_of_global gr =
  let c, ctx = fresh_global_instance (Global.env ()) gr in
    if not (Univ.ContextSet.is_empty ctx) then
      if Univ.LSet.is_empty (Univ.ContextSet.levels ctx) then
        (* Should be an error as we might forget constraints, allow for now
           to make firstorder work with "using" clauses *)
        c
      else CErrors.user_err ~hdr:"constr_of_global"
          Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
              str " would forget universes.")
    else c

let constr_of_global_univ (gr,u) =
  match gr with
  | VarRef id -> mkVar id
  | ConstRef sp -> mkConstU (sp,u)
  | ConstructRef sp -> mkConstructU (sp,u)
  | IndRef sp -> mkIndU (sp,u)

let fresh_global_or_constr_instance env = function
  | IsConstr c -> c, ContextSet.empty
  | IsGlobal gr -> fresh_global_instance env gr

let global_of_constr c =
  match kind c with
  | Const (c, u) -> ConstRef c, u
  | Ind (i, u) -> IndRef i, u
  | Construct (c, u) -> ConstructRef c, u
  | Var id -> VarRef id, Instance.empty
  | _ -> raise Not_found

open Declarations

let type_of_reference env r =
  match r with
  | VarRef id -> Environ.named_type id env, ContextSet.empty
  | ConstRef c ->
     let cb = Environ.lookup_constant c env in
     let ty = cb.const_type in
     begin
       match cb.const_universes with
       | Monomorphic_const _ -> ty, ContextSet.empty
       | Polymorphic_const auctx ->
         let inst, ctx = fresh_instance_from auctx None in
         Vars.subst_instance_constr inst ty, ctx
     end
  | IndRef ind ->
     let (mib, oib as specif) = Inductive.lookup_mind_specif env ind in
     begin
       match mib.mind_universes with
       | Monomorphic_ind _ ->
         let ty = Inductive.type_of_inductive env (specif, Univ.Instance.empty) in
         ty, ContextSet.empty
       | Polymorphic_ind auctx ->
         let inst, ctx = fresh_instance_from auctx  None in
         let ty = Inductive.type_of_inductive env (specif, inst) in
         ty, ctx
       | Cumulative_ind cumi ->
         let inst, ctx =
           fresh_instance_from (ACumulativityInfo.univ_context cumi) None
         in
         let ty = Inductive.type_of_inductive env (specif, inst) in
         ty, ctx
     end

  | ConstructRef cstr ->
    let (mib,oib as specif) =
      Inductive.lookup_mind_specif env (inductive_of_constructor cstr)
    in
    begin
       match mib.mind_universes with
       | Monomorphic_ind _ ->
         Inductive.type_of_constructor (cstr,Instance.empty) specif, ContextSet.empty
       | Polymorphic_ind auctx ->
         let inst, ctx = fresh_instance_from auctx None in
         Inductive.type_of_constructor (cstr,inst) specif, ctx
       | Cumulative_ind cumi ->
         let inst, ctx =
           fresh_instance_from (ACumulativityInfo.univ_context cumi) None
         in
         Inductive.type_of_constructor (cstr,inst) specif, ctx
     end

let type_of_global t = type_of_reference (Global.env ()) t

let fresh_sort_in_family = function
  | InProp -> Sorts.prop, ContextSet.empty
  | InSet -> Sorts.set, ContextSet.empty
  | InType ->
    let u = fresh_level () in
      Type (Univ.Universe.make u), ContextSet.singleton u

let new_sort_in_family sf =
  fst (fresh_sort_in_family sf)

let extend_context (a, ctx) (ctx') =
  (a, ContextSet.union ctx ctx')

let new_global_univ () =
  let u = fresh_level () in
  (Univ.Universe.make u, ContextSet.singleton u)

let fresh_universe_context_set_instance ctx =
  if ContextSet.is_empty ctx then LMap.empty, ctx
  else
    let (univs, cst) = ContextSet.levels ctx, ContextSet.constraints ctx in
    let univs',subst = LSet.fold
      (fun u (univs',subst) ->
        let u' = fresh_level () in
          (LSet.add u' univs', LMap.add u u' subst))
      univs (LSet.empty, LMap.empty)
    in
    let cst' = subst_univs_level_constraints subst cst in
      subst, (univs', cst')
