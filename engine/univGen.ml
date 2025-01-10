(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open UVars

type sort_context_set = (Sorts.QVar.Set.t * Univ.Level.Set.t) * Univ.Constraints.t

type 'a in_sort_context_set = 'a * sort_context_set

let empty_sort_context = (QVar.Set.empty, Level.Set.empty), Constraints.empty

let is_empty_sort_context ((qs,us),csts) =
  QVar.Set.is_empty qs && Level.Set.is_empty us && Constraints.is_empty csts

let sort_context_union ((qs,us),csts) ((qs',us'),csts') =
  ((QVar.Set.union qs qs', Level.Set.union us us'),Constraints.union csts csts')

let diff_sort_context ((qs,us),csts) ((qs',us'),csts') =
  (QVar.Set.diff qs qs', Level.Set.diff us us'), Constraints.diff csts csts'

type univ_length_mismatch = {
  gref : GlobRef.t;
  actual : int * int;
  expect : int * int;
}
(* Due to an OCaml bug ocaml/ocaml#10027 inlining this record will cause
compliation with -rectypes to crash. *)
exception UniverseLengthMismatch of univ_length_mismatch

let () = CErrors.register_handler (function
    | UniverseLengthMismatch { gref; actual=(aq,au); expect=(eq,eu) } ->
      let ppreal, ppexpected =
        if aq = 0 && eq = 0 then Pp.(int au, int eu)
        else Pp.(str "(" ++ int aq ++ str " | " ++ int au ++ str ")"
                , str "(" ++ int eq ++ str " | " ++ int eu ++ str ")")
      in
      Some Pp.(str "Universe instance length for " ++ Nametab.pr_global_env Id.Set.empty gref ++
               spc() ++ str "is " ++ ppreal ++
               spc() ++ str "but should be " ++ ppexpected ++ str".")
  | _ -> None)

(* Generator of levels *)
let new_univ_id =
  let cnt = ref 0 in
  fun () -> incr cnt; !cnt

let new_univ_global () =
  let s = if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else "" in
  Univ.UGlobal.make (Global.current_dirpath ()) s (new_univ_id ())

let fresh_level () =
  Univ.Level.make (new_univ_global ())

let new_sort_id =
  let cnt = ref 0 in
  fun () -> incr cnt; !cnt

let new_sort_global () =
  let s = if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else "" in
  Sorts.QVar.make_unif s (new_sort_id ())

let fresh_instance auctx : _ in_sort_context_set =
  let qlen, ulen = AbstractContext.size auctx in
  let qinst = Array.init qlen (fun _ -> Sorts.Quality.QVar (new_sort_global())) in
  let uinst = Array.init ulen (fun _ -> fresh_level()) in
  let qctx = Array.fold_left (fun qctx q -> match q with
      | Sorts.Quality.QVar q -> Sorts.QVar.Set.add q qctx
      | _ -> assert false)
      Sorts.QVar.Set.empty
      qinst
  in
  let uctx = Array.fold_right Level.Set.add uinst Level.Set.empty in
  let inst = Instance.of_array (qinst,uinst) in
  inst, ((qctx,uctx), AbstractContext.instantiate inst auctx)

let existing_instance ?loc ~gref auctx inst =
  let () =
    let actual = Instance.length inst
    and expect = AbstractContext.size auctx in
      if not (UVars.eq_sizes actual expect) then
        Loc.raise ?loc (UniverseLengthMismatch { gref; actual; expect })
      else ()
  in
  inst, ((Sorts.QVar.Set.empty,Level.Set.empty), AbstractContext.instantiate inst auctx)

let fresh_instance_from ?loc ctx = function
  | Some (gref,inst) -> existing_instance ?loc ~gref ctx inst
  | None -> fresh_instance ctx

(** Fresh universe polymorphic construction *)

let fresh_global_instance ?loc ?names env gr =
  let auctx = Environ.universes_of_global env gr in
  let names = Option.map (fun x -> gr, x) names in
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

let constr_of_monomorphic_global env gr =
  if not (Environ.is_polymorphic env gr) then
    fst (fresh_global_instance env gr)
  else CErrors.user_err
      Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
          str " would forget universes.")

let fresh_sort_in_family = function
  | InSProp -> Sorts.sprop, empty_sort_context
  | InProp -> Sorts.prop, empty_sort_context
  | InSet -> Sorts.set, empty_sort_context
  | InType | InQSort (* Treat as Type *) ->
    let u = fresh_level () in
      sort_of_univ (Univ.Universe.make u), ((QVar.Set.empty,Level.Set.singleton u),Constraints.empty)

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

let fresh_sort_context_instance ((qs,us),csts) =
  let usubst, (us, csts) = fresh_universe_context_set_instance (us,csts) in
  let qsubst, qs = QVar.Set.fold (fun q (qsubst,qs) ->
      let q' = new_sort_global () in
      QVar.Map.add q (Sorts.Quality.QVar q') qsubst, QVar.Set.add q' qs)
      qs
      (QVar.Map.empty, QVar.Set.empty)
  in
  (qsubst, usubst), ((qs, us), csts)
