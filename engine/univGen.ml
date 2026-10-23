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

module QualityOrSet = struct
  type t = Qual of Quality.t | Set

  let equal a b = match a, b with
    | Qual a, Qual b -> Quality.equal a b
    | Set, Set -> true
    | Qual _, Set | Set, Qual _ -> false

  let compare a b = match a, b with
    | Qual a, Qual b -> Quality.compare a b
    | Set, Set -> 0
    | Qual _, Set -> 1
    | Set, Qual _ -> -1

  let eliminates_to a b =
    match a, b with
    | Set, Qual (QConstant QType) -> false
    | _ ->
      let to_qual = function
        | Set -> Quality.qtype
        | Qual q -> q
      in Inductive.raw_eliminates_to (to_qual a) (to_qual b)

  let of_quality q = Qual q
  let of_sort s = match s with
    | Sorts.Set -> Set
    | s -> of_quality (Sorts.quality s)
  let quality q = match q with
    | Set -> Quality.qtype
    | Qual q -> q

  let set = Set

  let qtype = Qual Quality.qtype
  let prop = Qual Quality.qprop
  let sprop = Qual Quality.qsprop

  let is_type q = match q with
    | Set -> false
    | Qual q -> Quality.is_qtype q

  let is_set q = match q with
    | Set -> true
    | Qual _ -> false

  let is_prop q = match q with
    | Set -> false
    | Qual q -> Quality.is_qprop q

  let is_sprop q = match q with
    | Set -> false
    | Qual q -> Quality.is_qsprop q

  let pr prv q = match q with
    | Set -> Pp.str"Set"
    | Qual q -> Quality.pr prv q

  let raw_pr = pr Sorts.Quality.raw_printer

  let all_constants = Set :: List.map (fun q -> Qual q) Quality.all_constants
end

type sort_context_set = (QVar.Set.t * Univ.Level.Set.t) * PConstraints.t

type 'a in_sort_context_set = 'a * sort_context_set

let empty_sort_context = (QVar.Set.empty, Level.Set.empty), PConstraints.empty

let is_empty_sort_context ((qs,us),csts) =
  QVar.Set.is_empty qs && Level.Set.is_empty us && PConstraints.is_empty csts

let sort_context_union ((qs,us),csts) ((qs',us'),csts') =
  ((QVar.Set.union qs qs', Level.Set.union us us'), PConstraints.union csts csts')

let diff_sort_context ((qs,us),csts) ((qs',us'),csts') =
  (QVar.Set.diff qs qs', Level.Set.diff us us'), PConstraints.diff csts csts'

let pr_sort_context printer ((vs, us), cst as ctx) =
  let open Pp in
  if is_empty_sort_context ctx then mt ()
  else
    let vs =
      if Sorts.QVar.Set.is_empty vs then mt ()
      else Sorts.QVar.Set.pr printer.Sorts.prq.prvar vs ++ pr_semicolon ()
    in
    hov 0 (h (vs ++ Level.Set.pr printer.pru us ++ str " |") ++ brk(1,2) ++ h (PConstraints.pr printer cst))

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

let new_unif_sort_id =
  let cnt = ref 0 in
  fun () -> incr cnt; !cnt

let fresh_sort_quality () =
  let s = if Flags.async_proofs_is_worker() then !Flags.async_proofs_worker_id else "" in
  Sorts.QVar.make_unif s (new_unif_sort_id ())

let fresh_instance auctx : _ in_sort_context_set =
  let qlen, ulen = AbstractContext.size auctx in
  let qinst = Array.init qlen (fun _ -> Sorts.Quality.QVar (fresh_sort_quality ())) in
  let uinst = Array.init ulen (fun _ -> fresh_level()) in
  let qctx = Array.fold_left (fun qctx q -> match q with
      | Sorts.Quality.QVar q -> Sorts.QVar.Set.add q qctx
      | _ -> assert false)
      Sorts.QVar.Set.empty
      qinst
  in
  let uctx = Array.fold_right Level.Set.add uinst Level.Set.empty in
  let inst = LevelInstance.of_array (qinst,uinst) in
  let inst = Instance.of_level_instance inst in
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
  let auctx, _variances = CPrimitives.typ_univs CPrimitives.PT_array in
  let u, ctx = fresh_instance_from auctx None in
  u, ctx

let fresh_global_instance ?loc ?names env gr =
  let u, ctx = fresh_global_instance ?loc ?names env gr in
  mkRef (gr, u), ctx

let constr_of_monomorphic_global env gr =
  let gru, ctx = fresh_global_instance env gr in
  if is_empty_sort_context ctx then gru
  else CErrors.user_err
      Pp.(str "globalization of polymorphic reference " ++ Nametab.pr_global_env Id.Set.empty gr ++
          str " would forget universes.")

let fresh_sort_in_quality =
  let open QualityOrSet in
  function
  | Qual (QConstant QSProp) -> Sorts.sprop, empty_sort_context
  | Qual (QConstant QProp) -> Sorts.prop, empty_sort_context
  | Set -> Sorts.set, empty_sort_context
  | Qual (QGlobal _ as q) ->
    let u = fresh_level () in
    Sorts.make q (Univ.Universe.make u), ((QVar.Set.empty,Level.Set.singleton u), PConstraints.empty)
  | Qual (QConstant QType | QVar _ (* Treat as Type *)) ->
     let u = fresh_level () in
     sort_of_univ (Univ.Universe.make u), ((QVar.Set.empty,Level.Set.singleton u), PConstraints.empty)

let fresh_sort_context_instance ((qs,us),csts as ctx) =
  let ufold u (univs',subst) =
    let u' = fresh_level () in
    (Level.Set.add u' univs', Level.Map.add u (Universe.make u') subst)
  in
  let qfold q (qs, qsubst) =
    let q' = fresh_sort_quality () in
    QVar.Set.add q' qs, QVar.Map.add q (Sorts.Quality.QVar q') qsubst
  in
  if QVar.Set.is_empty qs && Level.Set.is_empty us then
    (QVar.Map.empty, Level.Map.empty), ctx
  else
    let us, usubst = Level.Set.fold ufold us (Level.Set.empty, Level.Map.empty) in
    let qs, qsubst = QVar.Set.fold qfold qs (QVar.Set.empty, QVar.Map.empty) in
    let csts = subst_poly_constraints (qsubst, usubst) csts in
    (qsubst, usubst), ((qs, us), csts)
