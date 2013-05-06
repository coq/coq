(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open Errors
open Util

type 'a summary_declaration = {
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let summaries =
  (Hashtbl.create 17 : (string, Dyn.t summary_declaration) Hashtbl.t)

let internal_declare_summary sumname sdecl =
  let (infun,outfun) = Dyn.create sumname in
  let dyn_freeze () = infun (sdecl.freeze_function())
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init }
  in
  Hashtbl.add summaries sumname ddecl

let mangle id = id ^ "-SUMMARY"

let all_declared_summaries = ref CString.Set.empty

let declare_summary sumname decl =
  if CString.Set.mem sumname !all_declared_summaries then
    anomaly ~label:"Summary.declare_summary"
      (str "Cannot declare a summary twice: " ++ str sumname);
  all_declared_summaries := CString.Set.add sumname !all_declared_summaries;
  internal_declare_summary (mangle sumname) decl;

type frozen = Dyn.t String.Map.t

let freeze_summaries () =
  let m = ref String.Map.empty in
  Hashtbl.iter
    (fun id decl -> m := String.Map.add id (decl.freeze_function()) !m)
    summaries;
  !m

let unfreeze_summaries fs =
  Hashtbl.iter
    (fun id decl ->
       try decl.unfreeze_function (String.Map.find id fs)
       with Not_found -> decl.init_function())
    summaries

let init_summaries () =
  Hashtbl.iter (fun _ decl -> decl.init_function()) summaries

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** Selective freeze *)

type frozen_bits = (string * Dyn.t) list

let freeze_summary ~marshallable ?(complement=false) ids =
  let ids =
    if not complement then ids
    else
      CString.Set.elements
        (CString.Set.diff !all_declared_summaries
          (List.fold_right CString.Set.add ids CString.Set.empty))
  in
    List.map (fun id ->
      let id = mangle id in
      let summary = Hashtbl.find summaries id in
      id, summary.freeze_function marshallable)
    ids

let unfreeze_summary datas =
  List.iter
    (fun (id, data) ->
      let summary = Hashtbl.find summaries id in
      summary.unfreeze_function data)
  datas

(** All-in-one reference declaration + registration *)

let ref ~name x =
  let r = ref x in
  declare_summary name
    { freeze_function = (fun () -> !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) };
  r
