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

type marshallable = [ `Yes | `No | `Shallow ]
type 'a summary_declaration = {
  freeze_function : marshallable -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let summaries = ref Int.Map.empty

let mangle id = id ^ "-SUMMARY"

let internal_declare_summary hash sumname sdecl =
  let (infun, outfun) = Dyn.create (mangle sumname) in
  let dyn_freeze b = infun (sdecl.freeze_function b)
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init }
  in
  summaries := Int.Map.add hash (sumname, ddecl) !summaries

let all_declared_summaries = ref Int.Set.empty

let declare_summary sumname decl =
  let hash = String.hash sumname in
  let () = if Int.Map.mem hash !summaries then
    let (name, _) = Int.Map.find hash !summaries in
    anomaly ~label:"Summary.declare_summary"
      (str "Colliding summary names: " ++ str sumname ++ str " vs. " ++ str name)
  in
  all_declared_summaries := Int.Set.add hash !all_declared_summaries;
  internal_declare_summary hash sumname decl

type frozen = Dyn.t Int.Map.t

let freeze_summaries ~marshallable : frozen =
  let m = ref Int.Map.empty in
  let iter id (_, decl) =
    (* to debug missing Lazy.force
    if marshallable <> `No then begin
      prerr_endline ("begin marshalling " ^ id);
      ignore(Marshal.to_string (decl.freeze_function marshallable) []);
      prerr_endline ("end marshalling " ^ id);
    end;
    /debug *)
    m := Int.Map.add id (decl.freeze_function marshallable) !m
  in
  let () = Int.Map.iter iter !summaries in
  !m

let ml_modules = "ML-MODULES"
let ml_modules_summary = String.hash ml_modules

let unfreeze_summaries fs =
  (* The unfreezing of [ml_modules_summary] has to be anticipated since it
   * may modify the content of [summaries] ny loading new ML modules *)
  let () =
    try
      let (_, decl) = Int.Map.find ml_modules_summary !summaries in
      let state = Int.Map.find ml_modules_summary fs in
      decl.unfreeze_function state
    with Not_found -> anomaly (str"Undeclared summary "++str ml_modules)
  in
  Int.Map.iter
    (fun id (_, decl) ->
       if Int.equal id ml_modules_summary then () (* already unfreezed *)
       else
         try decl.unfreeze_function (Int.Map.find id fs)
         with Not_found -> decl.init_function())
    !summaries

let init_summaries () =
  Int.Map.iter (fun _ (_, decl) -> decl.init_function ()) !summaries

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** Selective freeze *)

type frozen_bits = (int * Dyn.t) list

let freeze_summary ~marshallable ?(complement=false) ids =
  let ids =
    if not complement then List.map String.hash ids
    else
      let fold accu id =
        let id = String.hash id in
        Int.Set.remove id accu
      in
      let ids = List.fold_left fold !all_declared_summaries ids in
      Int.Set.elements ids
  in
    List.map (fun id ->
      let (_, summary) = Int.Map.find id !summaries in
      id, summary.freeze_function marshallable)
    ids

let unfreeze_summary datas =
  List.iter
    (fun (id, data) ->
      let (name, summary) = Int.Map.find id !summaries in
      try summary.unfreeze_function data
      with e ->
        let e = Errors.push e in
        prerr_endline ("Exception unfreezing " ^ name);
        raise e)
  datas

(** All-in-one reference declaration + registration *)

let ref ?(freeze=fun _ r -> r) ~name x =
  let r = ref x in
  declare_summary name
    { freeze_function = (fun b -> freeze b !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) };
  r
