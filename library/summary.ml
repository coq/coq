(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util

module Dyn = Dyn.Make(struct end)

type marshallable = [ `Yes | `No | `Shallow ]
type 'a summary_declaration = {
  freeze_function : marshallable -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let summaries = ref Int.Map.empty

let mangle id = id ^ "-SUMMARY"

let internal_declare_summary hash sumname sdecl =
  let (infun, outfun) = Dyn.Easy.make_dyn (mangle sumname) in
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

let summary_names = ref []
let name_of_summary name =
  try List.assoc name !summary_names
  with Not_found -> "summary name not found"

let declare_summary sumname decl =
  let hash = String.hash sumname in
  let () = if Int.Map.mem hash !summaries then
    let (name, _) = Int.Map.find hash !summaries in
    anomaly ~label:"Summary.declare_summary"
      (str "Colliding summary names: " ++ str sumname ++ str " vs. " ++ str name)
  in
  all_declared_summaries := Int.Set.add hash !all_declared_summaries;
  summary_names := (hash, sumname) :: !summary_names;
  internal_declare_summary hash sumname decl

type frozen = {
  summaries : (int * Dyn.t) list;
  (** Ordered list w.r.t. the first component. *)
  ml_module : Dyn.t option;
  (** Special handling of the ml_module summary. *)
}

let empty_frozen = { summaries = []; ml_module = None; }

let ml_modules = "ML-MODULES"
let ml_modules_summary = String.hash ml_modules

let freeze_summaries ~marshallable : frozen =
  let fold id (_, decl) accu =
    (* to debug missing Lazy.force
    if marshallable <> `No then begin
      let id, _ = Int.Map.find id !summaries in
      prerr_endline ("begin marshalling " ^ id);
      ignore(Marshal.to_string (decl.freeze_function marshallable) []);
      prerr_endline ("end marshalling " ^ id);
    end;
    /debug *)
    let state = decl.freeze_function marshallable in
    if Int.equal id ml_modules_summary then { accu with ml_module = Some state }
    else { accu with summaries = (id, state) :: accu.summaries }
  in
  Int.Map.fold_right fold !summaries empty_frozen

let unfreeze_summaries fs =
  (* The unfreezing of [ml_modules_summary] has to be anticipated since it
   * may modify the content of [summaries] ny loading new ML modules *)
  let (_, decl) =
    try Int.Map.find ml_modules_summary !summaries
    with Not_found -> anomaly (str "Undeclared summary " ++ str ml_modules)
  in
  let () = match fs.ml_module with
  | None -> anomaly (str "Undeclared summary " ++ str ml_modules)
  | Some state -> decl.unfreeze_function state
  in
  let fold id (_, decl) states =
    if Int.equal id ml_modules_summary then states
    else match states with
    | [] ->
      let () = decl.init_function () in
      []
    | (nid, state) :: rstates ->
      if Int.equal id nid then
        let () = decl.unfreeze_function state in rstates
      else
        let () = decl.init_function () in states
  in
  let fold id decl state =
    try fold id decl state
    with e when CErrors.noncritical e ->
      let e = CErrors.push e in
      Feedback.msg_error
        Pp.(seq [str "Error unfreezing summary %s\n%s\n%!";
                 str (name_of_summary id);
                 CErrors.iprint e]);
      iraise e
  in
  (** We rely on the order of the frozen list, and the order of folding *)
  ignore (Int.Map.fold_left fold !summaries fs.summaries)

let init_summaries () =
  Int.Map.iter (fun _ (_, decl) -> decl.init_function ()) !summaries

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** Selective freeze *)

type frozen_bits = (int * Dyn.t) list

let ids_of_string_list complement ids =
  if not complement then List.map String.hash ids
  else
    let fold accu id =
      let id = String.hash id in
      Int.Set.remove id accu
    in
    let ids = List.fold_left fold !all_declared_summaries ids in
    Int.Set.elements ids

let freeze_summary ~marshallable ?(complement=false) ids =
  let ids = ids_of_string_list complement ids in
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
        let e = CErrors.push e in
        prerr_endline ("Exception unfreezing " ^ name);
        iraise e)
  datas

let surgery_summary { summaries; ml_module } bits =
  let summaries = List.map (fun (id, _ as orig) ->
      try id, List.assoc id bits
      with Not_found -> orig)
    summaries in
  { summaries; ml_module }

let project_summary { summaries; ml_module } ?(complement=false) ids =
  let ids = ids_of_string_list complement ids in
  List.filter (fun (id, _) -> List.mem id ids) summaries

let pointer_equal l1 l2 =
  let ptr_equal d1 d2 =
    let Dyn.Dyn (t1, x1) = d1 in
    let Dyn.Dyn (t2, x2) = d2 in
    match Dyn.eq t1 t2 with
    | None -> false
    | Some Refl -> x1 == x2
    in
  CList.for_all2eq
    (fun (id1,v1) (id2,v2) -> id1 = id2 && ptr_equal v1 v2) l1 l2

(** All-in-one reference declaration + registration *)

let ref ?(freeze=fun _ r -> r) ~name x =
  let r = ref x in
  declare_summary name
    { freeze_function = (fun b -> freeze b !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) };
  r

module Local = struct

type 'a local_ref = ('a CEphemeron.key * string) ref

let (:=) r v = r := (CEphemeron.create v, snd !r)

let (!) r =
  let key, name = !r in
  try CEphemeron.get key
  with CEphemeron.InvalidKey ->
    let _, { init_function } =
      Int.Map.find (String.hash (mangle name)) !summaries in
    init_function ();
    CEphemeron.get (fst !r)

let ref ?(freeze=fun x -> x) ~name init =
  let r = Pervasives.ref (CEphemeron.create init, name) in
  declare_summary name
    { freeze_function = (fun _ -> freeze !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := init) };
  r

end

let dump = Dyn.dump
