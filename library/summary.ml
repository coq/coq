(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open Pp
open CErrors
open Util

module Dyn = Dyn.Make ()

type marshallable =
  [ `No        (* Full data will be store in memory, e.g. for Undo            *)
  | `Shallow ] (* Only part of the data will be marshalled to a slave process *)

type 'a summary_declaration = {
  freeze_function : marshallable -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

let sum_mod = ref None
let sum_map = ref String.Map.empty

let mangle id = id ^ "-SUMMARY"
let unmangle id = String.(sub id 0 (length id - 8))

let ml_modules = "ML-MODULES"

let internal_declare_summary fadd sumname sdecl =
  let infun, outfun, tag = Dyn.Easy.make_dyn_tag (mangle sumname) in
  let dyn_freeze b = infun (sdecl.freeze_function b)
  and dyn_unfreeze sum = sdecl.unfreeze_function (outfun sum)
  and dyn_init = sdecl.init_function in
  let ddecl = {
    freeze_function = dyn_freeze;
    unfreeze_function = dyn_unfreeze;
    init_function = dyn_init }
  in
  fadd sumname ddecl;
  tag

let declare_ml_modules_summary decl =
  let ml_add _ ddecl = sum_mod := Some ddecl in
  internal_declare_summary ml_add ml_modules decl

let declare_ml_modules_summary decl =
  ignore(declare_ml_modules_summary decl)

let declare_summary_tag sumname decl =
  let fadd name ddecl = sum_map := String.Map.add name ddecl !sum_map in
  let () = if String.Map.mem sumname !sum_map then
      anomaly ~label:"Summary.declare_summary"
        (str "Colliding summary names: " ++ str sumname ++ str " vs. " ++ str sumname ++ str ".")
  in
  internal_declare_summary fadd sumname decl

let declare_summary sumname decl =
  ignore(declare_summary_tag sumname decl)

type frozen = {
  summaries : Dyn.t String.Map.t;
  (** Ordered list w.r.t. the first component. *)
  ml_module : Dyn.t option;
  (** Special handling of the ml_module summary. *)
}

let empty_frozen = { summaries = String.Map.empty; ml_module = None }

let freeze_summaries ~marshallable : frozen =
  let smap decl = decl.freeze_function marshallable in
  { summaries = String.Map.map smap !sum_map;
    ml_module = Option.map (fun decl -> decl.freeze_function marshallable) !sum_mod;
  }

let unfreeze_single name state =
  let decl =
    try String.Map.find name !sum_map
    with
    | Not_found ->
      CErrors.anomaly Pp.(str "trying to unfreeze unregistered summary " ++ str name)
  in
  try decl.unfreeze_function state
  with e when CErrors.noncritical e ->
    let e = CErrors.push e in
    Feedback.msg_warning
      Pp.(seq [str "Error unfreezing summary "; str name; fnl (); CErrors.iprint e]);
    iraise e

let unfreeze_summaries ?(partial=false) { summaries; ml_module } =
  (* The unfreezing of [ml_modules_summary] has to be anticipated since it
   * may modify the content of [summaries] by loading new ML modules *)
  begin match !sum_mod with
  | None -> anomaly (str "Undeclared summary " ++ str ml_modules ++ str ".")
  | Some decl -> Option.iter (fun state -> decl.unfreeze_function state) ml_module
  end;
  (** We must be independent on the order of the map! *)
  let ufz name decl =
    try decl.unfreeze_function String.Map.(find name summaries)
    with Not_found ->
      if not partial then begin
        Feedback.msg_warning Pp.(str "Summary was captured out of module scope for entry " ++ str name);
        decl.init_function ()
      end;
  in
  (* String.Map.iter unfreeze_single !sum_map *)
  String.Map.iter ufz !sum_map

let init_summaries () =
  String.Map.iter (fun _ decl -> decl.init_function ()) !sum_map

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** Summary projection *)
let project_from_summary { summaries } tag =
  let id = unmangle (Dyn.repr tag) in
  let state = String.Map.find id summaries in
  Option.get (Dyn.Easy.prj state tag)

let modify_summary st tag v =
  let id = unmangle (Dyn.repr tag) in
  let summaries = String.Map.set id (Dyn.Easy.inj v tag) st.summaries in
  {st with summaries}

let remove_from_summary st tag =
  let id = unmangle (Dyn.repr tag) in
  let summaries = String.Map.remove id st.summaries in
  {st with summaries}

(** Selective freeze *)

type frozen_bits = Dyn.t String.Map.t

let freeze_summary ~marshallable ?(complement=false) ids =
  let sub_map = String.Map.filter (fun id _ -> complement <> List.(mem id ids)) !sum_map in
  String.Map.map (fun decl -> decl.freeze_function marshallable) sub_map

let unfreeze_summary = String.Map.iter unfreeze_single

let surgery_summary { summaries; ml_module } bits =
  let summaries =
    String.Map.fold (fun hash state sum -> String.Map.set hash state sum ) summaries bits in
  { summaries; ml_module }

let project_summary { summaries; ml_module } ?(complement=false) ids =
  String.Map.filter (fun name _ -> complement <> List.(mem name ids)) summaries

let pointer_equal l1 l2 =
  let ptr_equal d1 d2 =
    let Dyn.Dyn (t1, x1) = d1 in
    let Dyn.Dyn (t2, x2) = d2 in
    match Dyn.eq t1 t2 with
    | None -> false
    | Some Refl -> x1 == x2
  in
  let l1, l2 = String.Map.bindings l1, String.Map.bindings l2 in
  CList.for_all2eq
    (fun (id1,v1) (id2,v2) -> id1 = id2 && ptr_equal v1 v2) l1 l2

(** All-in-one reference declaration + registration *)

let ref_tag ?(freeze=fun _ r -> r) ~name x =
  let r = ref x in
  let tag = declare_summary_tag name
    { freeze_function = (fun b -> freeze b !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) } in
  r, tag

let ref ?freeze ~name x = fst @@ ref_tag ?freeze ~name x

module Local = struct

type 'a local_ref = ('a CEphemeron.key * string) ref

let (:=) r v = r := (CEphemeron.create v, snd !r)

let (!) r =
  let key, name = !r in
  try CEphemeron.get key
  with CEphemeron.InvalidKey ->
    let { init_function } = String.Map.find name !sum_map in
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
