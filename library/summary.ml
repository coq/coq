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

module Dyn = Dyn.Make ()

type marshallable = [ `Yes | `No | `Shallow ]

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

let warn_summary_out_of_scope =
  let name = "summary-out-of-scope" in
  let category = "dev" in
  let default = CWarnings.Disabled in
  CWarnings.create ~name ~category ~default (fun name ->
    Pp.str (Printf.sprintf
      "A Coq plugin was loaded inside a local scope (such as a Section). It is recommended to load plugins at the start of the file. Summary entry: %s"
      name)
    )

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
        warn_summary_out_of_scope name;
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
