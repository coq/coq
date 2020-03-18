(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Pp
open CErrors
open Util

module Dyn = Dyn.Make ()

type 'a summary_declaration = {
  freeze_function : marshallable:bool -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

module DynMap = Dyn.Map(struct type 'a t = 'a summary_declaration end)

type ml_modules = (string * string option) list

let sum_mod : ml_modules summary_declaration option ref = ref None
let sum_map = ref DynMap.empty

let mangle id = id ^ "-SUMMARY"

let declare_ml_modules_summary decl =
  sum_mod := Some decl

let check_name sumname = match Dyn.name sumname with
| None -> ()
| Some (Dyn.Any tag) ->
  anomaly ~label:"Summary.declare_summary"
    (str "Colliding summary names: " ++ str sumname ++ str " vs. " ++ str (Dyn.repr tag) ++ str ".")

let declare_summary_tag sumname decl =
  let () = check_name (mangle sumname) in
  let tag = Dyn.create (mangle sumname) in
  let () = sum_map := DynMap.add tag decl !sum_map in
  tag

let declare_summary sumname decl =
  ignore(declare_summary_tag sumname decl)

module Frozen = Dyn.Map(struct type 'a t = 'a end)

type frozen = {
  summaries : Frozen.t;
  (** Ordered list w.r.t. the first component. *)
  ml_module : ml_modules option;
  (** Special handling of the ml_module summary. *)
}

let empty_frozen = { summaries = Frozen.empty; ml_module = None }

let freeze_summaries ~marshallable : frozen =
  let fold (DynMap.Any (tag, decl)) accu = Frozen.add tag (decl.freeze_function ~marshallable) accu in
  { summaries = DynMap.fold fold !sum_map Frozen.empty;
    ml_module = Option.map (fun decl -> decl.freeze_function ~marshallable) !sum_mod;
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
  | None -> anomaly (str "Undeclared ML-MODULES summary.")
  | Some decl -> Option.iter decl.unfreeze_function ml_module
  end;
  (* We must be independent on the order of the map! *)
  let ufz (DynMap.Any (name, decl)) =
    try decl.unfreeze_function Frozen.(find name summaries)
    with Not_found ->
      if not partial then begin
        warn_summary_out_of_scope (Dyn.repr name);
        decl.init_function ()
      end;
  in
  (* String.Map.iter unfreeze_single !sum_map *)
  DynMap.iter ufz !sum_map

let init_summaries () =
  DynMap.iter (fun (DynMap.Any (_, decl)) -> decl.init_function ()) !sum_map

(** For global tables registered statically before the end of coqtop
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** Summary projection *)
let project_from_summary { summaries } tag =
  Frozen.find tag summaries

let modify_summary st tag v =
  let () = assert (Frozen.mem tag st.summaries) in
  let summaries = Frozen.add tag v st.summaries in
  {st with summaries}

let remove_from_summary st tag =
  let summaries = Frozen.remove tag st.summaries in
  {st with summaries}

(** All-in-one reference declaration + registration *)

let ref_tag ?(freeze=fun ~marshallable r -> r) ~name x =
  let r = ref x in
  let tag = declare_summary_tag name
    { freeze_function = (fun ~marshallable -> freeze ~marshallable !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) } in
  r, tag

let ref ?freeze ~name x = fst @@ ref_tag ?freeze ~name x

module Local = struct

type 'a local_ref = ('a CEphemeron.key * 'a Dyn.tag) ref

let set r v = r := (CEphemeron.create v, snd !r)

let get r =
  let key, name = !r in
  try CEphemeron.get key
  with CEphemeron.InvalidKey ->
    let { init_function } = DynMap.find name !sum_map in
    init_function ();
    CEphemeron.get (fst !r)

let ref ?(freeze=fun x -> x) ~name init =
  let () = check_name (mangle name) in
  let tag : 'a Dyn.tag = Dyn.create (mangle name) in
  let r = pervasives_ref (CEphemeron.create init, tag) in
  let () = sum_map := DynMap.add tag
    { freeze_function = (fun ~marshallable -> freeze (get r));
      unfreeze_function = (set r);
      init_function = (fun () -> set r init) } !sum_map
  in
  r

let (!) = get
let (:=) = set

end

let dump = Dyn.dump
