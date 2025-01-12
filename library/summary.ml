(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Dyn = Dyn.Make ()

module Stage = struct

type t = Synterp | Interp

let equal x y =
  match x, y with
  | Synterp, Synterp -> true
  | Synterp, Interp -> false
  | Interp, Interp -> true
  | Interp, Synterp -> false

end

type 'a summary_declaration = {
  stage : Stage.t;
  freeze_function : unit -> 'a;
  unfreeze_function : 'a -> unit;
  init_function : unit -> unit }

module Decl = struct type 'a t = 'a summary_declaration end
module DynMap = Dyn.Map(Decl)

module MarshMap = Dyn.Map(struct type 'a t = 'a -> 'a end)

type ml_modules = string list

let sum_mod : ml_modules summary_declaration option ref = ref None
let sum_map_synterp = ref DynMap.empty
let sum_map_interp = ref DynMap.empty
let sum_marsh_synterp = ref MarshMap.empty
let sum_marsh_interp = ref MarshMap.empty

let mangle id = id ^ "-SUMMARY"

let declare_ml_modules_summary decl =
  sum_mod := Some decl

let check_name sumname = match Dyn.name sumname with
| None -> ()
| Some (Dyn.Any t) ->
  CErrors.anomaly ~label:"Summary.declare_summary"
    Pp.(str "Colliding summary names: " ++ str sumname
      ++ str " vs. " ++ str (Dyn.repr t) ++ str ".")

let declare_summary_tag sumname ?make_marshallable decl =
  let () = check_name (mangle sumname) in
  let tag = Dyn.create (mangle sumname) in
  let sum_map, marsh_map = match decl.stage with
    | Synterp -> sum_map_synterp, sum_marsh_synterp
    | Interp -> sum_map_interp, sum_marsh_interp
  in
  let () = sum_map := DynMap.add tag decl !sum_map in
  let () = make_marshallable |> Option.iter (fun f ->
      marsh_map := MarshMap.add tag f !marsh_map)
  in
  tag

let declare_summary sumname ?make_marshallable decl =
  ignore(declare_summary_tag sumname ?make_marshallable decl)

module ID = struct type 'a t = 'a end
module Frozen = Dyn.Map(ID)
module HMap = Dyn.HMap(Decl)(ID)


module type FrozenStage = sig

  (** The type [frozen] is a snapshot of the states of all the registered
      tables of the system. *)

  type frozen

  val empty_frozen : frozen
  val freeze_summaries : unit -> frozen
  val make_marshallable : frozen -> frozen
  val unfreeze_summaries : ?partial:bool -> frozen -> unit
  val init_summaries : unit -> unit
  val project_from_summary : frozen -> 'a Dyn.tag -> 'a

end

let freeze_summaries sum_map =
  let map = { HMap.map = fun tag decl -> decl.freeze_function () } in
  HMap.map map sum_map

let make_marshallable marsh_map summaries =
  let map = { Frozen.map = fun tag v -> match MarshMap.find tag marsh_map with
      | exception Not_found -> v
      | f -> f v }
  in
  Frozen.map map summaries

let warn_summary_out_of_scope =
  CWarnings.create ~name:"summary-out-of-scope" ~default:Disabled Pp.(fun name ->
      str "A Rocq plugin was loaded inside a local scope (such as a Section)." ++ spc() ++
      str "It is recommended to load plugins at the start of the file." ++ spc() ++
      str "Summary entry: " ++ str name)

let unfreeze_summaries ?(partial=false) sum_map summaries =
  (* We must be independent on the order of the map! *)
  let ufz (DynMap.Any (name, decl)) =
    try decl.unfreeze_function Frozen.(find name summaries)
    with Not_found ->
      if not partial then begin
        warn_summary_out_of_scope (Dyn.repr name);
        decl.init_function ()
      end
  in
  DynMap.iter ufz sum_map

let init_summaries sum_map =
  DynMap.iter (fun (DynMap.Any (_, decl)) -> decl.init_function ()) sum_map

module Synterp = struct

  type frozen =
    {
        summaries : Frozen.t;
        (** Ordered list w.r.t. the first component. *)
        ml_module : ml_modules option;
        (** Special handling of the ml_module summary. *)
    }

  let empty_frozen = { summaries = Frozen.empty; ml_module = None }

  let freeze_summaries () =
    let summaries = freeze_summaries !sum_map_synterp in
    { summaries; ml_module = Option.map (fun decl -> decl.freeze_function ()) !sum_mod }

  let make_marshallable { summaries; ml_module } =
    { summaries = make_marshallable !sum_marsh_synterp summaries;
      ml_module }

  let unfreeze_summaries ?(partial=false) { summaries; ml_module } =
    (* The unfreezing of [ml_modules_summary] has to be anticipated since it
    * may modify the content of [summaries] by loading new ML modules *)
    begin match !sum_mod with
    | None -> CErrors.anomaly Pp.(str "Undeclared ML-MODULES summary.")
    | Some decl -> Option.iter decl.unfreeze_function ml_module
    end;
    unfreeze_summaries ~partial !sum_map_synterp summaries

  let init_summaries () =
    init_summaries !sum_map_synterp

  (** Summary projection *)
  let project_from_summary { summaries; _ } tag =
    Frozen.find tag summaries

end

module Interp = struct

type frozen = Frozen.t

let empty_frozen = Frozen.empty

  let freeze_summaries () =
    freeze_summaries !sum_map_interp

  let make_marshallable summaries = make_marshallable !sum_marsh_interp summaries

  let unfreeze_summaries ?(partial=false) summaries =
    unfreeze_summaries ~partial !sum_map_interp summaries

  let init_summaries () =
    init_summaries !sum_map_interp

  (** Summary projection *)
  let project_from_summary summaries tag =
    Frozen.find tag summaries

  let modify_summary summaries tag v =
    let () = assert (Frozen.mem tag summaries) in
    Frozen.add tag v summaries

  let remove_from_summary summaries tag =
    let () = assert (Frozen.mem tag summaries) in
    Frozen.remove tag summaries

end

(** For global tables registered statically before the end of rocq repl
    launch, the following empty [init_function] could be used. *)

let nop () = ()

(** All-in-one reference declaration + registration *)

let ref_tag ?(stage=Stage.Interp) ~name x =
  let r = ref x in
  let tag = declare_summary_tag name
    { stage;
      freeze_function = (fun () -> !r);
      unfreeze_function = ((:=) r);
      init_function = (fun () -> r := x) } in
  r, tag

let ref ?(stage=Stage.Interp) ?(local=false) ~name x =
  if not local then fst @@ ref_tag ~stage ~name x
  else
    let r = ref x in
    let () = declare_summary name
        ~make_marshallable:(fun _ -> None)
        { stage;
          freeze_function = (fun () -> Some !r);
          unfreeze_function = (function Some v -> r := v | None -> r := x);
          init_function = (fun () -> r := x); }
    in
    r

let dump = Dyn.dump
