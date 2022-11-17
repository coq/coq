(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp

(* Code to interact with ML "toplevel", in particular, handling ML
   plugin loading.

   We use Fl_dynload to load plugins, which can correctly track
   dependencies, and manage path for us.

   A bit of infrastructure is still in place to support a "legacy"
   mode where Coq used to manage the OCaml include paths and directly
   load .cmxs/.cma files itself.

   We also place here the required code for interacting with the
   Summary and Libobject, and provide an API so plugins can interact
   with this loading/unloading for Coq-specific purposes adding their
   own init functions, given that OCaml cannot unlink a dynamic module.

*)


(* This path is where we look for .cmo/.cmxs using the legacy method *)
let coq_mlpath_copy = ref [Sys.getcwd ()]
let keep_copy_mlpath path =
  let cpath = CUnix.canonical_path_name path in
  let filter path' = not (String.equal cpath path') in
  coq_mlpath_copy := cpath :: List.filter filter !coq_mlpath_copy

module Fl_internals = struct

  (* Check that [m] is a findlib library name *)
  let validate_lib_name m = String.index_opt m '.' <> None

  (* Fl_split.in_words is not exported *)
  let fl_split_in_words s =
    (* splits s in words separated by commas and/or whitespace *)
    let l = String.length s in
    let rec split i j =
      if j < l then
        match s.[j] with
        | (' '|'\t'|'\n'|'\r'|',') ->
          if i<j then (String.sub s i (j-i)) :: (split (j+1) (j+1))
          else split (j+1) (j+1)
        |	_ ->
          split i (j+1)
      else
      if i<j then [ String.sub s i (j-i) ] else []
    in
    split 0 0

  (* simulate what fl_dynload does *)
  let fl_find_plugins lib =
    let base = Findlib.package_directory lib in
    let preds = Findlib.recorded_predicates () in
    let archive = try Findlib.package_property preds lib "plugin"
      with Not_found ->
      try fst (Findlib.package_property_2 ("plugin"::preds) lib "archive")
      with Not_found -> ""
    in
    fl_split_in_words archive |> List.map (Findlib.resolve_path ~base)

  (* We register errors at for Dynlink and Findlib, it is possible to
     do so Symtable too, as we used to do in the bytecode init code.
     *)
  let () = CErrors.register_handler (function
      | Dynlink.Error msg ->
        Some (hov 0 (str "Dynlink error: " ++ str (Dynlink.error_message msg)))
      | Fl_package_base.No_such_package(p,msg) ->
        let paths = Findlib.search_path () in
        Some (hov 0 (str "Findlib error: " ++ str p ++
                     str " not found in:" ++ cut () ++ v 0 (prlist_with_sep cut str paths) ++ fnl() ++ str msg))
      | _ ->
        None
    )

end

module PluginSpec : sig

  type t

  (* Main constructor, takes the format used in Declare ML Module *)
  val of_declare_ml_format : string -> t

  (* repr/unrepr are internal and only needed for the summary and other low-level stuff *)
  val repr : t -> string option * string
  val unrepr : string option * string -> t

  (* Load a plugin, low-level, that is to say, will directly call the
     loading mechanism in OCaml/findlib *)
  val load : t -> unit

  (* Compute a digest, a findlib library name have more than one
     plugin .cmxs, however this is not the case in Coq. Maybe we
     should strengthen this invariant. *)
  val digest : t -> Digest.t list

  val pp : t -> string

  module Set : CSet.S with type elt = t
  module Map : CMap.ExtS with type key = t and module Set := Set

end = struct

  type t = { file : string option; lib : string }

  module Errors = struct

    let plugin_name_should_contain_dot m =
      CErrors.user_err
        Pp.(str Format.(asprintf "%s is not a valid plugin name anymore." m) ++ spc() ++
            str "Plugins should be loaded using their public name" ++ spc () ++
            str "according to findlib, for example package-name.foo and not " ++
            str "foo_plugin.")

    let plugin_name_invalid_format m =
      CErrors.user_err
        Pp.(str Format.(asprintf "%s is not a valid plugin name." m) ++ spc () ++
            str "It should be a public findlib name, e.g. package-name.foo," ++ spc () ++
            str "or a legacy name followed by a findlib public name, e.g. "++ spc () ++
            str "legacy_plugin:package-name.plugin.")

  end

  let legacy_mapping = Core_plugins_findlib_compat.legacy_to_findlib

  let of_declare_ml_format m =
    match String.split_on_char ':' m with
    | [file] when List.mem_assoc file legacy_mapping ->
      { file = Some file; lib = String.concat "." ("coq-core" :: List.assoc file legacy_mapping) }
    | [x] when not (Fl_internals.validate_lib_name x) ->
      Errors.plugin_name_should_contain_dot m
    | [ file; lib ] ->
      { file = Some file; lib }
    | [ lib ] ->
      { file = None; lib }
    | [] -> assert false
    | _ :: _ :: _ ->
      Errors.plugin_name_invalid_format m

  (* Adds the corresponding extension .cmo/.cma or .cmxs. Dune and
     coq_makefile byte plugins do differ in the choice of extension,
     hence the probing. *)
  let select_plugin_version base =
    if Sys.(backend_type = Native)
    then base ^ ".cmxs"
    else
      let name = base ^ ".cmo" in
      if System.is_in_path !coq_mlpath_copy name
      then name else base ^ ".cma"

  let load = function
    | { file = None; lib } ->
      Fl_dynload.load_packages [lib]
    | { file = Some file; lib } ->
      let file = select_plugin_version file in
      let _, gname = System.find_file_in_path ~warn:false !coq_mlpath_copy file in
      Dynlink.loadfile gname;
      Findlib.(record_package Record_load) lib

  let digest s =
    match s with
    | { file = Some file; _ } ->
      let file = select_plugin_version file in
      let _, gname = System.find_file_in_path ~warn:false !coq_mlpath_copy file in
      [Digest.file gname]
    | { file = None; lib } ->
      let plugins = Fl_internals.fl_find_plugins lib in
      List.map Digest.file plugins

  let repr { file; lib } = ( file, lib )
  let unrepr ( file, lib ) = { file; lib }

  let compare { lib = l1; _ } { lib = l2; _ } = String.compare l1 l2

  let pp = function
    | { file = None; lib } -> lib
    | { file = Some file; lib } ->
      let file = select_plugin_version file in
      Filename.basename file ^ " (using legacy method)"

  module Self = struct
      type nonrec t = t
      let compare = compare
    end

  module Set = CSet.Make(Self)
  module Map = CMap.Make(Self)

end

(* If there is a toplevel under Coq *)
type toplevel =
  { load_plugin : PluginSpec.t -> unit
  (** Load a findlib library, given by public name *)
  ; load_module : string -> unit
  (** Load a cmxs / cmo module, used by the native compiler to load objects *)
  ; add_dir  : string -> unit
  (** Adds a dir to the module search path *)
  ; ml_loop  : unit -> unit
  (** Implementation of Drop *)
  }

(* Determines the behaviour of Coq with respect to ML files (compiled
   or not) *)
type kind_load =
  | WithTop of toplevel
  | WithoutTop

(* Must be always initialized *)
let load = ref WithoutTop

(* Sets and initializes a toplevel (if any) *)
let set_top toplevel = load :=
  WithTop toplevel;
  Nativelib.load_obj := toplevel.load_module

(* Removes the toplevel (if any) *)
let remove () =
  load := WithoutTop;
  Nativelib.load_obj := (fun x -> () : string -> unit)

(* Tests if an Ocaml toplevel runs under Coq *)
let is_ocaml_top () =
  match !load with
    | WithTop _ -> true
    |_ -> false

(* Tests if we can load ML files *)
let has_dynlink = Coq_config.has_natdynlink || not Sys.(backend_type = Native)

(* Runs the toplevel loop of Ocaml *)
let ocaml_toploop () =
  match !load with
    | WithTop t -> Printexc.catch t.ml_loop ()
    | _ -> ()

let ml_load p =
  match !load with
  | WithTop t -> t.load_plugin p
  | WithoutTop ->
    PluginSpec.load p

(* Adds a path to the ML paths *)
let add_ml_dir s =
  match !load with
    | WithTop t -> t.add_dir s; keep_copy_mlpath s
    | WithoutTop when has_dynlink -> keep_copy_mlpath s
    | _ -> ()

(** Is the ML code of the standard library placed into loadable plugins
    or statically compiled into coqtop ? For the moment this choice is
    made according to the presence of native dynlink : even if bytecode
    coqtop could always load plugins, we prefer to have uniformity between
    bytecode and native versions. *)

(* [known_loaded_module] contains the names of the loaded ML modules
 * (linked or loaded with load_object). It is used not to load a
 * module twice. It is NOT the list of ML modules Coq knows. *)

(* TODO: Merge known_loaded_module and known_loaded_plugins *)
let known_loaded_modules : PluginSpec.Set.t ref = ref PluginSpec.Set.empty

let add_known_module mname =
  if not (PluginSpec.Set.mem mname !known_loaded_modules) then
    known_loaded_modules := PluginSpec.Set.add mname !known_loaded_modules

let module_is_known mname = PluginSpec.Set.mem mname !known_loaded_modules
let plugin_is_known mname = PluginSpec.Set.mem mname !known_loaded_modules

(** A plugin is just an ML module with an initialization function. *)

let known_loaded_plugins : (unit -> unit) PluginSpec.Map.t ref = ref PluginSpec.Map.empty

let add_known_plugin init name =
  let name = PluginSpec.of_declare_ml_format name in
  add_known_module name;
  known_loaded_plugins := PluginSpec.Map.add name init !known_loaded_plugins

let init_known_plugins () =
  PluginSpec.Map.iter (fun _ f -> f()) !known_loaded_plugins

(** Registering functions to be used at caching time, that is when the Declare
    ML module command is issued. *)

let cache_objs = ref PluginSpec.Map.empty

let declare_cache_obj f name =
  let name = PluginSpec.of_declare_ml_format name in
  let objs = try PluginSpec.Map.find name !cache_objs with Not_found -> [] in
  let objs = f :: objs in
  cache_objs := PluginSpec.Map.add name objs !cache_objs

let perform_cache_obj name =
  let objs = try PluginSpec.Map.find name !cache_objs with Not_found -> [] in
  let objs = List.rev objs in
  List.iter (fun f -> f ()) objs
let perform_cache_obj x = perform_cache_obj x

(** ml object = ml module or plugin *)

let init_ml_object mname =
  try PluginSpec.Map.find mname !known_loaded_plugins ()
  with Not_found -> ()
let init_ml_object x = init_ml_object x

let load_ml_object mname =
  ml_load mname;
  add_known_module mname;
  init_ml_object mname

let add_known_module name =
  let name = PluginSpec.of_declare_ml_format name in
  add_known_module name

let module_is_known mname =
  let mname = PluginSpec.of_declare_ml_format mname in
  module_is_known mname

(* Summary of declared ML Modules *)

(* List and not String.Set because order is important: most recent first. *)

let loaded_modules = ref []
let get_loaded_modules () = List.rev !loaded_modules

(* XXX: It seems this should be part of trigger_ml_object, and
   moreover we should check the guard there *)
let add_loaded_module md =
  if not (List.mem md !loaded_modules) then
    loaded_modules := md :: !loaded_modules
let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name =
  if not verb then f name
  else
    let info = str "[Loading ML file " ++ str (PluginSpec.pp name) ++ str " ..." in
    try
      let path = f name in
      Feedback.msg_info (info ++ str " done]");
      path
    with reraise ->
      Feedback.msg_info (info ++ str " failed]");
      raise reraise

(** Load a module for the first time (i.e. dynlink it)
    or simulate its reload (i.e. doing nothing except maybe
    an initialization function). *)

let trigger_ml_object ~verbose ~cache ~reinit plugin =
  let () =
    if plugin_is_known plugin then
      (if reinit then init_ml_object plugin)
    else
      begin
        if not has_dynlink then
          CErrors.user_err
            (str "Dynamic link not supported (module " ++ str (PluginSpec.pp plugin) ++ str ").")
        else
          if_verbose_load (verbose && not !Flags.quiet) load_ml_object plugin
      end
  in
  add_loaded_module plugin;
  if cache then perform_cache_obj plugin

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter
    (fun name ->
       let name = PluginSpec.unrepr name in
       trigger_ml_object ~verbose:false ~cache:false ~reinit:false name) x

let () =
  Summary.declare_ml_modules_summary
    { Summary.freeze_function = (fun ~marshallable ->
          get_loaded_modules () |> List.map PluginSpec.repr)
    ;
      Summary.unfreeze_function = unfreeze_ml_modules
    ; Summary.init_function = reset_loaded_modules
    }

(* Liboject entries of declared ML Modules *)
type ml_module_object =
  { mlocal : Vernacexpr.locality_flag
  ; mnames : PluginSpec.t list
  ; mdigests : Digest.t list
  }

let cache_ml_objects mnames =
  let iter obj = trigger_ml_object ~verbose:true ~cache:true ~reinit:true obj in
  List.iter iter mnames

let load_ml_objects _ {mnames; _} =
  let iter obj = trigger_ml_object ~verbose:true ~cache:false ~reinit:true obj in
  List.iter iter mnames

let classify_ml_objects {mlocal=mlocal} =
  if mlocal then Libobject.Dispose else Libobject.Substitute

let inMLModule : ml_module_object -> Libobject.obj =
  let open Libobject in
  declare_object
    {(default_object "ML-MODULE") with
      cache_function = (fun _ -> ());
      load_function = load_ml_objects;
      subst_function = (fun (_,o) -> o);
      classify_function = classify_ml_objects }


let declare_ml_modules local l =
  let mnames = List.map PluginSpec.of_declare_ml_format l in
  if Global.sections_are_opened()
  then CErrors.user_err Pp.(str "Cannot Declare ML Module while sections are opened.");
  (* List.concat_map only available in 4.10 *)
  let mdigests = List.map PluginSpec.digest mnames |> List.concat in
  Lib.add_leaf (inMLModule {mlocal=local; mnames; mdigests});
  (* We can't put this in cache_function: it may declare other
     objects, and when the current module is required we want to run
     the ML-MODULE object before them. *)
  cache_ml_objects mnames

let print_ml_path () =
  let l = !coq_mlpath_copy in
  str"ML Load Path:" ++ fnl () ++ str"  " ++
          hv 0 (prlist_with_sep fnl str l)

(* Printing of loaded ML modules *)

let print_ml_modules () =
  let l = get_loaded_modules () in
  str"Loaded ML Modules: " ++ pr_vertical_list str (List.map PluginSpec.pp l)

let print_gc () =
  let stat = Gc.stat () in
  let msg =
    str "minor words: " ++ real stat.Gc.minor_words ++ fnl () ++
    str "promoted words: " ++ real stat.Gc.promoted_words ++ fnl () ++
    str "major words: " ++ real stat.Gc.major_words ++ fnl () ++
    str "minor_collections: " ++ int stat.Gc.minor_collections ++ fnl () ++
    str "major_collections: " ++ int stat.Gc.major_collections ++ fnl () ++
    str "heap_words: " ++ int stat.Gc.heap_words ++ fnl () ++
    str "heap_chunks: " ++ int stat.Gc.heap_chunks ++ fnl () ++
    str "live_words: " ++ int stat.Gc.live_words ++ fnl () ++
    str "live_blocks: " ++ int stat.Gc.live_blocks ++ fnl () ++
    str "free_words: " ++ int stat.Gc.free_words ++ fnl () ++
    str "free_blocks: " ++ int stat.Gc.free_blocks ++ fnl () ++
    str "largest_free: " ++ int stat.Gc.largest_free ++ fnl () ++
    str "fragments: " ++ int stat.Gc.fragments ++ fnl () ++
    str "compactions: " ++ int stat.Gc.compactions ++ fnl () ++
    str "top_heap_words: " ++ int stat.Gc.top_heap_words ++ fnl () ++
    str "stack_size: " ++ int stat.Gc.stack_size
  in
  hv 0 msg
