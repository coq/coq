(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open CErrors
open Util
open Pp

(* Code to hook Coq into the ML toplevel -- depends on having the
   objective-caml compiler mostly visible. The functions implemented here are:
   \begin{itemize}
   \item [dir_ml_load name]: Loads the ML module fname from the current ML
     path.
   \item [dir_ml_use]: Directive #use of Ocaml toplevel
   \item [add_ml_dir]: Directive #directory of Ocaml toplevel
   \end{itemize}

   How to build an ML module interface with these functions.
   The idea is that the ML directory path is like the Coq directory
   path.  So we can maintain the two in parallel.
   In the same way, we can use the "ml_env" as a kind of ML
   environment, which we freeze, unfreeze, and add things to just like
   to the other environments.
   Finally, we can create an object which is an ML module, and require
   that the "caching" of the ML module cause the loading of the
   associated ML file, if that file has not been yet loaded.  Of
   course, the problem is how to record dependencies between ML
   modules.
   (I do not know of a solution to this problem, other than to
   put all the needed names into the ML Module object.) *)


(* This path is where we look for .cmo *)
let coq_mlpath_copy = ref [Sys.getcwd ()]
let keep_copy_mlpath path =
  let cpath = CUnix.canonical_path_name path in
  let filter path' = not (String.equal cpath path')
  in
  coq_mlpath_copy := cpath :: List.filter filter !coq_mlpath_copy

type plugin =
| Legacy of { obj_file_path : string; fl_public_name : string }
| Findlib of { fl_public_name : string }

let pp_plugin = function
| Legacy { obj_file_path; _ } ->
    Filename.(chop_extension @@ basename obj_file_path) ^ " (using legacy method)"
| Findlib { fl_public_name } -> fl_public_name

let canonical_plugin_name = function
  | Findlib { fl_public_name }
  | Legacy { fl_public_name } -> fl_public_name

(* If there is a toplevel under Coq *)
type toplevel = {
  load_obj : plugin -> unit;
  add_dir  : string -> unit;
  ml_loop  : unit -> unit }

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
  Nativelib.load_obj := (fun x ->
    toplevel.load_obj (Legacy { obj_file_path = x; fl_public_name = x }))

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

(* Dynamic loading of .cmo/.cma *)

(* We register errors at least for Dynlink, it is possible to do so Symtable
   too, as we do in the bytecode init code.
*)
let _ = CErrors.register_handler (function
    | Dynlink.Error msg ->
      let paths = Findlib.search_path () in
      Some (hov 0 (str "Dynlink error: " ++ str (Dynlink.error_message msg) ++
        cut () ++ str "Findlib paths:" ++ cut () ++ v 0 (prlist_with_sep cut str paths) ++ fnl()))
    | Fl_package_base.No_such_package(p,msg) ->
      let paths = Findlib.search_path () in
      Some (hov 0 (str "Findlib error: " ++ str p ++
        str " not found in:" ++ cut () ++ v 0 (prlist_with_sep cut str paths) ++ fnl() ++ str msg))
    | _ ->
      None
  )

module Legacy_code_waiting_for_dune_release = struct

(* convertit un nom quelconque en nom de fichier ou de module *)

let get_ml_object_suffix name =
  if Filename.check_suffix name ".cmo" then
    Some ".cmo"
  else if Filename.check_suffix name ".cma" then
    Some ".cma"
  else if Filename.check_suffix name ".cmxs" then
    Some ".cmxs"
  else
    None

let file_of_name name =
  let suffix = get_ml_object_suffix name in
  let fail s =
    user_err
      (str"File not found on loadpath: " ++ str s ++ str"\n" ++
       str"Loadpath: " ++ str(String.concat ":" !coq_mlpath_copy) ++ str ".") in
  if not (Filename.is_relative name) then
    if Sys.file_exists name then name else fail name
  else if Sys.(backend_type = Native) then
    (* XXX: Dynlink.adapt_filename does the same? *)
    let name = match suffix with
      | Some ((".cmo"|".cma") as suffix) ->
          (Filename.chop_suffix name suffix) ^ ".cmxs"
      | Some ".cmxs" -> name
      | _ -> name ^ ".cmxs"
    in
    if System.is_in_path !coq_mlpath_copy name then name else fail name
  else
    let (full, base) = match suffix with
      | Some ".cmo" | Some ".cma" -> true, name
      | Some ".cmxs" -> false, Filename.chop_suffix name ".cmxs"
      | _ -> false, name
    in
    if full then
      if System.is_in_path !coq_mlpath_copy base then base else fail base
    else
      let name = base ^ ".cma" in
      if System.is_in_path !coq_mlpath_copy name then name else
        let name = base ^ ".cmo" in
        if System.is_in_path !coq_mlpath_copy name then name else
          fail (base ^ ".cm[ao]")

  let legacy_mapping = Core_plugins_findlib_compat.legacy_to_findlib

  let rec resolve_legacy_name_if_needed m =
    match String.split_on_char ':' m with
    | [x] when List.mem_assoc x legacy_mapping ->
        resolve_legacy_name_if_needed (m ^ ":coq-core." ^ String.concat "." @@ List.assoc x legacy_mapping)
    | [x] when String.index_opt m '.' = None ->
        CErrors.user_err Pp.(str Printf.(sprintf
         "%s is not a valid plugin name anymore." m) ++ spc() ++
         str "Plugins should be loaded using their public name" ++ spc () ++
         str "according to findlib, for example package-name.foo and not " ++
         str "foo_plugin.")
    | [ x; fl_public_name] ->
        begin try
          let file = file_of_name x in
          let _, obj_file_path = System.find_file_in_path ~warn:false !coq_mlpath_copy file in
          Legacy { obj_file_path; fl_public_name }
        with CErrors.UserError _ ->
          Findlib { fl_public_name }
        end
    | [ fl_public_name ] -> Findlib { fl_public_name }
    | [] -> assert false
    | _ :: _ :: _ ->
        CErrors.user_err Pp.(str Printf.(sprintf
          "%s is not a valid plugin name." m) ++ spc () ++
          str "It should be a public findlib name, e.g. package-name.foo," ++ spc () ++
          str "or a legacy name followed by a findlib public name, e.g. "++ spc () ++
          str "legacy_plugin:package-name.plugin.")

end

let ml_load use_legacy_loading_if_possible p =
  match !load with
  | WithTop t -> t.load_obj p
  | WithoutTop ->
      match p with
      | Findlib { fl_public_name } ->
        Fl_dynload.load_packages [fl_public_name]
      | Legacy { obj_file_path; fl_public_name } ->
        if use_legacy_loading_if_possible then begin
          Dynlink.loadfile obj_file_path;
          Findlib.(record_package Record_load) fl_public_name
        end else
          Fl_dynload.load_packages [fl_public_name]

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

let known_loaded_modules = ref String.Set.empty

let add_known_module mname =
  if not (String.Set.mem mname !known_loaded_modules)  then
    known_loaded_modules := String.Set.add mname !known_loaded_modules

let module_is_known mname =
  String.Set.mem mname !known_loaded_modules
let plugin_is_known x = module_is_known @@ canonical_plugin_name x

(** A plugin is just an ML module with an initialization function. *)

let known_loaded_plugins = ref String.Map.empty

let add_known_plugin init name =
  add_known_module name;
  known_loaded_plugins := String.Map.add name init !known_loaded_plugins

let init_known_plugins () =
  String.Map.iter (fun _ f -> f()) !known_loaded_plugins

(** Registering functions to be used at caching time, that is when the Declare
    ML module command is issued. *)

let cache_objs = ref String.Map.empty

let declare_cache_obj f name =
  let objs = try String.Map.find name !cache_objs with Not_found -> [] in
  let objs = f :: objs in
  cache_objs := String.Map.add name objs !cache_objs

let perform_cache_obj name =
  let objs = try String.Map.find name !cache_objs with Not_found -> [] in
  let objs = List.rev objs in
  List.iter (fun f -> f ()) objs
let perform_cache_obj x = perform_cache_obj @@ canonical_plugin_name x

(** ml object = ml module or plugin *)

let init_ml_object mname =
  try String.Map.find mname !known_loaded_plugins ()
  with Not_found -> ()
let init_ml_object x = init_ml_object @@ canonical_plugin_name x

let load_ml_object use_legacy_loading_if_possible mname =
  ml_load use_legacy_loading_if_possible mname;
  add_known_module @@ canonical_plugin_name mname;
  init_ml_object mname

let add_known_module m = add_known_module m

(* Summary of declared ML Modules *)

(* List and not String.Set because order is important: most recent first. *)

let loaded_modules = ref []
let get_loaded_modules () = List.rev !loaded_modules
let add_loaded_module md =
  if not (List.mem md !loaded_modules) then
    loaded_modules := md :: !loaded_modules
let add_loaded_module (use_legacy_loading_if_possible,p) =
  add_loaded_module (use_legacy_loading_if_possible,canonical_plugin_name p)
let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name =
  if not verb then f name
  else
    let info = str "[Loading ML file " ++ str (pp_plugin name) ++ str " ..." in
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

let trigger_ml_object ~verb ~cache ~reinit ~use_legacy_loading_if_possible s =
  let plugin = Legacy_code_waiting_for_dune_release.resolve_legacy_name_if_needed s in
  if plugin_is_known plugin then begin
    if reinit then init_ml_object plugin;
    add_loaded_module (use_legacy_loading_if_possible,plugin);
    if cache then perform_cache_obj plugin
  end else if not has_dynlink then
    user_err
      (str "Dynamic link not supported (module " ++ str (pp_plugin plugin) ++ str ").")
  else begin
    if_verbose_load (verb && not !Flags.quiet) (load_ml_object use_legacy_loading_if_possible) plugin;
    add_loaded_module (use_legacy_loading_if_possible,plugin);
    if cache then perform_cache_obj plugin
  end

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter
    (fun (use_legacy_loading_if_possible,name) -> trigger_ml_object ~verb:false ~cache:false ~reinit:false ~use_legacy_loading_if_possible name) x

let _ =
  Summary.declare_ml_modules_summary
    { Summary.freeze_function = (fun ~marshallable -> get_loaded_modules ());
      Summary.unfreeze_function = unfreeze_ml_modules;
      Summary.init_function = reset_loaded_modules }

(* Liboject entries of declared ML Modules *)

type ml_module_object = {
  mlocal : Vernacexpr.locality_flag;
  mnames : string list;
  dune_compat_logpathroot : Names.module_ident
}
let current_logpathroot () =
  let open Names in
  List.hd @@ List.rev @@ DirPath.repr @@ ModPath.dp @@ Global.current_modpath ()

let cache_ml_objects mnames =
  let use_legacy_loading_if_possible = true in
  let iter obj = trigger_ml_object ~verb:true ~cache:true ~reinit:true ~use_legacy_loading_if_possible obj in
  List.iter iter mnames

let load_ml_objects _ {mnames; dune_compat_logpathroot; _} =
  let use_legacy_loading_if_possible =
    Names.Id.equal dune_compat_logpathroot (current_logpathroot ()) in
  let iter obj = trigger_ml_object ~verb:true ~cache:false ~reinit:true ~use_legacy_loading_if_possible obj in
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
  if Global.sections_are_opened()
  then user_err Pp.(str "Cannot Declare ML Module while sections are opened.");
  let dune_compat_logpathroot = current_logpathroot () in
  Lib.add_leaf (inMLModule {mlocal=local; mnames=l;dune_compat_logpathroot});
  (* We can't put this in cache_function: it may declare other
     objects, and when the current module is required we want to run
     the ML-MODULE object before them. *)
  cache_ml_objects l

let print_ml_path () =
  let l = !coq_mlpath_copy in
  str"ML Load Path:" ++ fnl () ++ str"  " ++
          hv 0 (prlist_with_sep fnl str l)

(* Printing of loaded ML modules *)

let print_ml_modules () =
  let l = get_loaded_modules () in
  str"Loaded ML Modules: " ++ pr_vertical_list str (List.map snd l)

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
