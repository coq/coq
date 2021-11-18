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

(* If there is a toplevel under Coq *)
type toplevel = {
  load_obj : string -> unit;
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
  Nativelib.load_obj := toplevel.load_obj

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

let ml_load s =
  match !load with
  | WithTop t ->
     t.load_obj s
  | WithoutTop ->
     Fl_dynload.load_packages [s]

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

(** ml object = ml module or plugin *)

let init_ml_object mname =
  try String.Map.find mname !known_loaded_plugins ()
  with Not_found -> ()

let load_ml_object mname =
  ml_load mname;
  add_known_module mname;
  init_ml_object mname

let add_known_module m = add_known_module m

(* Summary of declared ML Modules *)

(* List and not String.Set because order is important: most recent first. *)

let loaded_modules = ref []
let get_loaded_modules () = List.rev !loaded_modules
let add_loaded_module md =
  if not (List.mem md !loaded_modules) then
    loaded_modules := md :: !loaded_modules
let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name =
  if not verb then f name
  else
    let info = str "[Loading ML file " ++ str name ++ str " ..." in
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

let trigger_ml_object verb cache reinit name =
  if module_is_known name then begin
    if reinit then init_ml_object name;
    add_loaded_module name;
    if cache then perform_cache_obj name
  end else if not has_dynlink then
    user_err
      (str "Dynamic link not supported (module " ++ str name ++ str ").")
  else begin
    if_verbose_load (verb && not !Flags.quiet) load_ml_object name;
    add_loaded_module name;
    if cache then perform_cache_obj name
  end

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter
    (fun name -> trigger_ml_object false false false name) x

let _ =
  Summary.declare_ml_modules_summary
    { Summary.freeze_function = (fun ~marshallable -> get_loaded_modules ());
      Summary.unfreeze_function = unfreeze_ml_modules;
      Summary.init_function = reset_loaded_modules }

(* Liboject entries of declared ML Modules *)

type ml_module_object = {
  mlocal : Vernacexpr.locality_flag;
  mnames : string list
}

let cache_ml_objects mnames =
  let iter obj = trigger_ml_object true true true obj in
  List.iter iter mnames

let load_ml_objects _ {mnames=mnames} =
  let iter obj = trigger_ml_object true false true obj in
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
  Lib.add_leaf (inMLModule {mlocal=local; mnames=l});
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
  str"Loaded ML Modules: " ++ pr_vertical_list str l

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
