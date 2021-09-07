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
open System

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


(* NB: this module relies on OCaml's Dynlink library. The bytecode version
   of Dynlink is always available, but there are some architectures
   with native compilation and no dynlink.cmxa. Instead of nasty IFDEF's
   here for hiding the calls to Dynlink, we now simply reject this rather
   rare situation during ./configure, and give instructions there about how
   to build a dummy dynlink.cmxa, cf. dev/dynlink.ml. *)

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
    | Dynlink.Error e ->
      Some (hov 0 (str "Dynlink error: " ++ str Dynlink.(error_message e)))
    | _ ->
      None
  )

let ml_load s =
  (match !load with
   | WithTop t ->
     t.load_obj s
   | WithoutTop ->
     Dynlink.loadfile s
  );
  s

let dir_ml_load s =
  match !load with
    | WithTop _ -> ml_load s
    | WithoutTop ->
        let warn = not !Flags.quiet in
        let _,gname = find_file_in_path ~warn !coq_mlpath_copy s in
        ml_load gname

(* Adds a path to the ML paths *)
let add_ml_dir s =
  match !load with
    | WithTop t -> t.add_dir s; keep_copy_mlpath s
    | WithoutTop when has_dynlink -> keep_copy_mlpath s
    | _ -> ()

(* convertit un nom quelconque en nom de fichier ou de module *)
let mod_of_name name =
    if Filename.check_suffix name ".cmo" then
      Filename.chop_suffix name ".cmo"
    else
      name

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
    user_err ~hdr:"Mltop.load_object"
      (str"File not found on loadpath : " ++ str s ++ str"\n" ++
       str"Loadpath: " ++ str(String.concat ":" !coq_mlpath_copy)) in
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
    if is_in_path !coq_mlpath_copy name then name else fail name
  else
    let (full, base) = match suffix with
      | Some ".cmo" | Some ".cma" -> true, name
      | Some ".cmxs" -> false, Filename.chop_suffix name ".cmxs"
      | _ -> false, name
    in
    if full then
      if is_in_path !coq_mlpath_copy base then base else fail base
    else
      let name = base ^ ".cma" in
      if is_in_path !coq_mlpath_copy name then name else
        let name = base ^ ".cmo" in
        if is_in_path !coq_mlpath_copy name then name else
          fail (base ^ ".cm[ao]")

(** Is the ML code of the standard library placed into loadable plugins
    or statically compiled into coqtop ? For the moment this choice is
    made according to the presence of native dynlink : even if bytecode
    coqtop could always load plugins, we prefer to have uniformity between
    bytecode and native versions. *)

(* [known_loaded_module] contains the names of the loaded ML modules
 * (linked or loaded with load_object). It is used not to load a
 * module twice. It is NOT the list of ML modules Coq knows. *)

let known_loaded_modules = ref String.Map.empty

let add_known_module mname path =
  if not (String.Map.mem mname !known_loaded_modules) ||
     String.Map.find mname !known_loaded_modules = None then
    known_loaded_modules := String.Map.add mname path !known_loaded_modules

let module_is_known mname =
  String.Map.mem mname !known_loaded_modules

let known_module_path mname =
  String.Map.find mname !known_loaded_modules

(** A plugin is just an ML module with an initialization function. *)

let known_loaded_plugins = ref String.Map.empty

let add_known_plugin init name =
  add_known_module name None;
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

let load_ml_object mname ?path fname=
  let path = match path with
    | None -> dir_ml_load fname
    | Some p -> ml_load p in
  add_known_module mname (Some path);
  init_ml_object mname;
  path

let add_known_module m = add_known_module m None

(* Summary of declared ML Modules *)

(* List and not String.Set because order is important: most recent first. *)

let loaded_modules = ref []
let get_loaded_modules () = List.rev !loaded_modules
let add_loaded_module md path =
  if not (List.mem_assoc md !loaded_modules) then
    loaded_modules := (md,path) :: !loaded_modules
let reset_loaded_modules () = loaded_modules := []

let if_verbose_load verb f name ?path fname =
  if not verb then f name ?path fname
  else
    let info = str "[Loading ML file " ++ str fname ++ str " ..." in
    try
      let path = f name ?path fname in
      Feedback.msg_info (info ++ str " done]");
      path
    with reraise ->
      Feedback.msg_info (info ++ str " failed]");
      raise reraise

(** Load a module for the first time (i.e. dynlink it)
    or simulate its reload (i.e. doing nothing except maybe
    an initialization function). *)

let trigger_ml_object verb cache reinit ?path name =
  if module_is_known name then begin
    if reinit then init_ml_object name;
    add_loaded_module name (known_module_path name);
    if cache then perform_cache_obj name
  end else if not has_dynlink then
    user_err ~hdr:"Mltop.trigger_ml_object"
      (str "Dynamic link not supported (module " ++ str name ++ str ")")
  else begin
    let file = file_of_name (Option.default name path) in
    let path =
      if_verbose_load (verb && not !Flags.quiet) load_ml_object name ?path file in
    add_loaded_module name (Some path);
    if cache then perform_cache_obj name
  end

let unfreeze_ml_modules x =
  reset_loaded_modules ();
  List.iter
    (fun (name,path) -> trigger_ml_object false false false ?path name) x

let _ =
  Summary.declare_ml_modules_summary
    { Summary.freeze_function = (fun ~marshallable -> get_loaded_modules ());
      Summary.unfreeze_function = unfreeze_ml_modules;
      Summary.init_function = reset_loaded_modules }

(* Liboject entries of declared ML Modules *)

(* Digest of module used to compile the file *)
type ml_module_digest =
  | NoDigest
  | AnyDigest of Digest.t             (* digest of any used cma / cmxa *)

type ml_module_object = {
  mlocal : Vernacexpr.locality_flag;
  mnames : (string * ml_module_digest) list
}

let add_module_digest m =
  if not has_dynlink then
    m, NoDigest
  else
  try
    let file = file_of_name m in
    let path, file = System.where_in_path ~warn:false !coq_mlpath_copy file in
    m, AnyDigest (Digest.file file)
  with
  | Not_found ->
    m, NoDigest

let cache_ml_objects (_,{mnames=mnames}) =
  let iter (obj, _) = trigger_ml_object true true true obj in
  List.iter iter mnames

let load_ml_objects _ (_,{mnames=mnames}) =
  let iter (obj, _) = trigger_ml_object true false true obj in
  List.iter iter mnames

let classify_ml_objects ({mlocal=mlocal} as o) =
  if mlocal then Libobject.Dispose else Libobject.Substitute o

let inMLModule : ml_module_object -> Libobject.obj =
  let open Libobject in
  declare_object
    {(default_object "ML-MODULE") with
      cache_function = cache_ml_objects;
      load_function = load_ml_objects;
      subst_function = (fun (_,o) -> o);
      classify_function = classify_ml_objects }

let declare_ml_modules local l =
  let l = List.map mod_of_name l in
  let l = List.map add_module_digest l in
  Lib.add_anonymous_leaf ~cache_first:false (inMLModule {mlocal=local; mnames=l})

let print_ml_path () =
  let l = !coq_mlpath_copy in
  str"ML Load Path:" ++ fnl () ++ str"  " ++
          hv 0 (prlist_with_sep fnl str l)

(* Printing of loaded ML modules *)

let print_ml_modules () =
  let l = get_loaded_modules () in
  str"Loaded ML Modules: " ++ pr_vertical_list str (List.map fst l)

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
