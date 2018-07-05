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

open Names
open Libnames
open Lib
open Libobject

(************************************************************************)
(*s Low-level interning/externing of libraries to files *)

let raw_extern_library f =
  System.raw_extern_state Coq_config.vo_magic_number f

let raw_intern_library f =
  System.with_magic_number_check
    (System.raw_intern_state Coq_config.vo_magic_number) f

(************************************************************************)
(** Serialized objects loaded on-the-fly *)

exception Faulty of string

module Delayed :
sig

type 'a delayed
val in_delayed : string -> in_channel -> 'a delayed * Digest.t
val fetch_delayed : 'a delayed -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int;
  del_digest : Digest.t;
}

let in_delayed f ch =
  let pos = pos_in ch in
  let _, digest = System.skip_in_segment f ch in
  ({ del_file = f; del_digest = digest; del_off = pos; }, digest)

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let fetch_delayed del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  try
    let ch = raw_intern_library f in
    let () = seek_in ch pos in
    let obj, _, digest' = System.marshal_in_segment f ch in
    let () = close_in ch in
    if not (String.equal digest digest') then raise (Faulty f);
    obj
  with e when CErrors.noncritical e -> raise (Faulty f)

end

open Delayed


(************************************************************************)
(*s Modules on disk contain the following informations (after the magic
    number, and before the digest). *)

type compilation_unit_name = DirPath.t

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_objects : Declaremods.library_objects;
}

type summary_disk = {
  md_name : compilation_unit_name;
  md_imports : compilation_unit_name array;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
}

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_data : library_disk delayed;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_imports : compilation_unit_name array;
  library_digests : Safe_typing.vodigest;
  library_extra_univs : Univ.ContextSet.t;
}

type library_summary = {
  libsum_name : compilation_unit_name;
  libsum_digests : Safe_typing.vodigest;
  libsum_imports : compilation_unit_name array;
}

module LibraryOrdered = DirPath
module LibraryMap = Map.Make(LibraryOrdered)
module LibraryFilenameMap = Map.Make(LibraryOrdered)

(* This is a map from names to loaded libraries *)
let libraries_table : library_summary LibraryMap.t ref =
  Summary.ref LibraryMap.empty ~name:"LIBRARY"

(* This is the map of loaded libraries filename *)
(* (not synchronized so as not to be caught in the states on disk) *)
let libraries_filename_table = ref LibraryFilenameMap.empty

(* These are the _ordered_ sets of loaded, imported and exported libraries *)
let libraries_loaded_list = Summary.ref [] ~name:"LIBRARY-LOAD"
let libraries_imports_list = Summary.ref [] ~name:"LIBRARY-IMPORT"
let libraries_exports_list = Summary.ref [] ~name:"LIBRARY-EXPORT"

(* various requests to the tables *)

let find_library dir =
  LibraryMap.find dir !libraries_table

let try_find_library dir =
  try find_library dir
  with Not_found ->
    user_err ~hdr:"Library.find_library"
      (str "Unknown library " ++ DirPath.print dir)

let register_library_filename dir f =
  (* Not synchronized: overwrite the previous binding if one existed *)
  (* from a previous play of the session *)
  libraries_filename_table :=
    LibraryFilenameMap.add dir f !libraries_filename_table

let library_full_filename dir =
  try LibraryFilenameMap.find dir !libraries_filename_table
  with Not_found -> "<unavailable filename>"

let overwrite_library_filenames f =
  let f =
    if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  LibraryMap.iter (fun dir _ -> register_library_filename dir f)
    !libraries_table

let library_is_loaded dir =
  try let _ = find_library dir in true
  with Not_found -> false

let library_is_opened dir =
  List.exists (fun name -> DirPath.equal name dir) !libraries_imports_list

let loaded_libraries () = !libraries_loaded_list

let opened_libraries () = !libraries_imports_list

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  let libname = m.libsum_name in
  let link () =
    let dirname = Filename.dirname (library_full_filename libname) in
    let prefix = Nativecode.mod_uid_of_dirpath libname ^ "." in
    let f = prefix ^ "cmo" in
    let f = Dynlink.adapt_filename f in
    if Coq_config.native_compiler then
      Nativelib.link_library ~prefix ~dirname ~basename:f
  in
  let rec aux = function
    | [] -> link (); [libname]
    | m'::_ as l when DirPath.equal m' libname -> l
    | m'::l' -> m' :: aux l' in
  libraries_loaded_list := aux !libraries_loaded_list;
  libraries_table := LibraryMap.add libname m !libraries_table

  (* ... while if a library is imported/exported several time, then
     only the last occurrence is really needed - though the imported
     list may differ from the exported list (consider the sequence
     Export A; Export B; Import A which results in A;B for exports but
     in B;A for imports) *)

let rec remember_last_of_each l m =
  match l with
  | [] -> [m]
  | m'::l' when DirPath.equal m' m -> remember_last_of_each l' m
  | m'::l' -> m' :: remember_last_of_each l' m

let register_open_library export m =
  libraries_imports_list := remember_last_of_each !libraries_imports_list m;
  if export then
    libraries_exports_list := remember_last_of_each !libraries_exports_list m

(************************************************************************)
(*s Opening libraries *)

(* [open_library export explicit m] opens library [m] if not already
   opened _or_ if explicitly asked to be (re)opened *)

let open_library export explicit_libs m =
  if
    (* Only libraries indirectly to open are not reopen *)
    (* Libraries explicitly mentionned by the user are always reopen *)
    List.exists (fun m' -> DirPath.equal m m') explicit_libs
    || not (library_is_opened m)
  then begin
    register_open_library export m;
    Declaremods.really_import_module (MPfile m)
  end
  else
    if export then
      libraries_exports_list := remember_last_of_each !libraries_exports_list m

(* open_libraries recursively open a list of libraries but opens only once
   a library that is re-exported many times *)

let open_libraries export modl =
  let to_open_list =
    List.fold_left
      (fun l m ->
         let subimport =
           Array.fold_left
             (fun l m -> remember_last_of_each l m)
             l m.libsum_imports
         in remember_last_of_each subimport m.libsum_name)
      [] modl in
  let explicit = List.map (fun m -> m.libsum_name) modl in
  List.iter (open_library export explicit) to_open_list


(**********************************************************************)
(* import and export of libraries - synchronous operations            *)
(* at the end similar to import and export of modules except that it  *)
(* is optimized: when importing several libraries at the same time    *)
(* which themselves indirectly imports the very same modules, these   *)
(* ones are imported only ones *)

let open_import_library i (_,(modl,export)) =
  if Int.equal i 1 then
    (* even if the library is already imported, we re-import it *)
    (* if not (library_is_opened dir) then *)
      open_libraries export (List.map try_find_library modl)

let cache_import_library obj =
  open_import_library 1 obj

let subst_import_library (_,o) = o

let classify_import_library (_,export as obj) =
  if export then Substitute obj else Dispose

let in_import_library : DirPath.t list * bool -> obj =
  declare_object {(default_object "IMPORT LIBRARY") with
       cache_function = cache_import_library;
       open_function = open_import_library;
       subst_function = subst_import_library;
       classify_function = classify_import_library }


(************************************************************************)
(*s Locate absolute or partially qualified library names in the path *)

exception LibUnmappedDir
exception LibNotFound
type library_location = LibLoaded | LibInPath

let warn_several_object_files =
  CWarnings.create ~name:"several-object-files" ~category:"require"
         (fun (vi, vo) -> str"Loading" ++ spc () ++ str vi ++
                            strbrk " instead of " ++ str vo ++
                            strbrk " because it is more recent")

let locate_absolute_library dir =
  (* Search in loadpath *)
  let pref, base = split_dirpath dir in
  let loadpath = Loadpath.filter_path (fun dir -> DirPath.equal dir pref) in
  let () = match loadpath with [] -> raise LibUnmappedDir | _ -> () in
  let loadpath = List.map fst loadpath in
  let find ext =
    try
      let name = Id.to_string base ^ ext in
      let _, file = System.where_in_path ~warn:false loadpath name in
      Some file
    with Not_found -> None in
  match find ".vo", find ".vio" with
  | None, None -> raise LibNotFound
  | Some file, None | None, Some file -> file
  | Some vo, Some vi when Unix.((stat vo).st_mtime < (stat vi).st_mtime) ->
    warn_several_object_files (vi, vo);
    vi
  | Some vo, Some _ -> vo

let locate_qualified_library ?root ?(warn = true) qid =
  (* Search library in loadpath *)
  let dir, base = repr_qualid qid in
  let loadpath = Loadpath.expand_path ?root dir in
  let () = match loadpath with [] -> raise LibUnmappedDir | _ -> () in
  let find ext =
    try
      let name = Id.to_string base ^ ext in
      let lpath, file =
        System.where_in_path ~warn (List.map fst loadpath) name in
      Some (lpath, file)
    with Not_found -> None in
  let lpath, file =
    match find ".vo", find ".vio" with
    | None, None -> raise LibNotFound
    | Some res, None | None, Some res -> res
    | Some (_, vo), Some (_, vi as resvi)
      when Unix.((stat vo).st_mtime < (stat vi).st_mtime) ->
      warn_several_object_files (vi, vo);
       resvi
    | Some resvo, Some _ -> resvo
  in
  let dir = add_dirpath_suffix (String.List.assoc lpath loadpath) base in
  (* Look if loaded *)
  if library_is_loaded dir then (LibLoaded, dir,library_full_filename dir)
  (* Otherwise, look for it in the file system *)
  else (LibInPath, dir, file)

let error_unmapped_dir qid =
  let prefix, _ = repr_qualid qid in
  user_err ~hdr:"load_absolute_library_from"
    (str "Cannot load " ++ pr_qualid qid ++ str ":" ++ spc () ++
     str "no physical path bound to" ++ spc () ++ DirPath.print prefix ++ fnl ())

let error_lib_not_found qid =
  user_err ~hdr:"load_absolute_library_from"
    (str"Cannot find library " ++ pr_qualid qid ++ str" in loadpath")

let try_locate_absolute_library dir =
  try
    locate_absolute_library dir
  with
    | LibUnmappedDir -> error_unmapped_dir (qualid_of_dirpath dir)
    | LibNotFound -> error_lib_not_found (qualid_of_dirpath dir)

(************************************************************************)
(** {6 Tables of opaque proof terms} *)

(** We now store opaque proof terms apart from the rest of the environment.
    See the [Indirect] contructor in [Lazyconstr.lazy_constr]. This way,
    we can quickly load a first half of a .vo file without these opaque
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

(** Delayed / available tables of opaque terms *)

type 'a table_status =
  | ToFetch of 'a Future.computation array delayed
  | Fetched of 'a Future.computation array

let opaque_tables =
  ref (LibraryMap.empty : (Constr.constr table_status) LibraryMap.t)
let univ_tables =
  ref (LibraryMap.empty : (Univ.ContextSet.t table_status) LibraryMap.t)

let add_opaque_table dp st =
  opaque_tables := LibraryMap.add dp st !opaque_tables
let add_univ_table dp st =
  univ_tables := LibraryMap.add dp st !univ_tables

let access_table what tables dp i =
  let t = match LibraryMap.find dp !tables with
    | Fetched t -> t
    | ToFetch f ->
      let dir_path = Names.DirPath.to_string dp in
      Flags.if_verbose Feedback.msg_info (str"Fetching " ++ str what++str" from disk for " ++ str dir_path);
      let t =
        try fetch_delayed f
        with Faulty f ->
          user_err ~hdr:"Library.access_table"
            (str "The file " ++ str f ++ str " (bound to " ++ str dir_path ++
             str ") is inaccessible or corrupted,\ncannot load some " ++
             str what ++ str " in it.\n")
      in
      tables := LibraryMap.add dp (Fetched t) !tables;
      t
  in
  assert (i < Array.length t); t.(i)

let access_opaque_table dp i =
  let what = "opaque proofs" in
  access_table what opaque_tables dp i

let access_univ_table dp i =
  try
    let what = "universe contexts of opaque proofs" in
    Some (access_table what univ_tables dp i)
  with Not_found -> None

let () =
  Opaqueproof.set_indirect_opaque_accessor access_opaque_table;
  Opaqueproof.set_indirect_univ_accessor access_univ_table

(************************************************************************)
(* Internalise libraries *)

type seg_sum = summary_disk
type seg_lib = library_disk
type seg_univ = (* true = vivo, false = vi *)
  Univ.ContextSet.t Future.computation array * Univ.ContextSet.t * bool
type seg_discharge = Opaqueproof.cooking_info list array
type seg_proofs = Constr.constr Future.computation array

let mk_library sd md digests univs =
  {
    library_name     = sd.md_name;
    library_data     = md;
    library_deps     = sd.md_deps;
    library_imports  = sd.md_imports;
    library_digests  = digests;
    library_extra_univs = univs;
  }

let mk_summary m = {
  libsum_name = m.library_name;
  libsum_imports = m.library_imports;
  libsum_digests = m.library_digests;
}

let intern_from_file f =
  let ch = raw_intern_library f in
  let (lsd : seg_sum), _, digest_lsd = System.marshal_in_segment f ch in
  let ((lmd : seg_lib delayed), digest_lmd) = in_delayed f ch in
  let (univs : seg_univ option), _, digest_u = System.marshal_in_segment f ch in
  let _ = System.skip_in_segment f ch in
  let _ = System.skip_in_segment f ch in
  let ((del_opaque : seg_proofs delayed),_) = in_delayed f ch in
  close_in ch;
  register_library_filename lsd.md_name f;
  add_opaque_table lsd.md_name (ToFetch del_opaque);
  let open Safe_typing in
  match univs with
  | None -> mk_library lsd lmd (Dvo_or_vi digest_lmd) Univ.ContextSet.empty
  | Some (utab,uall,true) ->
      add_univ_table lsd.md_name (Fetched utab);
      mk_library lsd lmd (Dvivo (digest_lmd,digest_u)) uall
  | Some (utab,_,false) ->
      add_univ_table lsd.md_name (Fetched utab);
      mk_library lsd lmd (Dvo_or_vi digest_lmd) Univ.ContextSet.empty

module DPMap = Map.Make(DirPath)

let rec intern_library (needed, contents) (dir, f) from =
  (* Look if in the current logical environment *)
  try (find_library dir).libsum_digests, (needed, contents)
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  try (DPMap.find dir contents).library_digests, (needed, contents)
  with Not_found ->
  Feedback.feedback(Feedback.FileDependency (from, DirPath.to_string dir));
  (* [dir] is an absolute name which matches [f] which must be in loadpath *)
  let f = match f with Some f -> f | None -> try_locate_absolute_library dir in
  let m = intern_from_file f in
  if not (DirPath.equal dir m.library_name) then
    user_err ~hdr:"load_physical_library"
      (str "The file " ++ str f ++ str " contains library" ++ spc () ++
       DirPath.print m.library_name ++ spc () ++ str "and not library" ++
       spc() ++ DirPath.print dir);
  Feedback.feedback (Feedback.FileLoaded(DirPath.to_string dir, f));
  m.library_digests, intern_library_deps (needed, contents) dir m f

and intern_library_deps libs dir m from =
  let needed, contents = Array.fold_left (intern_mandatory_library dir from) libs m.library_deps in
  (dir :: needed, DPMap.add dir m contents )

and intern_mandatory_library caller from libs (dir,d) =
  let digest, libs = intern_library libs (dir, None) (Some from) in
  if not (Safe_typing.digest_match ~actual:digest ~required:d) then
    user_err (str "Compiled library " ++ DirPath.print caller ++
    str " (in file " ++ str from ++ str ") makes inconsistent assumptions \
    over library " ++ DirPath.print dir);
  libs

let rec_intern_library libs (dir, f) =
  let _, libs = intern_library libs (dir, Some f) None in
  libs

let native_name_from_filename f =
  let ch = raw_intern_library f in
  let (lmd : seg_sum), pos, digest_lmd = System.marshal_in_segment f ch in
  Nativecode.mod_uid_of_dirpath lmd.md_name

(**********************************************************************)
(*s [require_library] loads and possibly opens a library. This is a
    synchronized operation. It is performed as follows:

  preparation phase: (functions require_library* ) the library and its
    dependencies are read from to disk (using intern_* )
    [they are read from disk to ensure that at section/module
     discharging time, the physical library referred to outside the
     section/module is the one that was used at type-checking time in
     the section/module]

  execution phase: (through add_leaf and cache_require)
    the library is loaded in the environment and Nametab, the objects are
    registered etc, using functions from Declaremods (via load_library,
    which recursively loads its dependencies)
*)

let register_library m =
  let l = fetch_delayed m.library_data in
  Declaremods.register_library
    m.library_name
    l.md_compiled
    l.md_objects
    m.library_digests
    m.library_extra_univs;
  register_loaded_library (mk_summary m)

(* Follow the semantics of Anticipate object:
   - called at module or module type closing when a Require occurs in
     the module or module type
   - not called from a library (i.e. a module identified with a file) *)
let load_require _ (_,(needed,modl,_)) =
  List.iter register_library needed

let open_require i (_,(_,modl,export)) =
  Option.iter (fun exp -> open_libraries exp (List.map find_library modl))
    export

  (* [needed] is the ordered list of libraries not already loaded *)
let cache_require o =
  load_require 1 o;
  open_require 1 o

let discharge_require (_,o) = Some o

(* open_function is never called from here because an Anticipate object *)

type require_obj = library_t list * DirPath.t list * bool option

let in_require : require_obj -> obj =
  declare_object {(default_object "REQUIRE") with
       cache_function = cache_require;
       load_function = load_require;
       open_function = (fun _ _ -> assert false);
       discharge_function = discharge_require;
       classify_function = (fun o -> Anticipate o) }

(* Require libraries, import them if [export <> None], mark them for export
   if [export = Some true] *)

let warn_require_in_module =
  CWarnings.create ~name:"require-in-module" ~category:"deprecated"
                   (fun () -> strbrk "Require inside a module is" ++
                              strbrk " deprecated and strongly discouraged. " ++
                              strbrk "You can Require a module at toplevel " ++
                              strbrk "and optionally Import it inside another one.")

let require_library_from_dirpath modrefl export =
  let needed, contents = List.fold_left rec_intern_library ([], DPMap.empty) modrefl in
  let needed = List.rev_map (fun dir -> DPMap.find dir contents) needed in
  let modrefl = List.map fst modrefl in
    if Lib.is_module_or_modtype () then
      begin
        warn_require_in_module ();
	add_anonymous_leaf (in_require (needed,modrefl,None));
	Option.iter (fun exp ->
	  add_anonymous_leaf (in_import_library (modrefl,exp)))
	  export
      end
    else
      add_anonymous_leaf (in_require (needed,modrefl,export));
  ()

(* the function called by Vernacentries.vernac_import *)

let safe_locate_module qid =
  try Nametab.locate_module qid
  with Not_found ->
    user_err ?loc:qid.CAst.loc ~hdr:"import_library"
      (pr_qualid qid ++ str " is not a module")

let import_module export modl =
  (* Optimization: libraries in a raw in the list are imported
     "globally".  If there is non-library in the list; it breaks the
     optimization For instance: "Import Arith MyModule Zarith" will
     not be optimized (possibly resulting in redefinitions, but
     "Import MyModule Arith Zarith" and "Import Arith Zarith MyModule"
     will have the submodules imported by both Arith and ZArith
     imported only once *)
  let flush = function
    | [] -> ()
    | modl -> add_anonymous_leaf (in_import_library (List.rev modl, export)) in
  let rec aux acc = function
    | qid :: l ->
        let m,acc =
          try Nametab.locate_module qid, acc
          with Not_found-> flush acc; safe_locate_module qid, [] in
        (match m with
        | MPfile dir -> aux (dir::acc) l
        | mp ->
            flush acc;
            try Declaremods.import_module export mp; aux [] l
            with Not_found ->
              user_err ?loc:qid.CAst.loc ~hdr:"import_library"
                (pr_qualid qid ++ str " is not a module"))
    | [] -> flush acc
  in aux [] modl

(************************************************************************)
(*s Initializing the compilation of a library. *)

let check_coq_overwriting p id =
  let l = DirPath.repr p in
  let is_empty = match l with [] -> true | _ -> false in
  if not !Flags.boot && not is_empty && Id.equal (List.last l) coq_root then
    user_err 
      (str "Cannot build module " ++ DirPath.print p ++ str "." ++ Id.print id ++ str "." ++ spc () ++
      str "it starts with prefix \"Coq\" which is reserved for the Coq library.")

let start_library fo =
  let ldir0 =
    try
      let lp = Loadpath.find_load_path (Filename.dirname fo) in
      Loadpath.logical lp
    with Not_found -> Libnames.default_root_prefix
  in
  let file = Filename.chop_extension (Filename.basename fo) in
  let id = Id.of_string file in
  check_coq_overwriting ldir0 id;
  let ldir = add_dirpath_suffix ldir0 id in
  Declaremods.start_library ldir;
  ldir

let load_library_todo f =
  let longf = Loadpath.locate_file (f^".v") in
  let f = longf^"io" in
  let ch = raw_intern_library f in
  let (s0 : seg_sum), _, _ = System.marshal_in_segment f ch in
  let (s1 : seg_lib), _, _ = System.marshal_in_segment f ch in
  let (s2 : seg_univ option), _, _ = System.marshal_in_segment f ch in
  let (s3 : seg_discharge option), _, _ = System.marshal_in_segment f ch in
  let tasks, _, _ = System.marshal_in_segment f ch in
  let (s5 : seg_proofs), _, _ = System.marshal_in_segment f ch in
  close_in ch;
  if tasks = None then user_err ~hdr:"restart" (str"not a .vio file");
  if s2 = None then user_err ~hdr:"restart" (str"not a .vio file");
  if s3 = None then user_err ~hdr:"restart" (str"not a .vio file");
  if pi3 (Option.get s2) then user_err ~hdr:"restart" (str"not a .vio file");
  longf, s0, s1, Option.get s2, Option.get s3, Option.get tasks, s5

(************************************************************************)
(*s [save_library dir] ends library [dir] and save it to the disk. *)

let current_deps () =
  let map name =
    let m = try_find_library name in
    (name, m.libsum_digests)
  in
  List.map map !libraries_loaded_list

let current_reexports () = !libraries_exports_list

let error_recursively_dependent_library dir =
  user_err 
    (strbrk "Unable to use logical name " ++ DirPath.print dir ++
     strbrk " to save current library because" ++
     strbrk " it already depends on a library of this name.")

(* We now use two different digests in a .vo file. The first one
   only covers half of the file, without the opaque table. It is
   used for identifying this version of this library : this digest
   is the one leading to "inconsistent assumptions" messages.
   The other digest comes at the very end, and covers everything
   before it. This one is used for integrity check of the whole
   file when loading the opaque table. *)

(* Security weakness: file might have been changed on disk between
   writing the content and computing the checksum... *)

let save_library_to ?todo dir f otab =
  let except = match todo with
    | None ->
        (* XXX *)
        (* assert(!Flags.compilation_mode = Flags.BuildVo); *)
        assert(Filename.check_suffix f ".vo");
        Future.UUIDSet.empty
    | Some (l,_) ->
        assert(Filename.check_suffix f ".vio");
        List.fold_left (fun e (r,_) -> Future.UUIDSet.add r.Stateid.uuid e)
          Future.UUIDSet.empty l in
  let cenv, seg, ast = Declaremods.end_library ~except dir in
  let opaque_table, univ_table, disch_table, f2t_map = Opaqueproof.dump otab in
  let tasks, utab, dtab =
    match todo with
    | None -> None, None, None
    | Some (tasks, rcbackup) ->
        let tasks =
          List.map Stateid.(fun (r,b) ->
            try { r with uuid = Future.UUIDMap.find r.uuid f2t_map }, b
            with Not_found -> assert b; { r with uuid = -1 }, b)
          tasks in
        Some (tasks,rcbackup),
        Some (univ_table,Univ.ContextSet.empty,false),
        Some disch_table in
  let except =
    Future.UUIDSet.fold (fun uuid acc ->
      try Int.Set.add (Future.UUIDMap.find uuid f2t_map) acc
      with Not_found -> acc)
      except Int.Set.empty in
  let is_done_or_todo i x = Future.is_val x || Int.Set.mem i except in
  Array.iteri (fun i x ->
    if not(is_done_or_todo i x) then CErrors.user_err ~hdr:"library"
      Pp.(str"Proof object "++int i++str" is not checked nor to be checked"))
    opaque_table;
  let sd = {
    md_name = dir;
    md_deps = Array.of_list (current_deps ());
    md_imports = Array.of_list (current_reexports ());
  } in
  let md = {
    md_compiled = cenv;
    md_objects = seg;
  } in
  if Array.exists (fun (d,_) -> DirPath.equal d dir) sd.md_deps then
    error_recursively_dependent_library dir;
  (* Open the vo file and write the magic number *)
  let f' = f in
  let ch = raw_extern_library f' in
  try
    (* Writing vo payload *)
    System.marshal_out_segment f' ch (sd           : seg_sum);
    System.marshal_out_segment f' ch (md           : seg_lib);
    System.marshal_out_segment f' ch (utab         : seg_univ option);
    System.marshal_out_segment f' ch (dtab         : seg_discharge option);
    System.marshal_out_segment f' ch (tasks        : 'tasks option);
    System.marshal_out_segment f' ch (opaque_table : seg_proofs);
    close_out ch;
    (* Writing native code files *)
    if !Flags.output_native_objects then
      let fn = Filename.dirname f'^"/"^Nativecode.mod_uid_of_dirpath dir in
      if not (Nativelib.compile_library dir ast fn) then
	user_err Pp.(str "Could not compile the library to native code.")
   with reraise ->
    let reraise = CErrors.push reraise in
    let () = Feedback.msg_warning (str "Removed file " ++ str f') in
    let () = close_out ch in
    let () = Sys.remove f' in
    iraise reraise

let save_library_raw f sum lib univs proofs =
  let f' = f^"o" in
  let ch = raw_extern_library f' in
  System.marshal_out_segment f' ch (sum        : seg_sum);
  System.marshal_out_segment f' ch (lib        : seg_lib);
  System.marshal_out_segment f' ch (Some univs : seg_univ option);
  System.marshal_out_segment f' ch (None       : seg_discharge option);
  System.marshal_out_segment f' ch (None       : 'tasks option);
  System.marshal_out_segment f' ch (proofs     : seg_proofs);
  close_out ch

module StringOrd = struct type t = string let compare = String.compare end
module StringSet = Set.Make(StringOrd)

let get_used_load_paths () =
  StringSet.elements
    (List.fold_left (fun acc m -> StringSet.add
      (Filename.dirname (library_full_filename m)) acc)
       StringSet.empty !libraries_loaded_list)

let _ = Nativelib.get_load_paths := get_used_load_paths
