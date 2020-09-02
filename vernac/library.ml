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

open Names
open Lib
open Libobject

(************************************************************************)
(*s Low-level interning/externing of libraries to files *)

let raw_extern_library f =
  ObjFile.open_out ~file:f

let raw_intern_library f =
  System.with_magic_number_check
    (fun file -> ObjFile.open_in ~file) f

(************************************************************************)
(** Serialized objects loaded on-the-fly *)

exception Faulty of string

module Delayed :
sig

type 'a delayed
val in_delayed : string -> segment:ObjFile.segment -> 'a delayed * Digest.t
val fetch_delayed : 'a delayed -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int64;
  del_digest : Digest.t;
}

let in_delayed f ~segment =
  let digest = segment.ObjFile.hash in
  { del_file = f; del_digest = digest; del_off = segment.ObjFile.pos; }, digest

(** Fetching a table of opaque terms at position [pos] in file [f],
    expecting to find first a copy of [digest]. *)

let fetch_delayed del =
  let { del_digest = digest; del_file = f; del_off = pos; } = del in
  let ch = open_in_bin f in
  let obj, digest' =
    try
      let () = LargeFile.seek_in ch pos in
      let obj = System.marshal_in f ch in
      let digest' = Digest.input ch in
      obj, digest'
    with e -> close_in ch; raise e
  in
  close_in ch;
  if not (String.equal digest digest') then raise (Faulty f);
  obj

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
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
}

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_data : library_disk;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digests : Safe_typing.vodigest;
  library_extra_univs : Univ.ContextSet.t;
}

type library_summary = {
  libsum_name : compilation_unit_name;
  libsum_digests : Safe_typing.vodigest;
}

(* This is a map from names to loaded libraries *)
let libraries_table : library_summary DPmap.t ref =
  Summary.ref DPmap.empty ~name:"LIBRARY"

(* This is the map of loaded libraries filename *)
(* (not synchronized so as not to be caught in the states on disk) *)
let libraries_filename_table = ref DPmap.empty

(* These are the _ordered_ sets of loaded, imported and exported libraries *)
let libraries_loaded_list = Summary.ref [] ~name:"LIBRARY-LOAD"

(* various requests to the tables *)

let find_library dir =
  DPmap.find dir !libraries_table

let try_find_library dir =
  try find_library dir
  with Not_found ->
    user_err ~hdr:"Library.find_library"
      (str "Unknown library " ++ DirPath.print dir)

let register_library_filename dir f =
  (* Not synchronized: overwrite the previous binding if one existed *)
  (* from a previous play of the session *)
  libraries_filename_table :=
    DPmap.add dir f !libraries_filename_table

let library_full_filename dir =
  try DPmap.find dir !libraries_filename_table
  with Not_found -> "<unavailable filename>"

let overwrite_library_filenames f =
  let f =
    if Filename.is_relative f then Filename.concat (Sys.getcwd ()) f else f in
  DPmap.iter (fun dir _ -> register_library_filename dir f)
    !libraries_table

let library_is_loaded dir =
  try let _ = find_library dir in true
  with Not_found -> false

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library m =
  let libname = m.libsum_name in
  let link () =
    let dirname = Filename.dirname (library_full_filename libname) in
    let prefix = Nativecode.mod_uid_of_dirpath libname ^ "." in
    let f = prefix ^ "cmo" in
    let f = Dynlink.adapt_filename f in
    Nativelib.link_library (Global.env()) ~prefix ~dirname ~basename:f
  in
  let rec aux = function
    | [] ->
      let () = if Flags.get_native_compiler () then link () in
      [libname]
    | m'::_ as l when DirPath.equal m' libname -> l
    | m'::l' -> m' :: aux l' in
  libraries_loaded_list := aux !libraries_loaded_list;
  libraries_table := DPmap.add libname m !libraries_table

  let loaded_libraries () = !libraries_loaded_list

(************************************************************************)
(** {6 Tables of opaque proof terms} *)

(** We now store opaque proof terms apart from the rest of the environment.
    See the [Indirect] constructor in [Lazyconstr.lazy_constr]. This way,
    we can quickly load a first half of a .vo file without these opaque
    terms, and access them only when a specific command (e.g. Print or
    Print Assumptions) needs it. *)

(** Delayed / available tables of opaque terms *)

let opaque_tables =
  ref (DPmap.empty : Opaqueproof.opaque_proofterm delayed Int.Map.t DPmap.t)

let get_opaque_segment name = match CString.split_on_char '/' name with
| ["opaques"; n] ->
  (try let n = int_of_string n in Some n with _ -> None)
| _ -> None

let add_opaque_table dp (f, segments) =
  let fold name segment accu = match get_opaque_segment name with
  | Some n ->
    let (d, _) = in_delayed f ~segment in
    Int.Map.add n d accu
  | None -> accu
  in
  let opaques = CString.Map.fold fold segments Int.Map.empty in
  opaque_tables := DPmap.add dp opaques !opaque_tables

let access_opaque_table dp i =
  let f = Int.Map.find i (DPmap.find dp !opaque_tables) in
  let dir_path = Names.DirPath.to_string dp in
  Flags.if_verbose Feedback.msg_info (str"Fetching opaque proofs from disk for " ++ str dir_path);
  let v =
    try fetch_delayed f
    with Faulty f ->
      user_err ~hdr:"Library.access_table"
        (str "The file " ++ str f ++ str " (bound to " ++ str dir_path ++
          str ") is inaccessible or corrupted,\ncannot load some opaque proofs in it.\n")
  in
  Some v

let indirect_accessor = {
  Opaqueproof.access_proof = access_opaque_table;
  Opaqueproof.access_discharge = Cooking.cook_constr;
}

(************************************************************************)
(* Internalise libraries *)

type seg_sum = summary_disk
type seg_lib = library_disk
type seg_univ = (* true = vivo, false = vi *)
  Univ.ContextSet.t * bool
type seg_proofs = Opaqueproof.opaque_proofterm option array

let mk_library sd md digests univs =
  {
    library_name     = sd.md_name;
    library_data     = md;
    library_deps     = sd.md_deps;
    library_digests  = digests;
    library_extra_univs = univs;
  }

let mk_summary m = {
  libsum_name = m.library_name;
  libsum_digests = m.library_digests;
}

let intern_from_file f =
  let ch = raw_intern_library f in
  let segments = ObjFile.segments ch in
  let (lsd : seg_sum), digest_lsd = ObjFile.marshal_in_segment ch ~segment:"summary" in
  let ((lmd : seg_lib), digest_lmd) = ObjFile.marshal_in_segment ch ~segment:"library" in
  let (univs : seg_univ option), digest_u = ObjFile.marshal_in_segment ch ~segment:"universes" in
  ObjFile.close_in ch;
  System.check_caml_version ~caml:lsd.md_ocaml ~file:f;
  register_library_filename lsd.md_name f;
  add_opaque_table lsd.md_name (f, segments);
  let open Safe_typing in
  match univs with
  | None -> mk_library lsd lmd (Dvo_or_vi digest_lmd) Univ.ContextSet.empty
  | Some (uall,true) ->
      mk_library lsd lmd (Dvivo (digest_lmd,digest_u)) uall
  | Some (_,false) ->
      mk_library lsd lmd (Dvo_or_vi digest_lmd) Univ.ContextSet.empty

let rec intern_library ~lib_resolver (needed, contents) (dir, f) from =
  (* Look if in the current logical environment *)
  try (find_library dir).libsum_digests, (needed, contents)
  with Not_found ->
  (* Look if already listed and consequently its dependencies too *)
  try (DPmap.find dir contents).library_digests, (needed, contents)
  with Not_found ->
  Feedback.feedback(Feedback.FileDependency (from, DirPath.to_string dir));
  (* [dir] is an absolute name which matches [f] which must be in loadpath *)
  let f = match f with Some f -> f | None -> lib_resolver dir in
  let m = intern_from_file f in
  if not (DirPath.equal dir m.library_name) then
    user_err ~hdr:"load_physical_library"
      (str "The file " ++ str f ++ str " contains library" ++ spc () ++
       DirPath.print m.library_name ++ spc () ++ str "and not library" ++
       spc() ++ DirPath.print dir);
  Feedback.feedback (Feedback.FileLoaded(DirPath.to_string dir, f));
  m.library_digests, intern_library_deps ~lib_resolver (needed, contents) dir m f

and intern_library_deps ~lib_resolver libs dir m from =
  let needed, contents =
    Array.fold_left (intern_mandatory_library ~lib_resolver dir from)
      libs m.library_deps in
  (dir :: needed, DPmap.add dir m contents )

and intern_mandatory_library ~lib_resolver caller from libs (dir,d) =
  let digest, libs = intern_library ~lib_resolver libs (dir, None) (Some from) in
  if not (Safe_typing.digest_match ~actual:digest ~required:d) then
    user_err (str "Compiled library " ++ DirPath.print caller ++
    str " (in file " ++ str from ++ str ") makes inconsistent assumptions \
    over library " ++ DirPath.print dir);
  libs

let rec_intern_library ~lib_resolver libs (dir, f) =
  let _, libs = intern_library ~lib_resolver libs (dir, Some f) None in
  libs

let native_name_from_filename f =
  let ch = raw_intern_library f in
  let (lmd : seg_sum), digest_lmd = ObjFile.marshal_in_segment ch ~segment:"summary" in
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
  let l = m.library_data in
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
  Option.iter (fun export ->
      let mpl = List.map (fun m -> Unfiltered, MPfile m) modl in
      (* TODO support filters in Require *)
      Declaremods.import_modules ~export mpl)
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

let require_library_from_dirpath ~lib_resolver modrefl export =
  let needed, contents = List.fold_left (rec_intern_library ~lib_resolver) ([], DPmap.empty) modrefl in
  let needed = List.rev_map (fun dir -> DPmap.find dir contents) needed in
  let modrefl = List.map fst modrefl in
  if Lib.is_module_or_modtype () then
    begin
      warn_require_in_module ();
      add_anonymous_leaf (in_require (needed,modrefl,None));
      Option.iter (fun export ->
          (* TODO import filters *)
          List.iter (fun m -> Declaremods.import_module Unfiltered ~export (MPfile m)) modrefl)
        export
    end
  else
    add_anonymous_leaf (in_require (needed,modrefl,export));
  ()

(************************************************************************)
(*s Initializing the compilation of a library. *)

let load_library_todo f =
  let ch = raw_intern_library f in
  let _segments = ObjFile.segments ch in
  let (s0 : seg_sum), _ = ObjFile.marshal_in_segment ch ~segment:"summary" in
  let (s1 : seg_lib), _ = ObjFile.marshal_in_segment ch ~segment:"library" in
  let (s2 : seg_univ option), _ = ObjFile.marshal_in_segment ch ~segment:"universes" in
  let tasks, _ = ObjFile.marshal_in_segment ch ~segment:"tasks" in
  ObjFile.close_in ch;
  System.check_caml_version ~caml:s0.md_ocaml ~file:f;
  if tasks = None then user_err ~hdr:"restart" (str"not a .vio file");
  if s2 = None then user_err ~hdr:"restart" (str"not a .vio file");
  if snd (Option.get s2) then user_err ~hdr:"restart" (str"not a .vio file");
  s0, s1, Option.get s2, Option.get tasks, assert false (* FIXME *)

(************************************************************************)
(*s [save_library dir] ends library [dir] and save it to the disk. *)

let current_deps () =
  let map name =
    let m = try_find_library name in
    (name, m.libsum_digests)
  in
  List.map map !libraries_loaded_list

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

type opaques =
| OpaqueDirect of seg_proofs
| OpaqueAncient of Opaqueproof.opaque_proofterm Ancient.t option array

let save_library_base f sum lib univs tasks (proofs : opaques) =
  let ch = raw_extern_library f in
  try
    ObjFile.marshal_out_segment ch ~segment:"summary" (sum    : seg_sum);
    ObjFile.marshal_out_segment ch ~segment:"library" (lib    : seg_lib);
    ObjFile.marshal_out_segment ch ~segment:"universes" (univs  : seg_univ option);
    ObjFile.marshal_out_segment ch ~segment:"tasks" (tasks  : 'tasks option);
    let () = match proofs with
    | OpaqueDirect proofs ->
      let iter i = function
      | None -> ()
      | Some (proof : Opaqueproof.opaque_proofterm) ->
        let segment = Printf.sprintf "opaques/%i" i in
        ObjFile.marshal_out_segment ch ~segment proof
      in
      Array.iteri iter proofs
    | OpaqueAncient proofs ->
      let iter i = function
      | None -> ()
      | Some proof ->
        let segment = Printf.sprintf "opaques/%i" i in
        let ch, final = ObjFile.marshal_out_binary ch ~segment in
        let () = Ancient.serialize proof ch in
        let () = final () in
        Ancient.delete proof
      in
      Array.iteri iter proofs
    in
    ObjFile.close_out ch
  with reraise ->
    let reraise = Exninfo.capture reraise in
    ObjFile.close_out ch;
    Feedback.msg_warning (str "Removed file " ++ str f);
    Sys.remove f;
    Exninfo.iraise reraise

type ('document,'counters) todo_proofs =
 | ProofsTodoNone (* for .vo *)
 | ProofsTodoSomeEmpty of Future.UUIDSet.t (* for .vos *)
 | ProofsTodoSome of Future.UUIDSet.t * ((Future.UUID.t,'document) Stateid.request * bool) list * 'counters (* for .vio *)

let save_library_to todo_proofs ~output_native_objects dir f otab =
  assert(
    let expected_extension = match todo_proofs with
      | ProofsTodoNone -> ".vo"
      | ProofsTodoSomeEmpty _ -> ".vos"
      | ProofsTodoSome _ -> ".vio"
      in
    Filename.check_suffix f expected_extension);
  let except = match todo_proofs with
    | ProofsTodoNone -> Future.UUIDSet.empty
    | ProofsTodoSomeEmpty except -> except
    | ProofsTodoSome (except,l,_) -> except
    in
  let cenv, seg, ast = Declaremods.end_library ~output_native_objects ~except dir in
  let opaque_table, f2t_map = Opaqueproof.dump ~except otab in
  let tasks, utab =
    match todo_proofs with
    | ProofsTodoNone -> None, None
    | ProofsTodoSomeEmpty _except ->
      None, Some (Univ.ContextSet.empty,false)
    | ProofsTodoSome (_except, tasks, rcbackup) ->
      let tasks =
        List.map Stateid.(fun (r,b) ->
            try { r with uuid = Future.UUIDMap.find r.uuid f2t_map }, b
            with Not_found -> assert b; { r with uuid = -1 }, b)
          tasks in
      Some (tasks,rcbackup),
      Some (Univ.ContextSet.empty,false)
    in
    let sd = {
    md_name = dir;
    md_deps = Array.of_list (current_deps ());
    md_ocaml = Coq_config.caml_version;
  } in
  let md = {
    md_compiled = cenv;
    md_objects = seg;
  } in
  if Array.exists (fun (d,_) -> DirPath.equal d dir) sd.md_deps then
    error_recursively_dependent_library dir;
  (* Writing vo payload *)
  save_library_base f sd md utab tasks (OpaqueAncient opaque_table);
  (* Writing native code files *)
  if output_native_objects then
    let fn = Filename.dirname f ^"/"^ Nativecode.mod_uid_of_dirpath dir in
    Nativelib.compile_library dir ast fn

let save_library_raw f sum lib univs proofs =
  save_library_base f sum lib (Some univs) None (OpaqueDirect proofs)

let get_used_load_paths () =
  String.Set.elements
    (List.fold_left (fun acc m -> String.Set.add
      (Filename.dirname (library_full_filename m)) acc)
       String.Set.empty !libraries_loaded_list)

let _ = Nativelib.get_load_paths := get_used_load_paths
