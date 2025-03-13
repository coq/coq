(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
open Libobject

(************************************************************************)
(*s Low-level interning/externing of libraries to files *)

let raw_extern_library f =
  ObjFile.open_out ~file:f

let raw_intern_library ?loc f =
  System.with_magic_number_check ?loc
   (fun file -> ObjFile.open_in ~file) f

(************************************************************************)
(** Serialized objects loaded on-the-fly *)

exception Faulty of string

module Delayed :
sig

type 'a delayed
val in_delayed : string -> ObjFile.in_handle -> segment:'a ObjFile.id -> 'a delayed * Digest.t
val fetch_delayed : 'a delayed -> 'a

end =
struct

type 'a delayed = {
  del_file : string;
  del_off : int64;
  del_digest : Digest.t;
}

let in_delayed f ch ~segment =
  let seg = ObjFile.get_segment ch ~segment in
  let digest = seg.ObjFile.hash in
  { del_file = f; del_digest = digest; del_off = seg.ObjFile.pos; }, digest

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
  md_syntax_objects : Declaremods.library_objects;
  md_objects : Declaremods.library_objects;
}

type summary_disk = {
  md_name : compilation_unit_name;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : Library_info.t;
}

(*s Modules loaded in memory contain the following informations. They are
    kept in the global table [libraries_table]. *)

type library_t = {
  library_name : compilation_unit_name;
  library_data : library_disk;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digests : Safe_typing.vodigest;
  library_info : Library_info.t;
  library_vm : Vmlibrary.on_disk;
}

(* This is a map from names to loaded libraries *)
let libraries_table : library_t DPmap.t ref =
  Summary.ref DPmap.empty ~stage:Summary.Stage.Synterp ~name:"LIBRARY"

(* This is the map of loaded libraries filename *)
(* (not synchronized so as not to be caught in the states on disk) *)
let libraries_filename_table = ref DPmap.empty

(* These are the _ordered_ sets of loaded, imported and exported libraries *)
let libraries_loaded_list = Summary.ref [] ~stage:Summary.Stage.Synterp ~name:"LIBRARY-LOAD"

let loaded_native_libraries = Summary.ref DPset.empty ~stage:Summary.Stage.Interp ~name:"NATIVE-LIBRARY-LOAD"

(* Opaque proof tables *)

(* various requests to the tables *)

let find_library dir =
  DPmap.find_opt dir !libraries_table

let try_find_library dir =
  match find_library dir with
  | Some lib -> lib
  | None ->
    user_err
      (str "Unknown library " ++ DirPath.print dir ++ str ".")

let library_compiled dir =
  let lib = Option.get @@ find_library dir in
  lib.library_data.md_compiled

let register_library_filename dir f =
  (* Not synchronized: overwrite the previous binding if one existed *)
  (* from a previous play of the session *)
  libraries_filename_table :=
    DPmap.add dir f !libraries_filename_table

let library_full_filename dir =
  try DPmap.find dir !libraries_filename_table
  with Not_found -> "<unavailable filename>"

let library_is_loaded dir =
  try let _ = find_library dir in true
  with Not_found -> false

  (* If a library is loaded several time, then the first occurrence must
     be performed first, thus the libraries_loaded_list ... *)

let register_loaded_library ~root m =
  let libname = m.library_name in
  let rec aux = function
    | [] -> [root, libname]
    | (_, m') ::_ as l when DirPath.equal m' libname -> l
    | m'::l' -> m' :: aux l' in
  libraries_loaded_list := aux !libraries_loaded_list;
  libraries_table := DPmap.add libname m !libraries_table

let register_native_library libname =
  if (Global.typing_flags ()).enable_native_compiler
    && not (DPset.mem libname !loaded_native_libraries) then begin
      let dirname = Filename.dirname (library_full_filename libname) in
      loaded_native_libraries := DPset.add libname !loaded_native_libraries;
      Nativelib.enable_library dirname libname
  end

let loaded_libraries () = List.map snd !libraries_loaded_list

(** Delayed / available tables of opaque terms *)

type table_status =
  | ToFetch of Opaques.opaque_disk delayed
  | Fetched of Opaques.opaque_disk

let opaque_tables =
  ref (DPmap.empty : table_status DPmap.t)

let add_opaque_table dp st =
  opaque_tables := DPmap.add dp st !opaque_tables

let access_table what tables dp i =
  let t = match DPmap.find dp !tables with
    | Fetched t -> t
    | ToFetch f ->
      let dir_path = Names.DirPath.to_string dp in
      Flags.if_verbose Feedback.msg_info (str"Fetching " ++ str what++str" from disk for " ++ str dir_path);
      let t =
        try fetch_delayed f
        with Faulty f ->
          user_err
            (str "The file " ++ str f ++ str " (bound to " ++ str dir_path ++
             str ") is corrupted,\ncannot load some " ++
             str what ++ str " in it.\n")
      in
      tables := DPmap.add dp (Fetched t) !tables;
      t
  in
  Opaques.get_opaque_disk i t

let access_opaque_table o =
  let (sub, ci, dp, i) = Opaqueproof.repr o in
  let ans =
    if DirPath.equal dp (Global.current_dirpath ()) then
      Opaques.get_current_opaque i
    else
      let what = "opaque proofs" in
      access_table what opaque_tables dp i
  in
  match ans with
  | None -> None
  | Some (c, ctx) ->
    let (c, ctx) = Discharge.cook_opaque_proofterm ci (c, ctx) in
    let c = Mod_subst.subst_mps_list sub c in
    Some (c, ctx)

let indirect_accessor = {
  Global.access_proof = access_opaque_table;
}

(************************************************************************)
(* Internalise libraries *)

type seg_sum = summary_disk
type seg_lib = library_disk
type seg_proofs = Opaques.opaque_disk
type seg_vm = Vmlibrary.compiled_library

let mk_library sd md digests vm =
  {
    library_name     = sd.md_name;
    library_data     = md;
    library_deps     = sd.md_deps;
    library_digests  = digests;
    library_info     = sd.md_info;
    library_vm = vm;
  }

let mk_intern_library sum lib digest_lib proofs vm =
  add_opaque_table sum.md_name (ToFetch proofs);
  let open Safe_typing in
  mk_library sum lib (Dvo_or_vi digest_lib) vm

let summary_seg : seg_sum ObjFile.id = ObjFile.make_id "summary"
let library_seg : seg_lib ObjFile.id = ObjFile.make_id "library"
let opaques_seg : seg_proofs ObjFile.id = ObjFile.make_id "opaques"
let vm_seg : seg_vm ObjFile.id = Vmlibrary.vm_segment

module Intern = struct
  module Provenance = struct
    type t = string * string
    (** A pair of [kind, object], for example ["file",
        "/usr/local/foo.vo"], used for error messages. *)
  end

  type t = DirPath.t -> (library_t, Exninfo.iexn) Result.t * Provenance.t
end

let intern_from_file file =
  let ch = raw_intern_library file in
  let lsd, digest_lsd = ObjFile.marshal_in_segment ch ~segment:summary_seg in
  let lmd, digest_lmd = ObjFile.marshal_in_segment ch ~segment:library_seg in
  let del_opaque, _ = in_delayed file ch ~segment:opaques_seg in
  let vmlib = Vmlibrary.load lsd.md_name ~file ch in
  ObjFile.close_in ch;
  System.check_caml_version ~caml:lsd.md_ocaml ~file;
  register_library_filename lsd.md_name file;
  Library_info.warn_library_info ~transitive:true lsd.md_name lsd.md_info;
  mk_intern_library lsd lmd digest_lmd del_opaque vmlib

let intern_from_file file =
  let provenance = ("file", file) in
  (* This is a barrier to catch IO / Marshal exceptions in a more
     structured way, as to provide better error messages. *)
  (match CErrors.to_result ~f:intern_from_file file with
   | Ok res -> Ok res
   | Error iexn -> Error iexn), provenance

let check_library_expected_name ~provenance dir library_name =
  if not (DirPath.equal dir library_name) then
    let kind, obj = provenance in
    user_err
      (str "The " ++ str kind ++ str " " ++ str obj ++ str " contains library" ++ spc () ++
       DirPath.print library_name ++ spc () ++ str "and not library" ++
       spc() ++ DirPath.print dir ++ str ".")

exception InternError of { exn : exn; provenance : Intern.Provenance.t; dir : DirPath.t }

let () = CErrors.register_handler (function
    | InternError { exn; provenance; dir } ->
      let err = CErrors.print exn in
      Some (Pp.(str "Error when parsing .vo (from " ++ str (fst provenance) ++ str " " ++
                str (snd provenance) ++ str ") for library " ++ Names.DirPath.print dir ++ str ": " ++ err))
    | _ -> None)

let error_in_intern provenance dir (exn, info) =
  Exninfo.iraise (InternError { exn; provenance; dir }, info)

(* Returns the digest of a library, checks both caches to see what is loaded *)
let rec intern_library ~root ~intern (needed, contents as acc) dir =
  (* Look if in the current logical environment *)
  match find_library dir with
  | Some loaded_lib -> loaded_lib, acc
  | None ->
    (* Look if already listed in the accumulator *)
    match DPmap.find_opt dir contents with
    | Some interned_lib ->
      interned_lib, acc
    | None ->
      (* We intern the library, and then intern the deps *)
      match intern dir with
      | Ok m, provenance ->
        check_library_expected_name ~provenance dir m.library_name;
        m, intern_library_deps ~root ~intern acc dir m
      | Error iexn, provenance ->
        error_in_intern provenance dir iexn

and intern_library_deps ~root ~intern libs dir m =
  let needed, contents =
    Array.fold_left (intern_mandatory_library ~intern dir)
      libs m.library_deps in
  ((root, dir) :: needed, DPmap.add dir m contents )

and intern_mandatory_library ~intern caller libs (dir,d) =
  let m, libs = intern_library ~root:false ~intern libs dir in
  let digest = m.library_digests in
  let () = if not (Safe_typing.digest_match ~actual:digest ~required:d) then
    let from = library_full_filename caller in
    user_err
      (str "Compiled library " ++ DirPath.print caller ++
       str " (in file " ++ str from ++
       str ") makes inconsistent assumptions over library " ++
       DirPath.print dir)
  in
  libs

let rec_intern_library ~intern libs (loc, dir) =
  let m, libs = intern_library ~root:true ~intern libs dir in
  Library_info.warn_library_info m.library_name m.library_info;
  libs

let native_name_from_filename f =
  let ch = raw_intern_library f in
  let lmd, digest_lmd = ObjFile.marshal_in_segment ch ~segment:summary_seg in
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
  Declaremods.Interp.register_library
    m.library_name
    l.md_compiled
    l.md_objects
    m.library_digests
    m.library_vm
  ;
  register_native_library m.library_name

let register_library_syntax (root, m) =
  let l = m.library_data in
  Declaremods.Synterp.register_library
    m.library_name
    l.md_syntax_objects;
  register_loaded_library ~root m

(* Follow the semantics of Anticipate object:
   - called at module or module type closing when a Require occurs in
     the module or module type
   - not called from a library (i.e. a module identified with a file) *)
let load_require _ needed =
  List.iter register_library needed

  (* [needed] is the ordered list of libraries not already loaded *)
let cache_require o =
  load_require 1 o

let discharge_require o = Some o

(* open_function is never called from here because an Anticipate object *)

type require_obj = library_t list

let in_require : require_obj -> obj =
  declare_object
    {(default_object "REQUIRE") with
     cache_function = cache_require;
     load_function = load_require;
     open_function = (fun _ _ -> assert false);
     discharge_function = discharge_require;
     classify_function = (fun o -> Anticipate) }

let load_require_syntax _ needed =
  List.iter register_library_syntax needed

let cache_require_syntax o =
  load_require_syntax 1 o

let discharge_require_syntax o = Some o

(* open_function is never called from here because an Anticipate object *)

type require_obj_syntax = (bool * library_t) list

let in_require_syntax : require_obj_syntax -> obj =
  declare_object
    {(default_object "REQUIRE-SYNTAX") with
     object_stage = Summary.Stage.Synterp;
     cache_function = cache_require_syntax;
     load_function = load_require_syntax;
     open_function = (fun _ _ -> assert false);
     discharge_function = discharge_require_syntax;
     classify_function = (fun o -> Anticipate) }

(* Require libraries, import them if [export <> None], mark them for export
   if [export = Some true] *)

let warn_require_in_module =
  CWarnings.create ~name:"require-in-module" ~category:CWarnings.CoreCategories.fragile
    (fun () -> strbrk "Use of “Require” inside a module is fragile." ++ spc() ++
               strbrk "It is not recommended to use this functionality in finished proof scripts.")

let require_library_from_dirpath needed =
  if Lib.is_module_or_modtype () then warn_require_in_module ();
  Lib.add_leaf (in_require needed)

let require_library_syntax_from_dirpath ~intern modrefl =
  let needed, contents = List.fold_left (rec_intern_library ~intern) ([], DPmap.empty) modrefl in
  let needed = List.rev_map (fun (root, dir) -> root, DPmap.find dir contents) needed in
  Lib.add_leaf (in_require_syntax needed);
  List.map snd needed

(************************************************************************)
(*s [save_library dir] ends library [dir] and save it to the disk. *)

let current_deps () =
  (* Only keep the roots of the dependency DAG *)
  let map (root, m) =
    if root then
      let m = try_find_library m in
      Some (m.library_name, m.library_digests)
    else None
  in
  List.map_filter map !libraries_loaded_list

let error_recursively_dependent_library dir =
  user_err
    (strbrk "Unable to use logical name " ++ DirPath.print dir ++
     strbrk " to save current library because" ++
     strbrk " it already depends on a library of this name.")

type 'doc todo_proofs =
 | ProofsTodoNone (* for .vo *)
 | ProofsTodoSomeEmpty of Future.UUIDSet.t (* for .vos *)

(* We now use two different digests in a .vo file. The first one
   only covers half of the file, without the opaque table. It is
   used for identifying this version of this library : this digest
   is the one leading to "inconsistent assumptions" messages.
   The other digest comes at the very end, and covers everything
   before it. This one is used for integrity check of the whole
   file when loading the opaque table. *)

(* Security weakness: file might have been changed on disk between
   writing the content and computing the checksum... *)

let save_library_base f sum lib proofs vmlib =
  let ch = raw_extern_library f in
  try
    ObjFile.marshal_out_segment ch ~segment:summary_seg sum;
    ObjFile.marshal_out_segment ch ~segment:library_seg lib;
    ObjFile.marshal_out_segment ch ~segment:opaques_seg proofs;
    ObjFile.marshal_out_segment ch ~segment:vm_seg vmlib;
    ObjFile.close_out ch
  with reraise ->
    let reraise = Exninfo.capture reraise in
    ObjFile.close_out ch;
    Feedback.msg_warning (str "Removed file " ++ str f);
    Sys.remove f;
    Exninfo.iraise reraise

(* This is the basic vo save structure *)
let save_library_struct ~output_native_objects dir =
  let md_compiled, md_objects, md_syntax_objects, vmlib, ast, info =
    Declaremods.end_library ~output_native_objects dir in
  let sd =
    { md_name = dir
    ; md_deps = Array.of_list (current_deps ())
    ; md_ocaml = Coq_config.caml_version
    ; md_info = info
    } in
  let md =
    { md_compiled
    ; md_syntax_objects
    ; md_objects
    } in
  if Array.exists (fun (d,_) -> DirPath.equal d dir) sd.md_deps then
    error_recursively_dependent_library dir;
  sd, md, vmlib, ast

let save_library dir : library_t =
  let sd, md, vmlib, _ast = save_library_struct ~output_native_objects:false dir in
  (* Digest for .vo files is on the md part, for now we also play it
     safe when we work on-memory and compute the digest for the lib
     part, even if that's slow. Better safe than sorry. *)
  let digest = Marshal.to_string md [] |> Digest.string in
  mk_library sd md (Dvo_or_vi digest) (Vmlibrary.inject vmlib)

let save_library_to todo_proofs ~output_native_objects dir f =
  assert(
    let expected_extension = match todo_proofs with
      | ProofsTodoNone -> ".vo"
      | ProofsTodoSomeEmpty _ -> ".vos"
      in
    Filename.check_suffix f expected_extension);
  let except = match todo_proofs with
    | ProofsTodoNone -> Future.UUIDSet.empty
    | ProofsTodoSomeEmpty except -> except
    in
  (* Ensure that the call below is performed with all opaques joined *)
  let () = Opaques.Summary.join ~except () in
  let opaque_table, f2t_map = Opaques.dump ~except () in
  let () = assert (not (Future.UUIDSet.is_empty except) ||
    Safe_typing.is_joined_environment (Global.safe_env ()))
  in
  let sd, md, vmlib, ast = save_library_struct ~output_native_objects dir in
  (* Writing vo payload *)
  save_library_base f sd md opaque_table vmlib;
  (* Writing native code files *)
  if output_native_objects then
    let fn = Filename.dirname f ^"/"^ Nativecode.mod_uid_of_dirpath dir in
    Nativelib.compile_library ast fn

let get_used_load_paths () =
  String.Set.elements
    (List.fold_left (fun acc (root, m) -> String.Set.add
      (Filename.dirname (library_full_filename m)) acc)
       String.Set.empty !libraries_loaded_list)

let _ = Nativelib.get_load_paths := get_used_load_paths
