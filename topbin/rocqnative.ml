(* Rocq native compiler *)
open CErrors
open Util
open Names
open Pp

let fatal_error info anomaly =
  flush_all (); Format.eprintf "@[Fatal Error: @[%a@]@]@\n%!" Pp.pp_with info; flush_all ();
  exit (if anomaly then 129 else 1)

module Loadpath :
sig
  val add_load_path : string * DirPath.t -> unit
  val default_root_prefix : DirPath.t
  val dirpath_of_string : string -> DirPath.t
  val locate_absolute_library : DirPath.t -> string
end =
struct

let pr_dirpath dp = str (DirPath.to_string dp)
let default_root_prefix = DirPath.empty
let split_dirpath d =
  let l = DirPath.repr d in (DirPath.make (List.tl l), List.hd l)

type logical_path = DirPath.t

let load_paths = ref ([],[] : CUnix.physical_path list * logical_path list)

let remove_load_path dir =
  let physical, logical = !load_paths in
  load_paths := List.filter2 (fun p d -> p <> dir) physical logical

let add_load_path (phys_path,rocq_path) =
  if CDebug.(get_flag misc) then
    Feedback.msg_notice (str "path: " ++ pr_dirpath rocq_path ++ str " ->" ++ spc() ++
           str phys_path);
  let phys_path = CUnix.canonical_path_name phys_path in
  let physical, logical = !load_paths in
    match List.filter2 (fun p d -> p = phys_path) physical logical with
      | _,[dir] ->
          if rocq_path <> dir
            (* If this is not the default -I . to coqtop *)
            && not
            (phys_path = CUnix.canonical_path_name Filename.current_dir_name
                && rocq_path = default_root_prefix)
          then
            begin
              (* Assume the user is concerned by library naming *)
              if dir <> default_root_prefix then
                Feedback.msg_warning
                  (str phys_path ++ strbrk " was previously bound to " ++
                   pr_dirpath dir ++ strbrk "; it is remapped to " ++
                   pr_dirpath rocq_path);
              remove_load_path phys_path;
              load_paths := (phys_path::fst !load_paths, rocq_path::snd !load_paths)
            end
      | _,[] ->
          load_paths := (phys_path :: fst !load_paths, rocq_path :: snd !load_paths)
      | _ -> anomaly (Pp.str ("Two logical paths are associated to "^phys_path^"."))

let load_paths_of_dir_path dir =
  let physical, logical = !load_paths in
  fst (List.filter2 (fun p d -> d = dir) physical logical)

let locate_absolute_library dir =
  (* Search in loadpath *)
  let pref, base = split_dirpath dir in
  let loadpath = load_paths_of_dir_path pref in
  if loadpath = [] then CErrors.user_err (str "No loadpath for " ++ DirPath.print pref);
  let name = Id.to_string base^".vo" in
  try
    let _, file = System.where_in_path ~warn:false loadpath name in
    file
  with Not_found ->
    CErrors.user_err (str "File " ++ str name ++ str " not found in loadpath")

let dirpath_of_string s = match String.split_on_char '.' s with
| [""] -> default_root_prefix
| dir -> DirPath.make (List.rev_map Id.of_string dir)

end

module Library =
struct

type library_objects

type compilation_unit_name = DirPath.t

(* The [*_disk] types below must be kept in sync with the vo representation. *)

type library_disk = {
  md_compiled : Safe_typing.compiled_library;
  md_syntax_objects : library_objects;
  md_objects : library_objects;
}

type library_info

type summary_disk = {
  md_name : compilation_unit_name;
  md_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  md_ocaml : string;
  md_info : library_info;
}

type library_t = {
  library_name : compilation_unit_name;
  library_file : string;
  library_data : Safe_typing.compiled_library;
  library_deps : (compilation_unit_name * Safe_typing.vodigest) array;
  library_digests : Safe_typing.vodigest;
  library_vm : Vmlibrary.on_disk;
}

let libraries_table : string DPmap.t ref = ref DPmap.empty

let register_loaded_library senv libname file =
  let () = assert (not @@ DPmap.mem libname !libraries_table) in
  let () = libraries_table := DPmap.add libname file !libraries_table in
  let prefix = Nativecode.mod_uid_of_dirpath libname ^ "." in
  let () = Nativecode.register_native_file prefix in
  senv

let mk_library sd f md digests vm =
  {
    library_name     = sd.md_name;
    library_file     = f;
    library_data     = md;
    library_deps     = sd.md_deps;
    library_digests  = digests;
    library_vm = vm;
  }

let summary_seg : summary_disk ObjFile.id = ObjFile.make_id "summary"
let library_seg : library_disk ObjFile.id = ObjFile.make_id "library"

let intern_from_file f =
  let ch = System.with_magic_number_check (fun file -> ObjFile.open_in ~file) f in
  let lsd, digest_lsd = ObjFile.marshal_in_segment ch ~segment:summary_seg in
  let lmd, digest_lmd = ObjFile.marshal_in_segment ch ~segment:library_seg in
  let vmlib = Vmlibrary.load ~file:f lsd.md_name ch in
  ObjFile.close_in ch;
  System.check_caml_version ~caml:lsd.md_ocaml ~file:f;
  let open Safe_typing in
  mk_library lsd f lmd.md_compiled (Dvo_or_vi digest_lmd) vmlib

let rec intern_library (needed, contents) dir =
  (* Look if already listed and consequently its dependencies too *)
  match DPmap.find dir contents with
  | lib -> lib.library_digests, (needed, contents)
  | exception Not_found ->
  let f = Loadpath.locate_absolute_library dir in
  let m = intern_from_file f in
  if not (DirPath.equal dir m.library_name) then
    user_err
      (str "The file " ++ str f ++ str " contains library" ++ spc () ++
       DirPath.print m.library_name ++ spc () ++ str "and not library" ++
       spc() ++ DirPath.print dir ++ str ".");
  let (needed, contents) = intern_library_deps (needed, contents) dir m f in
  m.library_digests, (dir :: needed, DPmap.add dir m contents)

and intern_library_deps libs dir m from =
  Array.fold_left (intern_mandatory_library dir from) libs m.library_deps

and intern_mandatory_library caller from libs (dir,d) =
  let digest, libs = intern_library libs dir in
  if not (Safe_typing.digest_match ~actual:digest ~required:d) then
    user_err (str "Compiled library " ++ DirPath.print caller ++
    str " (in file " ++ str from ++ str ") makes inconsistent assumptions \
    over library " ++ DirPath.print dir);
  libs

let register_library senv m =
  let mp = MPfile m.library_name in
  let mp', senv = Safe_typing.import m.library_data m.library_vm m.library_digests senv in
  let () =
    if not (ModPath.equal mp mp') then
      anomaly (Pp.str "Unexpected disk module name.")
  in
  register_loaded_library senv m.library_name m.library_file

let save_library_to env dir f lib =
  let mp = MPfile dir in
  let ast = Nativelibrary.dump_library mp env lib in
  let fn = Filename.dirname f ^"/"^ Nativecode.mod_uid_of_dirpath dir in
  Nativelib.compile_library ast fn

let get_used_load_paths () =
  String.Set.elements
    (DPmap.fold (fun m f acc -> String.Set.add
      (Filename.dirname f) acc)
       !libraries_table String.Set.empty)

let _ = Nativelib.get_load_paths := get_used_load_paths
end

let add_path ~unix_path:dir ~rocq_root:rocq_dirpath =
  let open System in
  if exists_dir dir then
    begin
      Loadpath.add_load_path (dir,rocq_dirpath)
    end
  else
    Feedback.msg_warning (str "Cannot open " ++ str dir)

let convert_string d =
  try Id.of_string d
  with CErrors.UserError _ ->
    Flags.if_verbose Feedback.msg_warning
      (str "Directory " ++ str d ++ str " cannot be used as a Rocq identifier (skipped)");
    raise_notrace Exit

let rocq_root = Id.of_string "Corelib"

let add_rec_path ~unix_path ~rocq_root =
  let open System in
  if exists_dir unix_path then
    let dirs = all_subdirs ~unix_path in
    let prefix = DirPath.repr rocq_root in
    let convert_dirs (lp, cp) =
      try
        let path = List.rev_map convert_string cp @ prefix in
        Some (lp, Names.DirPath.make path)
      with Exit -> None
    in
    let dirs = List.map_filter convert_dirs dirs in
    List.iter Loadpath.add_load_path dirs;
    Loadpath.add_load_path (unix_path, rocq_root)
  else
    Feedback.msg_warning (str "Cannot open " ++ str unix_path)

let init_load_path_std () =
  let env = Boot.Env.init () in
  let stdlib = Boot.Env.stdlib env |> Boot.Path.to_string in
  let user_contrib = Boot.Env.user_contrib env |> Boot.Path.to_string in
  let xdg_dirs = Envars.xdg_dirs in
  let rocqpath = Envars.coqpath in
  (* NOTE: These directories are searched from last to first *)
  (* first standard library *)
  add_rec_path ~unix_path:stdlib ~rocq_root:(Names.DirPath.make[rocq_root]);
  (* then user-contrib *)
  if Sys.file_exists user_contrib then
    add_rec_path ~unix_path:user_contrib ~rocq_root:Loadpath.default_root_prefix;
  (* then directories in XDG_DATA_DIRS and XDG_DATA_HOME *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:Loadpath.default_root_prefix)
    (xdg_dirs ~warn:(fun x -> Feedback.msg_warning (str x)));
  (* then directories in ROCQPATH *)
  List.iter (fun s -> add_rec_path ~unix_path:s ~rocq_root:Loadpath.default_root_prefix) (rocqpath())

let init_load_path ~boot ~vo_path =
  if not boot then init_load_path_std ();
  (* always add current directory *)
  add_path ~unix_path:"." ~rocq_root:Loadpath.default_root_prefix;
  (* additional loadpath, given with -R/-Q options *)
  List.iter
    (fun (unix_path, rocq_root) -> add_rec_path ~unix_path ~rocq_root)
    (List.rev vo_path)

let fb_handler = function
  | Feedback.{ contents; _ } ->
    match contents with
    | Feedback.Message(_lvl,_loc,_qf, msg)->
      Format.printf "%s@\n%!" Pp.(string_of_ppcmds msg)
    | _ -> ()

let init_rocq () =
  let senv = Safe_typing.empty_environment in
  let senv = Safe_typing.set_native_compiler true senv in
  let () = Safe_typing.allow_delayed_constants := false in
  let dummy = Names.DirPath.make [Names.Id.of_string_soft "@native"] in
  let _, senv = Safe_typing.start_library dummy senv in
  senv

let compile senv ~in_file =
  let lib = Library.intern_from_file in_file in
  let dir = lib.Library.library_name in
  (* Require the dependencies **only once** *)
  let deps, contents = Library.intern_library_deps ([], DPmap.empty) dir lib in_file in
  let fold senv dep = Library.register_library senv (DPmap.find dep contents) in
  let senv = List.fold_left fold senv (List.rev deps) in
  (* Extract the native code and compile it *)
  let modl = Mod_declarations.mod_type (Safe_typing.module_of_library lib.Library.library_data) in
  let out_vo = Filename.(remove_extension in_file) ^ ".vo" in
  Library.save_library_to (Safe_typing.env_of_safe_env senv) dir out_vo modl

module Usage :
sig
  val usage : unit -> 'a
end =
struct

let print_usage_channel co command =
  output_string co command;
  output_string co "rocq native-precompile options are:\n";
  output_string co
"  -Q dir coqdir          map physical dir to logical coqdir\
\n  -R dir coqdir          synonymous for -Q\
\n\
\n\
\n  -boot                  boot mode\
\n  -coqlib dir            set coqnative's standard library location\
\n  -native-output-dir     <directory> set the output directory for native objects\
\n  -nI dir                OCaml include directories for the native compiler (default if not set) \
\n\
\n  -h, --help             print this list of options\
\n"

(* print the usage on standard error *)

let print_usage = print_usage_channel stderr

let print_usage_coqnative () =
  print_usage "Usage: rocq native-precompile <options> file\n\n"

let usage () =
  print_usage_coqnative ();
  flush stderr;
  exit 1

end

type opts = {
  boot : bool;
  vo_path : (string * DirPath.t) list;
  ml_path : string list;
}

let rec parse_args (args : string list) accu =
  match args with
  | [] -> CErrors.user_err (Pp.str "parse args error: missing argument")
  | "-boot" :: rem ->
    parse_args rem { accu with boot = true}
  (* We ignore as we don't require Prelude explicitly *)
  | "-noinit" :: rem ->
    parse_args rem accu
  | ("-Q" | "-R") :: d :: p :: rem ->
    let p = if String.equal p "Coq" then "Corelib" else p in
    (* -R Coq ... is only used by Dune in conjunction with the -boot
       option. The above line should be removed once we require an
       updated version of Dune. *)
    let p = Loadpath.dirpath_of_string p in
    let accu = { accu with vo_path = (d, p) :: accu.vo_path } in
    parse_args rem accu
  | "-I" :: _d :: rem ->
    (* Ignore *)
    parse_args rem accu
  | "-nI" :: dir :: rem ->
    let accu =  { accu with ml_path = dir :: accu.ml_path } in
    parse_args rem accu
  |"-native-output-dir" :: dir :: rem ->
    Nativelib.output_dir := dir;
    parse_args rem accu
  | "-coqlib" :: s :: rem ->
    if not (System.exists_dir s) then
      fatal_error (str "Directory '" ++ str s ++ str "' does not exist") false;
    Boot.Env.set_coqlib s;
    parse_args rem accu
  | ("-?"|"-h"|"-H"|"-help"|"--help") :: _ -> Usage.usage ()
  | [file] ->
    accu, file
  | args ->
    let args_msg = String.concat " " args in
    CErrors.user_err Pp.(str "parse args error, too many arguments: " ++ str args_msg)

let () =
  let _ = Feedback.add_feeder fb_handler in
  try
    let opts = { boot = false; vo_path = []; ml_path = [] } in
    let opts, in_file = parse_args (List.tl @@ Array.to_list Sys.argv) opts in
    let () = init_load_path ~boot:opts.boot ~vo_path:(List.rev opts.vo_path) in
    let () = Nativelib.include_dirs := List.rev opts.ml_path in
    let senv = init_rocq () in
    compile senv ~in_file
  with exn ->
    Format.eprintf "Error: @[%a@]@\n%!" Pp.pp_with (CErrors.print exn);
    let exit_code = if (CErrors.is_anomaly exn) then 129 else 1 in
    exit exit_code
