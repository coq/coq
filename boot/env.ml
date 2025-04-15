(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

module Path = struct

  type t = string

  let relative = Filename.concat
  let to_string x = x
  let exists x = Sys.file_exists x

end

(* For now just a pointer to coq/lib (for .vo) and rocq-runtime/lib (for plugins)  *)
type t =
  { core: Path.t
  ; lib : Path.t
  }

(* This code needs to be refactored, for now it is just what used to be in envvars  *)

let use_suffix prefix suffix =
  if Filename.is_relative suffix
  then Filename.concat prefix suffix
  else suffix

let canonical_path_name p =
  let current = Sys.getcwd () in
  try
    Sys.chdir p;
    let p' = Sys.getcwd () in
    Sys.chdir current;
    p'
  with Sys_error _ ->
    (* We give up to find a canonical name and just simplify it... *)
    Filename.concat current p

let theories_dir = "theories"
let plugins_dir = "plugins"
let prelude = Filename.concat theories_dir "Init/Prelude.vo"

let find_in_PATH f =
  match Sys.getenv_opt "PATH" with
  | None -> None
  | Some paths ->
    let sep = if Coq_config.arch_is_win32 then ';' else ':' in
    let paths = String.split_on_char sep paths in
    paths |> List.find_opt (fun path ->
        Sys.file_exists (if path = "" then f else Filename.concat path f))

let rocqbin =
  (* avoid following symlinks if possible (Sys.executable_name followed symlinks) *)
  if Filename.basename Sys.argv.(0) <> Sys.argv.(0) then
    (* explicit directory (maybe relative to current dir) *)
    canonical_path_name (Filename.dirname Sys.argv.(0))
  else match find_in_PATH Sys.argv.(0) with
    | Some p -> p
    | None -> canonical_path_name (Filename.dirname Sys.executable_name)

(** The following only makes sense when executables are running from
    source tree (e.g. during build or in local mode). *)
let rocqroot =
  let rec search = function
    | [] ->
      (* couldn't recognize the layout, guess the executable is 1 dir below the root
         (eg "mybin/rocq")
         XXX we should search only when we need the root
         and produce an error if we can't find it *)
      Filename.dirname rocqbin
    | path :: rest ->
      if Sys.file_exists (Filename.concat path "bin") then path
      else search rest
  in
  (* we can be "bin/rocq" or "lib/rocq-runtime/rocqworker"
     so rocqbin can be "bin/" or "lib/rocq-runtime/" *)
  let dirname = Filename.dirname in
  search [ dirname rocqbin; dirname @@ dirname rocqbin ]

let relocate = function
  | Coq_config.NotRelocatable p -> p
  | Coq_config.Relocatable p -> Filename.concat rocqroot p

(** [check_file_else ~dir ~file oth] checks if [file] exists in
    the installation directory [dir] given relatively to [coqroot],
    which maybe has been relocated.
    If the check fails, then [oth ()] is evaluated.
    Using file system equality seems well enough for this heuristic *)
let check_file_else ~dir ~file oth =
  let path = use_suffix rocqroot dir in
  if Sys.file_exists (Filename.concat path file) then path else oth ()

let guess_coqlib () =
  match Util.getenv_rocq "LIB" with
  | Some v -> v
  | None ->
    check_file_else
      ~dir:Coq_config.coqlibsuffix
      ~file:prelude
      (fun () -> relocate Coq_config.coqlib)

(* Build layout uses coqlib = coqcorelib
   XXX we should be using -boot in build layout so is that dead code? *)
let guess_coqcorelib lib =
  match Util.getenv_rocq_gen ~rocq:"ROCQRUNTIMELIB" ~coq:"COQCORELIB" with
  | Some v -> v
  | None ->
    if Sys.file_exists (Path.relative lib plugins_dir)
    then lib
    else Path.relative lib "../rocq-runtime"

let fail_lib lib =
  let open Printf in
  eprintf "File not found: %s\n" lib;
  eprintf "The path for Rocq libraries is wrong.\n";
  eprintf "Rocq prelude is shipped in the rocq-core package.\n";
  eprintf "Please check the ROCQLIB env variable or the -coqlib option.\n";
  exit 1

let fail_core plugin =
  let open Printf in
  eprintf "File not found: %s\n" plugin;
  eprintf "The path for Rocq plugins is wrong.\n";
  eprintf "Rocq plugins are shipped in the rocq-runtime package.\n";
  eprintf "Please check the ROCQRUNTIMELIB env variable.\n";
  exit 1

let validate_env ({ core; lib } as env) =
  let lib = Filename.concat lib prelude in
  if not (Sys.file_exists lib) then fail_lib lib;
  let plugin = Filename.concat core plugins_dir in
  if not (Sys.file_exists plugin) then fail_core plugin;
  env

type maybe_env =
  | Env of t
  | Boot

let env_ref = ref None

(* Should we fail on double initialization? That seems a way to avoid
   mis-use for example when we pass command line arguments *)
let init_with ~coqlib =
  let lib = match coqlib with
    | None -> guess_coqlib ()
    | Some lib -> lib
  in
  let env = validate_env { lib; core = guess_coqcorelib lib } in
  env_ref := Some (Env env);
  env

let initialized () = !env_ref

let ignored_coqlib_msg = "Command line options -boot and -coqlib are incompatible, ignored -coqlib."

let maybe_init ~warn_ignored_coqlib ~boot ~coqlib =
  match boot, coqlib with
  | true, None -> Boot
  | false, (None | Some _ as coqlib) ->
    (Env (init_with ~coqlib))
  | true, Some _ ->
    warn_ignored_coqlib ();
    Boot

let coqlib { lib; _ } = lib
let corelib { core; _ } = core
let plugins { core; _ } = Path.relative core plugins_dir
let stdlib { lib; _ } = Path.relative lib theories_dir
let user_contrib { lib; _ } = Path.relative lib "user-contrib"
let tool { core; _ } tool = Path.(relative (relative core "tools") tool)
let revision { core; _ } = Path.relative core "revision"

let native_cmi { core; _ } lib =
  let install_path = Path.relative core lib in
  if Sys.file_exists install_path then
    install_path
  else
    (* Dune build layout, we need to improve this *)
    let obj_dir = Format.asprintf ".%s.objs" lib in
    Filename.(concat (concat (concat core lib) obj_dir) "byte")

(** {2 Caml paths} *)

let ocamlfind () = match Util.getenv_opt "OCAMLFIND" with
  | None -> Coq_config.ocamlfind
  | Some v -> v

let docdir () =
  (* This assumes implicitly that the suffix is non-trivial *)
  let path = use_suffix rocqroot Coq_config.docdirsuffix in
  if Sys.file_exists path then path else relocate Coq_config.docdir

(* Print the configuration information *)

let print_config ?(prefix_var_name="") env f =
  let coqlib = coqlib env |> Path.to_string in
  let corelib = corelib env |> Path.to_string in
  let open Printf in
  fprintf f "%sCOQLIB=%s/\n" prefix_var_name coqlib;
  fprintf f "%sCOQCORELIB=%s/\n" prefix_var_name corelib;
  fprintf f "%sDOCDIR=%s/\n" prefix_var_name (docdir ());
  fprintf f "%sOCAMLFIND=%s\n" prefix_var_name (ocamlfind ());
  fprintf f "%sCAMLFLAGS=%s\n" prefix_var_name Coq_config.caml_flags;
  fprintf f "%sWARN=%s\n" prefix_var_name "-warn-error +a-3";
  fprintf f "%sHASNATDYNLINK=%s\n" prefix_var_name
    (if Coq_config.has_natdynlink then "true" else "false");
  fprintf f "%sCOQ_SRC_SUBDIRS=%s\n" prefix_var_name (String.concat " " Coq_config.all_src_dirs);
  fprintf f "%sCOQ_NATIVE_COMPILER_DEFAULT=%s\n" prefix_var_name
    (match Coq_config.native_compiler with
     | Coq_config.NativeOn {ondemand=false} -> "yes"
     | Coq_config.NativeOff -> "no"
     | Coq_config.NativeOn {ondemand=true} -> "ondemand")

let query_getenv = function
  | Boot -> assert false
  | Env v -> v

let print_query envopt usage : Usage.query -> unit = function
  | PrintVersion -> Usage.version ()
  | PrintMachineReadableVersion -> Usage.machine_readable_version ()
  | PrintWhere ->
    let env = query_getenv envopt in
    let coqlib = coqlib env |> Path.to_string in
    print_endline coqlib
  | PrintHelp -> begin match usage with
      | Some usage -> Usage.print_usage stderr usage
      | None -> assert false
    end
  | PrintConfig ->
    let env = query_getenv envopt in
    print_config env stdout

let query_needs_env : Usage.query -> string option = function
  | PrintVersion | PrintMachineReadableVersion | PrintHelp -> None
  | PrintWhere -> Some "-where"
  | PrintConfig -> Some "-config"

let print_queries_maybe_init ~warn_ignored_coqlib ~boot ~coqlib usage = function
  | [] -> Ok (maybe_init ~warn_ignored_coqlib ~boot ~coqlib)
  | _ :: _ as qs ->
    let needs_env = CList.find_map query_needs_env qs in
    let res = match boot, needs_env with
    | true, Some q -> Error ("Command line option -boot is not compatible with " ^ q ^ ".")
    | true, None ->
      (* warn_ignored_coqlib if coqlib and boot used together *)
      Ok (maybe_init ~warn_ignored_coqlib ~boot ~coqlib)
    | false, None -> Ok Boot
    | false, Some _ -> Ok (Env (init_with ~coqlib))
    in
    let () = match res with
      | Error _ -> ()
      | Ok envopt -> List.iter (print_query envopt usage) qs
    in
    res
