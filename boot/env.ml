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

(* fatal error *)
let fail_msg =
  "cannot guess a path for Rocq libraries; please use -coqlib option \
   or ensure you have installed the package containing Rocq's prelude (rocq-core in OPAM) \
   If you intend to use Rocq without prelude, the -boot -noinit options must be used."

let fail s = Format.eprintf "%s@\n%!" fail_msg; exit 1

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

let coqbin =
  canonical_path_name (Filename.dirname Sys.executable_name)

(** The following only makes sense when executables are running from
    source tree (e.g. during build or in local mode). *)
let coqroot =
  Filename.dirname coqbin

(** [check_file_else ~dir ~file oth] checks if [file] exists in
    the installation directory [dir] given relatively to [coqroot],
    which maybe has been relocated.
    If the check fails, then [oth ()] is evaluated.
    Using file system equality seems well enough for this heuristic *)
let check_file_else ~dir ~file oth =
  let path = use_suffix coqroot dir in
  if Sys.file_exists (Filename.concat path file) then path else oth ()

let guess_coqlib () =
  match Util.getenv_rocq "LIB" with
  | Some v -> v
  | None ->
    check_file_else
      ~dir:Coq_config.coqlibsuffix
      ~file:prelude
      (fun () ->
         if Sys.file_exists (Filename.concat Coq_config.coqlib prelude)
         then Coq_config.coqlib
         else fail ())

(* Build layout uses coqlib = coqcorelib *)
let guess_coqcorelib lib =
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

(* Should we fail on double initialization? That seems a way to avoid
   mis-use for example when we pass command line arguments *)
let init () =
  let lib = guess_coqlib () in
  let core =
    match Util.getenv_rocq_gen ~rocq:"ROCQRUNTIMELIB" ~coq:"COQCORELIB" with
    | Some v -> v
    | None -> guess_coqcorelib lib
  in
  validate_env { core ; lib }

let env_ref = ref None

let init () =
  match !env_ref with
  | None ->
    let env = init () in
    env_ref := Some env; env
  | Some env -> env

let set_coqlib lib =
  let env = validate_env { lib; core = guess_coqcorelib lib } in
  env_ref := Some env

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
  let path = use_suffix coqroot Coq_config.docdirsuffix in
  if Sys.file_exists path then path else Coq_config.docdir

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

let print_query usage : Usage.query -> unit = function
  | PrintVersion -> Usage.version ()
  | PrintMachineReadableVersion -> Usage.machine_readable_version ()
  | PrintWhere ->
    let env = init () in
    let coqlib = coqlib env |> Path.to_string in
    print_endline coqlib
  | PrintHelp -> begin match usage with
      | Some usage -> Usage.print_usage stderr usage
      | None -> assert false
    end
  | PrintConfig ->
    let env = init() in
    print_config env stdout

let query_needs_env : Usage.query -> bool = function
  | PrintVersion | PrintMachineReadableVersion | PrintHelp -> false
  | PrintWhere | PrintConfig -> true
