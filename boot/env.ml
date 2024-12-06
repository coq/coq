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

(* For now just a pointer to coq/lib (for .vo) and coq-core/lib (for plugins)  *)
type t =
  { core: Path.t
  ; lib : Path.t
  }

(* fatal error *)
let fail_msg =
  "cannot guess a path for Coq libraries; please use -coqlib option \
   or ensure you have installed the package containing Coq's prelude (rocq-core in OPAM) \
   If you intend to use Coq without prelude, the -boot -noinit options must be used."

let fail s = Format.eprintf "%s@\n%!" fail_msg; exit 1

(* This code needs to be refactored, for now it is just what used to be in envvars  *)

let theories_dir = "theories"
let plugins_dir = "plugins"
let prelude = Filename.concat theories_dir "Init/Prelude.vo"

let guess_coqlib () =
  Util.getenv_else "COQLIB" (fun () ->
  Util.check_file_else
    ~dir:Coq_config.coqlibsuffix
    ~file:prelude
    (fun () ->
      if Sys.file_exists (Filename.concat Coq_config.coqlib prelude)
      then Coq_config.coqlib
      else fail ()))

(* Build layout uses coqlib = coqcorelib *)
let guess_coqcorelib lib =
  if Sys.file_exists (Path.relative lib plugins_dir)
  then lib
  else Path.relative lib "../coq-core"

let fail_lib lib =
  let open Printf in
  eprintf "File not found: %s\n" lib;
  eprintf "The path for Coq libraries is wrong.\n";
  eprintf "Coq prelude is shipped in the rocq-core package.\n";
  eprintf "Please check the COQLIB env variable or the -coqlib option.\n";
  exit 1

let fail_core plugin =
  let open Printf in
  eprintf "File not found: %s\n" plugin;
  eprintf "The path for Coq plugins is wrong.\n";
  eprintf "Coq plugins are shipped in the coq-core package.\n";
  eprintf "Please check the COQCORELIB env variable.\n";
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
  let core = Util.getenv_else "COQCORELIB"
      (fun () -> guess_coqcorelib lib) in
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
