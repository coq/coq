(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type worker = {
  package : string;
  basename : string;
}

let get_worker_path {package; basename} =
  let dir = try Findlib.package_directory package
    with Findlib.No_such_package _ ->
      Printf.eprintf "Error: Could not find package %s.\n%!" package;
      exit 1
  in
  let exe = if Sys.(os_type = "Win32" || os_type = "Cygwin") then ".exe" else "" in
  Filename.concat dir (basename^exe)

type init_opts = {
  boot : bool;
  coqlib : string option;
  ml_includes : string list;
  queries : Boot.Usage.query list;
}

let default_opts = {
  boot = false;
  coqlib = None;
  ml_includes = [];
  queries = [];
}

let add_query q opts = { opts with queries = q :: opts.queries }

let parse_query = let open Boot.Usage in function
  | "-config"|"--config" -> Some PrintConfig
  | "-where" -> Some PrintWhere
  | "-v"|"-version"|"--version" -> Some PrintVersion
  | "-print-version"|"--print-version" -> Some PrintMachineReadableVersion
  | _ -> None

let rec parse_args opts = function
  | [] -> opts
  | "-boot" :: rest -> parse_args {opts with boot = true} rest
  | "-coqlib" :: lib :: rest -> parse_args {opts with coqlib = Some lib} rest
  | "-I" :: ml :: rest -> parse_args {opts with ml_includes = ml :: opts.ml_includes} rest
  | arg :: rest ->
    match parse_query arg with
    | Some q -> parse_args (add_query q opts) rest
    | None -> parse_args opts rest

let parse_args args =
  let opts = parse_args default_opts args in
  let opts = {
    opts with
    ml_includes = List.rev opts.ml_includes;
    queries = List.rev opts.queries;
  }
  in
  opts

let with_ic file f =
  let ic = open_in file in
  try
    let rc = f ic in
    close_in ic;
    rc
  with e -> close_in ic; raise e

let parse_env_line l =
  try Scanf.sscanf l "%[^=]=%S" (fun name value -> Some(name,value))
  with Scanf.Scan_failure _ | End_of_file -> None

(** We [putenv] instead of wrapping [getenv] calls because the
    subprocess also needs the updated env, and usually doesn't have
    the env file next to its binary. *)
let putenv_from_file ~debug () =
  let base = Filename.dirname Sys.executable_name in
  let f = base ^ "/coq_environment.txt" in
  try
    with_ic f (fun ic ->
        let () = if debug then Printf.eprintf "using env vars from %s\n%!" f in
        let rec iter () =
          match input_line ic with
          | exception End_of_file -> ()
          | l ->
            let () = match parse_env_line l with
              | Some(n,v) ->
                begin match Sys.getenv_opt n with
                | None -> Unix.putenv n v
                | Some _ -> ()
                end
              | None -> ()
            in
            iter ()
        in
        iter ())
  with
  | Sys_error s -> ()

let make_ocamlpath envopt opts =
  let boot_ml_path = match envopt with
    | None -> []
    | Some coqenv ->
      Boot.Env.Path.[to_string (relative (Boot.Env.corelib coqenv) "..")]
  in
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let path = List.concat [opts.ml_includes; boot_ml_path; env_ocamlpath] in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  String.concat ocamlpathsep path

let exec_or_create_process prog argv =
  if Sys.os_type <> "Win32" then
    Unix.execv prog argv
  else
    let pid = Unix.create_process prog argv Unix.stdin Unix.stdout Unix.stderr in
    if pid = 0 then begin
      Printf.eprintf "coqc shim: create_process failed\n%!";
      exit 127
    end;
    let _, status = Unix.waitpid [] pid in
    match status with
    | WEXITED n | WSIGNALED n -> exit n
    | WSTOPPED _ ->
      (* is there anything sensible to do with WSTOPPED? can it even happen on windows? *)
      assert false

type opts = { debug_shim : bool }

let parse_opts = function
  | "-debug-shim" :: rest -> { debug_shim = true }, rest
  | args -> { debug_shim = false }, args

let boot_env opts =
  let noenv = match opts.queries with
    | [] -> opts.boot
    | _ :: _ ->
      (* don't trust user-given -boot if the user also passed a query which needs it,
         and don't needlessly initialize the env
         if the user passed only queries which don't need it. *)
      not (List.exists Boot.Env.query_needs_env opts.queries)
  in
  if noenv then None
  else
    let () = Option.iter Boot.Env.set_coqlib opts.coqlib in
    Some (Boot.Env.init ())

let do_queries opts =
  match opts.queries with
  | [] -> ()
  | _ :: _ ->
    List.iter (Boot.Env.print_query None) opts.queries;
    exit 0

let init { debug_shim=debug } args =
  (* important to putenv before reading OCAMLPATH / ROCQLIB *)
  let () = putenv_from_file ~debug () in
  let opts = parse_args args in
  let coqenv = boot_env opts in
  let () = do_queries opts in
  let env_ocamlpath = make_ocamlpath coqenv opts in
  let () = if debug then Printf.eprintf "OCAMLPATH = %s\n%!" env_ocamlpath in
  Findlib.init ~env_ocamlpath ()

let try_run_queries { debug_shim=debug } args =
  let () = putenv_from_file ~debug () in
  let opts = parse_args args in
  match opts.queries with
  | [] -> false
  | _ :: _ ->
    let _coqenv = boot_env opts in
    let () = do_queries opts in
    true
