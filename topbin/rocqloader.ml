(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let debug_loader = ref false

let ppdebug fmt =
  if !debug_loader then Printf.eprintf fmt
  else Printf.ifprintf stderr fmt

type init_opts = {
  boot : bool;
  coqlib : string option;
  ml_includes : string list;
}

let default_opts = {
  boot = false;
  coqlib = None;
  ml_includes = [];
}

let rec parse_args opts = function
  | [] -> opts
  | "-boot" :: rest -> parse_args {opts with boot = true} rest
  | "-coqlib" :: lib :: rest -> parse_args {opts with coqlib = Some lib} rest
  | "-I" :: ml :: rest -> parse_args {opts with ml_includes = ml :: opts.ml_includes} rest
  | _ :: rest -> parse_args opts rest

let parse_args args =
  let opts = parse_args default_opts args in
  let opts = { opts with ml_includes = List.rev opts.ml_includes } in
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
let putenv_from_file () =
  let base = Filename.dirname Sys.executable_name in
  let f = base ^ "/coq_environment.txt" in
  try
    with_ic f (fun ic ->
        let () = ppdebug "using env vars from %s\n%!" f in
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

let make_ocamlpath opts =
  let boot_ml_path =
    if opts.boot then []
    else
      let () = Option.iter Boot.Env.set_coqlib opts.coqlib in
      let coqenv = Boot.Env.init () in
      Boot.Env.Path.[to_string (relative (Boot.Env.corelib coqenv) "..")]
  in
  let env_ocamlpath =
    try [Sys.getenv "OCAMLPATH"]
    with Not_found -> []
  in
  let path = List.concat [opts.ml_includes; boot_ml_path; env_ocamlpath] in
  let ocamlpathsep = if Sys.unix then ":" else ";" in
  String.concat ocamlpathsep path

let init args =
  let args = match args with
    | "-debug-loader" :: args -> debug_loader := true; args
    | _ -> args
  in
  (* important to putenv before reading OCAMLPATH / COQLIB *)
  let () = putenv_from_file () in
  let opts = parse_args args in
  let env_ocamlpath = make_ocamlpath opts in
  let () = ppdebug "OCAMLPATH = %s\n%!" env_ocamlpath in
  Findlib.init ~env_ocamlpath ();
  args

let load_and_run package args =
  Dynlink.allow_unsafe_modules true;
  Fl_dynload.load_packages ~debug:!debug_loader [package];
  !Rocqshim.run args
