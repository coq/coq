(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let parse_env_line l =
  try Scanf.sscanf l "%[^=]=%S" (fun name value -> Some(name,value))
  with Scanf.Scan_failure _ | End_of_file -> None

let with_ic file f =
  let ic = open_in file in
  try
    let rc = f ic in
    close_in ic;
    rc
  with e -> close_in ic; raise e

let getenv_from_file name =
  let base = Filename.dirname Sys.executable_name in
  try
    with_ic (base ^ "/coq_environment.txt") (fun ic ->
      let rec find () =
        let l = input_line ic in
        match parse_env_line l with
        | Some(n,v) when n = name -> Some v
        | _ -> find ()
      in
        find ())
  with
  | Sys_error s -> None
  | End_of_file -> None


let getenv_opt name =
  match Sys.getenv_opt name with
  | Some _ as v -> v
  | None -> getenv_from_file name

let warn_deprecated_coq_var = ref (fun ~rocq ~coq ->
    Printf.eprintf "Deprecated environment variable %s, use %s instead.\n%!" coq rocq)

let set_warn_deprecated_coq_var f = warn_deprecated_coq_var := f

let warn_deprecated_coq_var ~rocq ~coq = !warn_deprecated_coq_var ~rocq ~coq

let getenv_rocq_gen ~rocq ~coq =
  match getenv_opt rocq with
  | Some _ as  v -> v
  | None ->
    match getenv_opt coq with
    | Some _ as v ->
      warn_deprecated_coq_var ~rocq ~coq;
      v
    | None -> None

let getenv_rocq name =
  getenv_rocq_gen ~rocq:("ROCQ"^name) ~coq:("COQ"^name)
