(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let parse_env_line l =
  try Scanf.sscanf l "%[^=]=%S" (fun name value -> Some(name,value))
  with _ -> None

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
        | Some(n,v) when n = name -> v
        | _ -> find ()
      in
        find ())
  with
  | Sys_error s -> raise Not_found
  | End_of_file -> raise Not_found


let system_getenv name =
  try Sys.getenv name with Not_found -> getenv_from_file name

let getenv_else s dft = try system_getenv s with Not_found -> dft ()

(** Add a local installation suffix (unless the suffix is itself
    absolute in which case the prefix does not matter) *)
let use_suffix prefix suffix =
  if String.length suffix > 0 && suffix.[0] = '/'
  then suffix
  else Filename.concat prefix suffix

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
