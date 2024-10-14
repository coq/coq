(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let copy src dst =
  let cin = open_in src in
  try
    let cout = open_out dst in
    try
      while true do
        output_char cout (input_char cin)
      done
    with End_of_file -> close_out cout; close_in cin
  with Sys_error e -> Printf.eprintf "%s\n" e; exit 1

let check_if_file_exists f =
  if not (Sys.file_exists f) then begin
    Printf.eprintf "coqdoc: %s: no such file\n" f;
    exit 1
  end

(* [files_from_file f] returns the list of file names contained in the
   file named [f]. These file names must be separated by spaces,
   tabulations or newlines. *)
let files_from_file f =
  let files_from_channel ch =
    let buf = Buffer.create 80 in
    let l = ref [] in
    try
      while true do
        match input_char ch with
        | ' ' | '\t' | '\n' ->
          if Buffer.length buf > 0 then l := Buffer.contents buf :: !l;
          Buffer.clear buf
        | c -> Buffer.add_char buf c
      done;
      []
    with End_of_file -> List.rev !l
  in
  try
    check_if_file_exists f;
    let ch = open_in f in
    let l = files_from_channel ch in
    close_in ch; l
  with Sys_error s ->
    Printf.eprintf "coqdoc: cannot read from file %s (%s)\n" f s;
    exit 1
