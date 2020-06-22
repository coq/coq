(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* This API is loosely inspired by [Stdune.Path], for now we keep it
   minimal, but at some point we may extend it, see developer notes in
   the implementation file. *)

type t = string

(* Note that in general, make is not safe, due to its type, however
   relative is as you can enforce a particular root. So we eventually
   should remove [make] *)
let make = List.fold_left Filename.concat ""

let relative = Filename.concat

let rec choose_existing = function
  | [] -> None
  | f :: fs ->
    if Sys.file_exists f then Some f else choose_existing fs
