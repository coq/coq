(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Default priority *)
open CoqworkmgrApi
let async_proofs_worker_priority = ref Low

let rec parse = function
  | "--xml_format=Ppcmds" :: rest -> parse rest
  | x :: rest -> x :: parse rest
  | [] -> []

let loop init _coq_args extra_args =
  let args = parse extra_args in
  Flags.quiet := true;
  init ();
  CoqworkmgrApi.init !async_proofs_worker_priority;
  args
