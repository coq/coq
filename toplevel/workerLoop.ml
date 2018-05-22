(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let rec parse = function
  | "--xml_format=Ppcmds" :: rest -> parse rest
  | x :: rest -> x :: parse rest
  | [] -> []

let arg_init init ~opts extra_args =
  let extra_args = parse extra_args in
  Flags.quiet := true;
  init ();
  CoqworkmgrApi.(init !async_proofs_worker_priority);
  opts, extra_args

let start ~init ~loop =
  let open Coqtop in
  let custom = {
    init = arg_init init;
    run = (fun ~opts:_ ~state:_ -> loop ());
  } in
  start_coq custom
