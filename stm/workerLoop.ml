(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

let rec parse = function
  | "--xml_format=Ppcmds" :: rest -> parse rest
  | x :: rest -> x :: parse rest
  | [] -> []

let loop init args =
  let args = parse args in
  Flags.quiet := true;
  init ();
  CoqworkmgrApi.init !Flags.async_proofs_worker_priority;
  args
