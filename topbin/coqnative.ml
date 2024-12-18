(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Rocqshim

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let opts, args = Rocqshim.parse_opts args in
  let () = Rocqshim.init opts args in
  let prog = get_worker_path { package = "rocq-runtime"; basename = "rocqnative" } in
  let () = if opts.debug_shim then Printf.eprintf "Using %s\n%!" prog in
  let argv = Array.of_list (prog :: args) in
  exec_or_create_process prog argv
