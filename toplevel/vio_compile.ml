(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Coqcargs
open Compiler.Common_compile

(******************************************************************************)
(* VIO Dispatching                                                            *)
(******************************************************************************)
let check_vio_tasks copts =
  Flags.async_proofs_worker_id := "VioChecking";
  let rc =
    List.fold_left (fun acc (n,f) ->
        let f_in = ensure ~ext:".vio" ~src:f ~tgt:f in
        ensure_exists f_in;
        Vio_checking.check_vio (n,f_in) && acc)
      true copts.vio_tasks in
  if not rc then fatal_error Pp.(str "VIO Task Check failed")

(* vio files *)
let schedule_vio copts =
  let l =
    List.map (fun f -> let f_in = ensure ~ext:".vio" ~src:f ~tgt:f in ensure_exists f_in; f_in)
      copts.vio_files in
  if copts.vio_checking then
    Vio_checking.schedule_vio_checking copts.vio_files_j l
  else
    Vio_checking.schedule_vio_compilation copts.vio_files_j l

let do_vio opts copts _injections =
  (* Vio compile pass *)
  if copts.vio_files <> [] then schedule_vio copts;
  (* Vio task pass *)
  if copts.vio_tasks <> [] then check_vio_tasks copts
