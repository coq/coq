(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s interruption *)

let interrupt = ref false

let check_for_interrupt () =
  if !interrupt then begin interrupt := false; raise Sys.Break end

(** This function does not work on windows, sigh... *)
let unix_timeout n f e =
  let timeout_handler _ = raise e in
  let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
  let _ = Unix.alarm n in
  let restore_timeout () =
    let _ = Unix.alarm 0 in
    Sys.set_signal Sys.sigalrm psh
  in
  try
    let res = f () in
    restore_timeout ();
    res
  with e ->
    let e = Backtrace.add_backtrace e in
    restore_timeout ();
    raise e

type timeout = { timeout : 'a. int -> (unit -> 'a) -> exn -> 'a }

let timeout_fun = ref { timeout = unix_timeout }

let set_timeout f = timeout_fun := f

let timeout n f e = !timeout_fun.timeout n f e
