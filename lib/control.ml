(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*s interruption *)

let interrupt = ref false

let steps = ref 0

let are_we_threading = lazy (
  match !Flags.async_proofs_mode with
  | Flags.APon -> true
  | _ -> false)

let check_for_interrupt () =
  if !interrupt then begin interrupt := false; raise Sys.Break end;
  incr steps;
  if !steps = 1000 && Lazy.force are_we_threading then begin
    Thread.delay 0.001;
    steps := 0;
  end

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
    Exninfo.iraise e

let windows_timeout n f e =
  let killed = ref false in
  let exited = ref false in
  let thread init =
    while not !killed do
      let cur = Unix.time () in
      if float_of_int n <= cur -. init then begin
        interrupt := true;
        exited := true;
        Thread.exit ()
      end;
      Thread.delay 0.5
    done
  in
  let init = Unix.time () in
  let _id = Thread.create thread init in
  try
    let res = f () in
    let () = killed := true in
    let cur = Unix.time () in
    (** The thread did not interrupt, but the computation took longer than
        expected. *)
    let () = if float_of_int n <= cur -. init then begin
      exited := true;
      raise Sys.Break
    end in
    res
  with
  | Sys.Break ->
    (** Just in case, it could be a regular Ctrl+C *)
    if not !exited then begin killed := true; raise Sys.Break end
    else raise e
  | e ->
    let () = killed := true in
    let e = Backtrace.add_backtrace e in
    Exninfo.iraise e

type timeout = { timeout : 'a. int -> (unit -> 'a) -> exn -> 'a }

let timeout_fun = match Sys.os_type with
| "Unix" | "Cygwin" -> ref { timeout = unix_timeout }
| _ -> ref { timeout = windows_timeout }

let set_timeout f = timeout_fun := f

let timeout n f e = !timeout_fun.timeout n f e
