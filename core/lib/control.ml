(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*s interruption *)

let interrupt = ref false

let steps = ref 0

let enable_thread_delay = ref false

exception Timeout

let check_for_interrupt () =
  if !interrupt then begin interrupt := false; raise Sys.Break end;
  if !enable_thread_delay then begin
    incr steps;
    if !steps = 1000 then begin
      Thread.delay 0.001;
      steps := 0;
    end
  end

(** This function does not work on windows, sigh... *)
(* This function assumes it is the only function calling [setitimer] *)
let unix_timeout n f x =
  let open Unix in
  let timeout_handler _ = raise Timeout in
  let old_timer = getitimer ITIMER_REAL in
  (* Here we assume that the existing timer will also interrupt us. *)
  if old_timer.it_value > 0. && old_timer.it_value <= n then Some (f x) else
    let psh = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
    let old_timer = setitimer ITIMER_REAL {it_interval = 0.; it_value = n} in
    let restore_timeout () =
      let timer_status = getitimer ITIMER_REAL in
      let old_timer_value = old_timer.it_value -. n +. timer_status.it_value in
      (* We want to make sure that the parent timer triggers, even if somehow the parent timeout
         has already passed. This should not happen, but due to timer imprecision it can happen in practice *)
      let old_timer_value = if old_timer.it_value <= 0. then 0. else
          (if old_timer_value <= 0. then epsilon_float else old_timer_value) in
      let _ = setitimer ITIMER_REAL { old_timer with it_value = old_timer_value } in
      Sys.set_signal Sys.sigalrm psh
    in
    try
      let res = f x in
      restore_timeout ();
      Some res
    with
    | Timeout ->
      restore_timeout ();
      None
    | e ->
      let e = Exninfo.capture e in
      restore_timeout ();
      Exninfo.iraise e

let windows_timeout n f x =
  let killed = ref false in
  let exited = ref false in
  let thread init =
    while not !killed do
      let cur = Unix.gettimeofday () in
      if n <= cur -. init then begin
        interrupt := true;
        exited := true;
        Thread.exit ()
      end;
      Thread.delay 0.5
    done
  in
  let init = Unix.gettimeofday () in
  let _id = CThread.create thread init in
  try
    let res = f x in
    let () = killed := true in
    let cur = Unix.gettimeofday () in
    (* The thread did not interrupt, but the computation took longer than
       expected. *)
    let () = if n <= cur -. init then begin
      exited := true;
      raise Sys.Break
    end in
    Some res
  with
  | Sys.Break ->
    (* Just in case, it could be a regular Ctrl+C *)
    if not !exited then begin killed := true; raise Sys.Break end
    else None
  | e ->
    let e = Exninfo.capture e in
    let () = killed := true in
    Exninfo.iraise e

type timeout = { timeout : 'a 'b. float -> ('a -> 'b) -> 'a -> 'b option }

let timeout_fun = match Sys.os_type with
| "Unix" | "Cygwin" -> { timeout = unix_timeout }
| _ -> { timeout = windows_timeout }

let timeout_fun_ref = ref timeout_fun
let set_timeout f = timeout_fun_ref := f

let timeout n f = !timeout_fun_ref.timeout n f

let protect_sigalrm f x =
  let timed_out = ref false in
  let timeout_handler _ = timed_out := true in
  try
    let old_handler = Sys.signal Sys.sigalrm (Sys.Signal_handle timeout_handler) in
    try
      let res = f x in
      Sys.set_signal Sys.sigalrm old_handler;
      match !timed_out, old_handler with
      | true, Sys.Signal_handle f -> f Sys.sigalrm; res
      | _, _ -> res
    with e ->
      let e = Exninfo.capture e in
      Sys.set_signal Sys.sigalrm old_handler;
      Exninfo.iraise e
  with Invalid_argument _ -> (* This happens on Windows, as handling SIGALRM does not seem supported *)
    f x
