(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a getter = unit -> 'a
type 'a installer = ('a getter) -> unit

let new_counter a ~incr ~build =
  let data = ref a in
  let m = Mutex.create () in
  let mk_thsafe_getter f () =
    (* - slaves must use a remote counter getter, not this one! *)
    (* - in the main process there is a race condition between slave
         managers (that are threads) and the main thread, hence the mutex *)
    if !Flags.coq_slave_mode > 0 then
      Errors.anomaly(Pp.str"Slave processes must install remote counters");
    Mutex.lock m; let x = f () in Mutex.unlock m;
    build x in
  let getter = ref (mk_thsafe_getter (fun () -> data := incr !data; !data)) in
  let installer f =
    if !Flags.coq_slave_mode < 1 then
      Errors.anomaly(Pp.str"Only slave processes can install a remote counter")
    else getter := f in
  (fun () -> !getter ()), installer

