(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a getter = unit -> 'a
type 'a installer = ('a getter) -> unit

type remote_counters_status = (string * Obj.t) list

let counters : remote_counters_status ref = ref []

let (!!) x = !(!x)

let new_counter ~name a ~incr ~build =
  assert(not (List.mem_assoc name !counters));
  let data = ref (ref a) in
  counters := (name, Obj.repr data) :: !counters;
  let m = Mutex.create () in
  let mk_thsafe_local_getter f () =
    (* - slaves must use a remote counter getter, not this one! *)
    (* - in the main process there is a race condition between slave
         managers (that are threads) and the main thread, hence the mutex *)
    if Flags.async_proofs_is_worker () then
      CErrors.anomaly(Pp.str"Slave processes must install remote counters.");
    Mutex.lock m; let x = f () in Mutex.unlock m;
    build x in
  let mk_thsafe_remote_getter f () =
    Mutex.lock m; let x = f () in Mutex.unlock m; x in
  let getter = ref(mk_thsafe_local_getter (fun () -> !data := incr !!data; !!data)) in
  let installer f =
    if not (Flags.async_proofs_is_worker ()) then
      CErrors.anomaly(Pp.str"Only slave processes can install a remote counter.");
    getter := mk_thsafe_remote_getter f in
  (fun () -> !getter ()), installer

let backup () = !counters

let snapshot () =
  List.map (fun (n,v) -> n, Obj.repr (ref (ref !!(Obj.obj v)))) !counters

let restore l =
  List.iter (fun (name, data) ->
    assert(List.mem_assoc name !counters);
    let dataref = Obj.obj (List.assoc name !counters) in
    !dataref := !!(Obj.obj data))
  l
