(*
 * This file defines our persistent counter, which we use in the
 * CountPersistent command.
 *)

(*
 * Increment the persistent counter
 *)
val increment : unit -> unit

(*
 * Determine the value of the persistent counter
 *)
val value : unit -> int
