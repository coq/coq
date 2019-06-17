(*
 * This file defines our counter, which we use in the Count command.
 *)

(*
 * Our counter is simply a reference called "counter" to an integer.
 *
 * Summary.ref behaves like ref, but also registers a summary to Coq.
 *)
let counter = Summary.ref ~name:"counter" 0

(*
 * We can increment our counter:
 *)
let increment () =
  counter := succ !counter

(*
 * We can also read the value of our counter:
 *)
let value () =
  !counter
