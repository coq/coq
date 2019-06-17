(*
 * This file defines our persistent counter, which we use in the
 * CountPersistent command.
 *)

(*
 * At its core, our persistent counter looks exactly the same as
 * our non-persistent counter (with a different name to prevent collisions):
 *)
let counter = Summary.ref ~name:"persistent_counter" 0

(*
 * The difference is that we need to declare it as a persistent object
 * using Libobject.declare_object. To do that, we define a function that
 * saves the value that is passed to it into the reference we have just defined:
 *)
let cache_count (_, v) =
  counter := v

(*
 * We then use declare_object to create a function that takes an integer value
 * (the type our counter refers to) and creates a persistent object from that
 * value:
 *)
let declare_counter : int -> Libobject.obj =
  let open Libobject in
  declare_object
    {
      (default_object "COUNTER") with
      cache_function = cache_count;
      load_function = (fun _ -> cache_count);
    }
(*
 * See Libobject for more information on what other information you
 * can pass here, and what all of these functions mean.
 *
 * For example, if we passed the same thing that we pass to load_function
 * to open_function, then our last call to Count Persistent in Count.v
 * would return 4 and not 6.
 *)

(*
 * Incrementing our counter looks almost identical:
 *)
let increment () =
  Lib.add_anonymous_leaf (declare_counter (succ !counter))
(*
 * except that we must call our declare_counter function to get a persistent
 * object. We then pass this object to Lib.add_anonymous_leaf.
 *)

(*
 * Reading a value does not change at all:
 *)
let value () =
  !counter
