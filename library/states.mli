
(* $Id$ *)

(*s States of the system. *)

type state

val intern_state : string -> unit
val extern_state : string -> unit

(*s Rollback. [with_heavy_rollback f x] applies [f] to [x] and restores the
  state of the whole system as it was before the evaluation if an exception 
  is raised. *)

val with_heavy_rollback : ('a -> 'b) -> 'a -> 'b


