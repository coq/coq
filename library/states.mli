
(* $Id$ *)

(*s States of the system. In that module, we provide functions to get
  and set the state of the whole system. Internally, it is done by
  freezing the states of both [Lib] and [Summary]. We provide functions 
  to write and restore state to and from a given file. *)

val intern_state : string -> unit
val extern_state : string -> unit

(*s Rollback. [with_heavy_rollback f x] applies [f] to [x] and restores the
  state of the whole system as it was before the evaluation if an exception 
  is raised. *)

val with_heavy_rollback : ('a -> 'b) -> 'a -> 'b


