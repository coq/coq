(* From memprof-limits *)
val is_interrupted : unit -> bool

module Masking : sig

  val with_resource :
    acquire:('a -> 'b) -> 'a -> scope:('b -> 'c) -> release:('b -> unit) -> 'c

end

module Thread_map : sig

  (** An async-safe, scoped thread-local store *)

  type 'a t

  val create : unit -> 'a t
  (** Create an empty map *)

  val with_value : 'a t -> value:'a -> scope:(unit -> 'b) -> 'b
  (** Associate [~value] to the current thread for the duration of a scope.
      It can be nested: the previous association is restored on exit. *)

  val get : 'a t -> 'a option
  (** Get the value currently associated with the current thread. *)

end

module Resource_bind : sig
  (** Open {!Memprof_limits.Resource_bind} to enable the [let&] binder
      for resources. *)

  val ( let& ) : (scope:('a -> 'b) -> 'b) -> ('a -> 'b) -> 'b
(** RAII-style notation for resources cleaned-up at the end of
    scope. Example:
    {[open Memprof_limits.Resource_bind

      let with_my_resource x =
        Memprof_limits.Masking.with_resource ~acquire x ~release

      let f x =
        let& resource = with_my_resource x in
        …]} *)
end

module Mutex_aux : sig

  val with_lock : Mutex.t -> scope:(unit -> 'a) -> 'a

end
