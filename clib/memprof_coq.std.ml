let is_interrupted _ = false [@@inline]

module Resource_bind = struct
  let ( let& ) f scope = f ~scope
end

(* We do our own Mutex_aux for OCaml 5.x *)
module Mutex_aux = Mutex_aux

module Thread_map_core = struct
  open Resource_bind

  module IMap = Map.Make (
    struct
      type t = int
      let compare = Stdlib.compare
    end)

  type 'a t = { mutex : Mutex.t ; mutable map : 'a IMap.t }

  let create () = { mutex = Mutex.create () ; map = IMap.empty }

  let current_thread () = Thread.id (Thread.self ())

  let get s =
    (* Concurrent threads do not alter the value for the current
       thread, so we do not need a lock. *)
    IMap.find_opt (current_thread ()) s.map

  (* For set and clear we need a lock *)

  let set s v =
    let& () = Mutex_aux.with_lock s.mutex in
    let new_map = match v with
      | None -> IMap.remove (current_thread ()) s.map
      | Some v -> IMap.add (current_thread ()) v s.map
    in
    s.map <- new_map

  let _clear s =
    let& () = Mutex_aux.with_lock s.mutex in
    s.map <- IMap.empty
end

module Masking = struct

  (* There's no mechanism to block OCaml's async exceptions,
     so without memprof there is nothing interesting to do. *)
  let with_resource ~acquire arg ~scope ~(release : _ -> unit) =
    let r = acquire arg in
    Fun.protect ~finally:(fun () -> release r) (fun () -> scope r)

end

module Thread_map = struct
  include Thread_map_core

  let with_value tls ~value ~scope =
    let old_value = get tls in
    (* FIXME: needs proper masking here as there is a race between
       resources and asynchronous exceptions. For now, it is
       exception-safe only for exceptions arising from Memprof_callbacks. *)
    Masking.with_resource
      ~acquire:(fun () -> set tls (Some value)) ()
      ~scope
      ~release:(fun () -> set tls old_value)

end
