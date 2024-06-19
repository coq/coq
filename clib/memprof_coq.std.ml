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

  module T = Thread_map_core

  type mask = { mutable on : bool }

  let mask_tls : mask T.t = T.create ()
  (* whether the current thread is masked *)

  let create_mask () =
    let r = { on = false } in
    T.set mask_tls (Some r) ;
    r

  let delete_mask () = T.set mask_tls None

  let is_blocked () =
    match T.get mask_tls with
    | None -> false
    | Some r -> r.on

  let assert_blocked () = assert (is_blocked ())

  (* The current goal is only to protect from those asynchronous
     exceptions raised after dutifully checking that [is_blocked ()]
     evaluates to false, and that expect the asynchronous callback to be
     called again shortly thereafter (e.g. memprof callbacks). There is
     currently no mechanism to delay asynchronous callbacks, so this
     strategy cannot work for other kinds of asynchronous callbacks. *)
  let with_resource ~acquire arg ~scope ~(release : _ -> unit) =
    let mask, delete_after = match T.get mask_tls with
      | None -> create_mask (), true
      | Some r -> r, false
    in
    let old_mask = mask.on in
    let remove_mask () =
      (* remove the mask flag from the TLS to avoid it growing
         uncontrollably when there are lots of threads. *)
      if delete_after then delete_mask () else mask.on <- old_mask
    in
    let release_and_unmask r x =
      match release r with
      | () -> remove_mask () ; x
      | exception e -> remove_mask () ; raise e
    in
    mask.on <- true ;
    let r = try acquire arg with
      | e -> mask.on <- old_mask ; raise e
    in
    match
      mask.on <- old_mask ;
      scope r
    with
    | (* BEGIN ATOMIC *) y -> (
        mask.on <- true ;
        (* END ATOMIC *)
        release_and_unmask r y
      )
    | (* BEGIN ATOMIC *) exception e -> (
        mask.on <- true ;
        (* END ATOMIC *)
        match Printexc.get_raw_backtrace () with
        | bt -> (
            let e = release_and_unmask r e in
            Printexc.raise_with_backtrace e bt
          )
        | exception Out_of_memory -> raise (release_and_unmask r e)
      )

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
