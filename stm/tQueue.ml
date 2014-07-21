(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

module PriorityQueue : sig
  type 'a t
  val create : unit -> 'a t
  val set_rel : ('a -> 'a -> int) -> 'a t -> unit
  val is_empty : 'a t -> bool
  val pop : 'a t -> 'a
  val push : 'a -> 'a t -> unit
  val clear : 'a t -> unit
end = struct
  type 'a item = int * 'a
  type 'a rel = 'a item -> 'a item -> int
  type 'a t = ('a item list * 'a rel) ref
  let sort_timestamp (i,_) (j,_) = i - j
  let age = ref 0
  let create () = ref ([],sort_timestamp)
  let is_empty t = fst !t = []
  let pop ({ contents = (l, rel) } as t) =
    match l with
    | [] -> raise Queue.Empty
    | (_,x) :: xs -> t := (xs, rel); x
  let push x ({ contents = (xs, rel) } as t) =
    incr age;
    (* re-roting the whole list is not the most efficient way... *)
    t := (List.sort rel (xs @ [!age,x]), rel)
  let clear ({ contents = (l, rel) } as t) = t := ([], rel)
  let set_rel rel ({ contents = (xs, _) } as t) =
    let rel (_,x) (_,y) = rel x y in
    t := (List.sort rel xs, rel)
end

type 'a t = {
  queue: 'a PriorityQueue.t;
  lock : Mutex.t;
  cond : Condition.t;
  mutable nwaiting : int;
  cond_waiting : Condition.t;
  mutable release : bool;
}

exception BeingDestroyed

let create () = {
  queue = PriorityQueue.create ();
  lock = Mutex.create ();
  cond = Condition.create ();
  nwaiting = 0;
  cond_waiting = Condition.create ();
  release = false;
}

let pop ({ queue = q; lock = m; cond = c; cond_waiting = cn } as tq) =
  if tq.release then raise BeingDestroyed;
  Mutex.lock m;
  while PriorityQueue.is_empty q do
    tq.nwaiting <- tq.nwaiting + 1;
    Condition.signal cn;
    Condition.wait c m;
    tq.nwaiting <- tq.nwaiting - 1;
    if tq.release then (Mutex.unlock m; raise BeingDestroyed)
  done;
  let x = PriorityQueue.pop q in
  Condition.signal c;
  Condition.signal cn;
  Mutex.unlock m;
  x

let push { queue = q; lock = m; cond = c; release } x =
  if release then Errors.anomaly(Pp.str
    "TQueue.push while being destroyed! Only 1 producer/destroyer allowed");
  Mutex.lock m;
  PriorityQueue.push x q;
  Condition.signal c;
  Mutex.unlock m

let clear { queue = q; lock = m; cond = c } =
  Mutex.lock m;
  PriorityQueue.clear q;
  Mutex.unlock m

let is_empty { queue = q } = PriorityQueue.is_empty q

let destroy tq =
  tq.release <- true;
  while tq.nwaiting > 0 do
    Mutex.lock tq.lock;
    Condition.signal tq.cond;
    Mutex.unlock tq.lock;
  done;
  tq.release <- false

let wait_until_n_are_waiting_and_queue_empty j tq =
  Mutex.lock tq.lock;
  while not (PriorityQueue.is_empty tq.queue) || tq.nwaiting < j do
    Condition.wait tq.cond_waiting tq.lock
  done;
  Mutex.unlock tq.lock

let dump { queue; lock } =
  let l = ref [] in
  Mutex.lock lock;
  while not (PriorityQueue.is_empty queue) do
    l := PriorityQueue.pop queue :: !l
  done;
  Mutex.unlock lock;
  List.rev !l

let set_order tq rel =
  Mutex.lock tq.lock;
  PriorityQueue.set_rel rel tq.queue;
  Mutex.unlock tq.lock
