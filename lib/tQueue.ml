(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a t = {
  queue: 'a Queue.t;
  lock : Mutex.t;
  cond : Condition.t;
  mutable nwaiting : int;
  cond_waiting : Condition.t;
}

let create () = {
  queue = Queue.create ();
  lock = Mutex.create ();
  cond = Condition.create ();
  nwaiting = 0;
  cond_waiting = Condition.create ();
}

let pop ({ queue = q; lock = m; cond = c; cond_waiting = cn } as tq) =
  Mutex.lock m;
  while Queue.is_empty q do
    tq.nwaiting <- tq.nwaiting + 1;
    Condition.signal cn;
    Condition.wait c m;
    tq.nwaiting <- tq.nwaiting - 1;
  done;
  let x = Queue.pop q in
  Condition.signal c;
  Condition.signal cn;
  Mutex.unlock m;
  x

let push { queue = q; lock = m; cond = c } x =
  Mutex.lock m;
  Queue.push x q;
  Condition.signal c;
  Mutex.unlock m

let wait_until_n_are_waiting_and_queue_empty j tq =
  Mutex.lock tq.lock;
  while not (Queue.is_empty tq.queue) || tq.nwaiting < j do
    Condition.wait tq.cond_waiting tq.lock
  done;
  Mutex.unlock tq.lock

let dump { queue; lock } =
  let l = ref [] in
  Mutex.lock lock;
  while not (Queue.is_empty queue) do l := Queue.pop queue :: !l done;
  Mutex.unlock lock;
  List.rev !l

let reorder tq rel =
  Mutex.lock tq.lock;
  let l = ref [] in
  while not (Queue.is_empty tq.queue) do l := Queue.pop tq.queue :: !l done;
  List.iter (fun x -> Queue.push x tq.queue) (List.sort rel !l);
  Mutex.unlock tq.lock
