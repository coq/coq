(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception Empty

type 'a t = {
  face : 'a list;
  rear : 'a list;
  lenf : int;
  lenr : int;
}

let rec split i accu l = match l with
| [] ->
  if Int.equal i 0 then (accu, []) else invalid_arg "split"
| t :: q ->
  if Int.equal i 0 then (accu, l)
  else split (pred i) (t :: accu) q

let balance q =
  let avg = (q.lenf + q.lenr) / 2 in
  let dif = q.lenf + q.lenr - avg in
  if q.lenf > succ (2 * q.lenr) then
    let (ff, fr) = split avg [] q.face in
    { face = List.rev ff ; rear = q.rear @ List.rev fr; lenf = avg; lenr = dif }
  else if q.lenr > succ (2 * q.lenf) then
    let (rf, rr) = split avg [] q.rear in
    { face = q.face @ List.rev rr ; rear = List.rev rf; lenf = dif; lenr = avg }
  else q

let empty = {
  face = [];
  rear = [];
  lenf = 0;
  lenr = 0;
}

let lcons x q =
  balance { q with lenf = succ q.lenf; face = x :: q.face }

let lhd q = match q.face with
| [] ->
  begin match q.rear with
  | [] -> raise Empty
  | t :: _ -> t
  end
| t :: _ -> t

let ltl q = match q.face with
| [] ->
  begin match q.rear with
  | [] -> raise Empty
  | t :: _ -> empty
  end
| t :: r -> balance { q with lenf = pred q.lenf; face = r }

let rcons x q =
  balance { q with lenr = succ q.lenr; rear = x :: q.rear }

let rhd q = match q.rear with
| [] ->
  begin match q.face with
  | [] -> raise Empty
  | t :: r -> t
  end
| t :: _ -> t

let rtl q = match q.rear with
| [] ->
  begin match q.face with
  | [] -> raise Empty
  | t :: r -> empty
  end
| t :: r ->
  balance { q with lenr = pred q.lenr; rear = r }

let rev q = {
  face = q.rear;
  rear = q.face;
  lenf = q.lenr;
  lenr = q.lenf;
}

let length q = q.lenf + q.lenr

let is_empty q = Int.equal (length q) 0

let filter f q =
  let fold (accu, len) x = if f x then (x :: accu, succ len) else (accu, len) in
  let (rf, lenf) = List.fold_left fold ([], 0) q.face in
  let (rr, lenr) = List.fold_left fold ([], 0) q.rear in
  balance { face = List.rev rf; rear = List.rev rr; lenf = lenf; lenr = lenr }
