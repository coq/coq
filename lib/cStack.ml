(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

exception Empty = Stack.Empty

type 'a t = {
  mutable stack : 'a list;
}

let create () = { stack = [] }

let push x s = s.stack <- x :: s.stack

let pop = function
  | { stack = [] } -> raise Stack.Empty
  | { stack = x::xs } as s -> s.stack <- xs; x

let top = function
  | { stack = [] } -> raise Stack.Empty
  | { stack = x::_ } -> x

let to_list { stack = s } = s

let find f s = List.find f (to_list s)

let find_map f s =
  let rec aux = function
  | [] -> raise Not_found
  | x :: xs -> match f x with None -> aux xs | Some i -> i
  in
  aux (to_list s)

type ('b, 'c) seek = ('b, 'c) CSig.seek = Stop of 'b | Next of 'c

let fold_until f accu s =
  let rec aux accu = function
    | [] -> raise Not_found
    | x :: xs -> match f accu x with Stop x -> x | Next i -> aux i xs in
  aux accu s.stack

let is_empty { stack = s } = s = []

let iter f { stack = s } = List.iter f s

let clear s = s.stack <- []

let length { stack = s } = List.length s

