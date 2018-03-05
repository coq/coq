(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

let find_map f s = CList.find_map f s.stack

let fold_until f accu s = CList.fold_left_until f accu s.stack

let is_empty { stack = s } = s = []

let iter f { stack = s } = List.iter f s

let clear s = s.stack <- []

let length { stack = s } = List.length s

