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
  mutable context : ('a list * 'a list) option
}

let create () = { stack = []; context = None }

let push x s = s.stack <- x :: s.stack

let pop = function
  | { stack = [] } -> raise Stack.Empty
  | { stack = x::xs } as s -> s.stack <- xs; x

let tip = function
  | { stack = [] } -> raise Stack.Empty
  | { stack = x::_ } -> x

let to_list = function
  | { context = None; stack = s } -> s
  | { context = Some (a,b); stack = s } -> a @ s @ b

let to_lists = function
  | { context = None; stack = s } -> [],s,[]
  | { context = Some (a,b); stack = s } -> a,s,b

let find f s =
  let a, s, b = to_lists s in
  try List.find (fun x -> f x false) a with Not_found ->
  try List.find (fun x -> f x true)  s with Not_found ->
      List.find (fun x -> f x false) b

let find_map f s =
  let rec aux b = function
  | [] -> raise Not_found
  | x :: xs -> match f x b with None -> aux b xs | Some i -> i
  in
  let a, s, b = to_lists s in
  try aux false a with Not_found -> 
  try aux true s  with Not_found -> 
      aux false b

type ('b, 'c) seek = ('b, 'c) CSig.seek = Stop of 'b | Next of 'c

let fold_until f accu s =
  let rec aux accu = function
    | [] -> raise Not_found
    | x :: xs -> match f accu x with Stop x -> x | Next i -> aux i xs in
  aux accu s.stack

let is_empty = function
  | { stack = []; context = None } -> true
  | _ -> false

let iter f = function
  | { stack = s; context = None } -> List.iter (fun x -> f x true) s
  | { stack = s; context = Some(a,b) } ->
        List.iter (fun x -> f x false) a;
        List.iter (fun x -> f x true)  s;
        List.iter (fun x -> f x false) b

let clear s = s.stack <- []; s.context <- None

let length = function
  | { stack = s; context = None } -> List.length s
  | { stack = s; context = Some(a,b) } ->
        List.length a + List.length s + List.length b

let focus s ~cond_top:c_start ~cond_bot:c_stop =
  if s.context <> None then raise (Invalid_argument "CStack.focus");
  let rec aux (a,s,b) grab = function
    | [] -> raise (Invalid_argument "CStack.focus")
    | x::xs when not grab ->
        if c_start x then aux (a,s,b) true (x::xs)
        else aux (x::a,s,b) grab xs
    | x::xs ->
        if c_stop x then a, x::s, xs
        else aux (a,x::s,b) grab xs in
  let a, stack, b = aux ([],[],[]) false s.stack in
  s.stack <- List.rev stack;
  s.context <- Some (List.rev a, b)

let unfocus = function
  | { context = None } -> raise (Invalid_argument "CStack.unfocus")
  | { context = Some (a,b); stack } as s ->
       s.context <- None;
       s.stack <- a @ stack @ b

let focused { context } = context <> None

