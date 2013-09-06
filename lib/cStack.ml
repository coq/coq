(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

open CSig

exception Empty = Stack.Empty

type 'a t = 'a list ref

let create () = ref []
let push x l = l := x :: !l
let pop l = match !l with [] -> raise Stack.Empty | x::xs -> l := xs; x
let top l = match !l with [] -> raise Stack.Empty | x::_ -> x
let find f l = List.find f !l
let find_map f l =
  let rec aux = function
  | [] -> raise Not_found
  | x :: xs -> match f x with None -> aux xs | Some i -> i
  in
  aux !l
let seek f accu l =
  let rec aux accu = function
    | [] -> raise Not_found
    | x :: xs -> match f accu x with Stop x -> x | Next i -> aux accu xs in
  aux accu !l
let is_empty l = match !l with [] -> true | _ -> false
let iter f l = List.iter f !l
let clear l = l := []
let length l = List.length !l
let to_list l = !l
