(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type 'a t = 'a list ref
type ('a,'b) search = [ `Stop of 'b | `Cont of 'a ]

let create () = ref []
let push x l = l := x :: !l
let pop l = match !l with [] -> raise Stack.Empty | x::xs -> l := xs; x
let top l = match !l with [] -> raise Stack.Empty | x::_ -> x
let find f i l =
  let rec aux i = function
    | [] -> raise Not_found
    | x::xs -> match f i x with `Stop x -> x | `Cont i -> aux i xs in
  aux i !l
let is_empty l = match !l with [] -> true | _ -> false
let iter f l = List.iter f !l
let clear l = l := []
let length l = List.length !l
let to_list l = !l
