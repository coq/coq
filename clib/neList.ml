(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type 'a t = 'a * 'a list

let head (x,_) = x

let tail (_,tl) = match tl with
  | [] -> None
  | y::tl -> Some (y,tl)

let singleton x = x,[]

let iter f (x,tl) =
  f x;
  List.iter f tl

let map f (x,tl) =
  let x = f x in
  let tl = List.map f tl in
  x, tl

let map2 f (x,tl) (x',tl') =
  let x = f x x' in
  let tl = List.map2 f tl tl' in
  x, tl

let map_head f (x,tl) = f x, tl

let push x = function
  | None -> x, []
  | Some (y,tl) -> x, y::tl

let to_list (x,tl) = x::tl

let of_list = function
  | [] -> invalid_arg "NeList.of_list"
  | x::tl -> x,tl

let repr x = x

let of_repr x = x
