(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

open Util

type ('a,'b) t = ('a,'b list) Gmap.t

let empty = Gmap.empty
let mem = Gmap.mem
let iter = Gmap.iter
let map = Gmap.map
let fold = Gmap.fold

let add x y m =
  try
    let l = Gmap.find x m in
    Gmap.add x (y::list_except y l) m
  with Not_found ->
    Gmap.add x [y] m

let find x m =
  try Gmap.find x m with Not_found -> []

let remove x y m =
  let l = Gmap.find x m in
  Gmap.add x (if List.mem y l then list_subtract l [y] else l) m


