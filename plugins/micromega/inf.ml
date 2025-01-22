(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open NumCompat
open Q.Notations
open Mutils

(** Manipulation of infinitesimals *)

(* (x,y) denotes x + y.e for some infinitesimal e *)
type t = Q.t * Q.t

let tolerance = ref (Q.of_float min_float)

let set_tolerance q = tolerance := q

let frac_num (x,y) =
  let fn = x -/ Q.floor x in
  if not (y =/ Q.zero)
  then Some (fn +/ !tolerance)
  else if fn =/ Q.zero
       then None
       else Some fn

let decomp (x,y) = (x,y)

let cst q = (q,Q.zero)

let zero = (Q.zero,Q.zero)

let epsilon = (Q.zero, Q.one)

let cste q b =
  if b
  then  (q,Q.minus_one)
  else  (q,Q.zero)

let hash (x,y) = Hashtbl.hash (Q.to_float x,Q.to_float y)

let add (a1,b1) (a2,b2) =
  (a1 +/ a2, b1 +/ b2)

let mulc c (a1,b1) = (c */ a1, c */ b1)

let divc (a1,b1) c = (a1 // c , b1 // c)

let uminus (a1,b1) = (Q.neg a1,Q.neg b1)

let abs (i,j) =
  let cmp = Q.compare i Q.zero in
  if cmp = 0
  then (Q.zero,Q.abs j) (* epsilon wins *)
  else (* sign of epsilon does not matter *)
    if cmp < 0
    then (Q.neg i, Q.neg j)
    else (i,j)


let lt (a1,b1) (a2,b2) =
  let cmp = Q.compare a1 a2 in
  cmp < 0 || (Int.equal cmp  0 && b1 </ b2)

let ge_0 (a1,b1) =
  let cmp = Q.compare a1 Q.zero in
  if cmp > 0 then true
  else if cmp < 0 then false
  else b1 >=/ Q.zero


let equal (a1,b1) (a2,b2) =
  a1 =/ a2 && b1 =/ b2

let compare (a1,b1) (a2,b2) =
  let cmp = Q.compare a1 a2 in
  if cmp = 0 then Q.compare b1 b2
  else cmp

let pp o (a1,b1) =
  match a1 =/ Q.zero , b1 =/ Q.zero with
  | true , true -> output_string o "0"
  | true , false -> Printf.fprintf o "%s.e" (Q.to_string b1)
  | false , true -> output_string o (Q.to_string a1)
  | false , false -> Printf.fprintf o "%s + %s.e" (Q.to_string a1) (Q.to_string b1)

let is_zero (a1,b1) = a1 =/ Q.zero && (b1 = Q.zero)

let pp_smt o (a1,b1) =
  match a1 =/ Q.zero , b1 =/ Q.zero with
  | true , true -> output_string o "0"
  | true , false -> Printf.fprintf o "(* %a e)" pp_smt_num b1
  | false , true -> output_string o (Q.to_string a1)
  | false , false -> Printf.fprintf o "(+ %a  (* %a e))" pp_smt_num a1 pp_smt_num b1


let gcd (a,b) =
  Z.gcd (Q.num a) (Q.num b)

let ppcm (a,b) = Z.ppcm (Q.den a) (Q.den b)
