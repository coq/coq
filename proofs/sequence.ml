(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: sequence.ml aspiwack $ *)

(* This module implements a small list-like datatype with fast append. 
   Operations are not tailrec. *)

(* arnaud: blabla, pas essentiellement proof, mais utilisé que dans proof *)

(* arnaud: faire de la doc *)

type 'a sequence = 
  | Atom of 'a 
  | Compound of 'a sequence*'a sequence






(* iteration function *)
let rec iter f seq =
  match seq with
  | Atom a -> f a
  | Compound (lft,rgt) -> (iter f lft);(iter f rgt)


(* map function *)
let rec map f seq =
  match seq with
  | Atom a -> Atom (f a)
  | Compound (lft, rght) -> Compound (map f lft, map f rght)


let element a = Atom a

let append s t = Compound (s,t)
