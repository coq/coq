(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                                                                      *)
(* Micromega: A reflexive tactic using the Positivstellensatz           *)
(*                                                                      *)
(*  Frédéric Besson (Irisa/Inria) 2006-2008                             *)
(*                                                                      *)
(************************************************************************)

(* Used to generate micromega.ml *)

Require Import ZMicromega.
Require Import QMicromega.
Require Import RMicromega.
Require Import VarMap.
Require Import RingMicromega.
Require Import NArith.
Require Import QArith.

Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive list => list [ "[]" "(::)" ].
Extract Inductive bool => bool [ true false ].
Extract Inductive sumbool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive sumor => option [ Some None ].
(** Then, in a ternary alternative { }+{ }+{ },
   -  leftmost choice (Inleft Left) is (Some true),
   -  middle choice (Inleft Right) is (Some false),
   -  rightmost choice (Inright) is (None) *)


(** To preserve its laziness, andb is normally expansed.
    Let's rather use the ocaml && *)
Extract Inlined Constant andb => "(&&)".

Require Import Reals.

Extract Constant R => "int".  
Extract Constant R0 => "0".  
Extract Constant R1 => "1".  
Extract Constant Rplus => "( + )".
Extract Constant Rmult => "( * )".
Extract Constant Ropp  => "fun x -> - x".
Extract Constant Rinv   => "fun x -> 1 / x".

Extraction "micromega.ml"
  List.map simpl_cone (*map_cone  indexes*)
  denorm Qpower
  n_of_Z N.of_nat ZTautoChecker ZWeakChecker QTautoChecker RTautoChecker find.




(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
