(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
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

Extract Inductive prod => "( * )" [ "(,)" ].
Extract Inductive List.list => list [ "[]" "(::)" ].
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

Extraction "micromega.ml"
  List.map simpl_cone (*map_cone  indexes*)
  denorm
  n_of_Z Nnat.N_of_nat ZTautoChecker ZWeakChecker QTautoChecker RTautoChecker find.

(* Local Variables: *)
(* coding: utf-8 *)
(* End: *)
