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
Require Import VarMap.
Require Import RingMicromega.
Require Import NArith.

Extraction "micromega.ml"  List.map simpl_cone map_cone indexes  n_of_Z Nnat.N_of_nat ZTautoChecker QTautoChecker find.
