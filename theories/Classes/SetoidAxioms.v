(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Extensionality axioms that can be used when reasoning with setoids.
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Classes.SetoidClass.

(* Application of the extensionality axiom to turn a goal on leibinz equality to 
   a setoid equivalence. *)

Axiom setoideq_eq : forall [ sa : Setoid a ] (x y : a), x == y -> x = y.

(** Application of the extensionality principle for setoids. *)

Ltac setoid_extensionality :=
  match goal with
    [ |- @eq ?A ?X ?Y ] => apply (setoideq_eq (a:=A) (x:=X) (y:=Y))
  end.