(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** * Extensionality axioms that can be used when reasoning with setoids.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(* $Id$ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Classes.SetoidClass.

(** Application of the extensionality axiom to turn a goal on
   Leibniz equality to a setoid equivalence (use with care!). *)

Axiom setoideq_eq : forall `{sa : Setoid a} (x y : a), x == y -> x = y.

(** Application of the extensionality principle for setoids. *)

Ltac setoid_extensionality :=
  match goal with
    [ |- @eq ?A ?X ?Y ] => apply (setoideq_eq (a:=A) (x:=X) (y:=Y))
  end.
