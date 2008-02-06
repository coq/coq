(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Tactics for typeclass-based setoids.
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

Lemma setoideq_eq [ sa : Setoid a ] : forall x y : a, x == y -> x = y.
Proof.
  admit.
Qed.

Implicit Arguments setoideq_eq [[a] [sa]].

(** Application of the extensionality principle for setoids. *)

Ltac setoideq_ext :=
  match goal with
    [ |- @eq ?A ?X ?Y ] => apply (setoideq_eq (a:=A) X Y)
  end.

