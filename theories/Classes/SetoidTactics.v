(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certified Haskell Prelude.
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Classes.Setoid.

Ltac refl :=
  match goal with
    | [ |- @equiv ?A ?R ?s ?X _ ] => apply (equiv_refl (A:=A) (R:=R) (s:=s) X)
    | [ |- ?R ?X _ ] => apply (equiv_refl (R:=R) X)
    | [ |- ?R ?A ?X _ ] => apply (equiv_refl (R:=R A) X)
    | [ |- ?R ?A ?B ?X _ ] => apply (equiv_refl (R:=R A B) X)
    | [ |- ?R ?A ?B ?C ?X _ ] => apply (equiv_refl (R:=R A B C) X)
  end.

Ltac sym := 
  match goal with
    | [ |- @equiv ?A ?R ?s ?X ?Y ] => apply (equiv_sym (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y))
    | [ |- ?R ?X ?Y ] => apply (equiv_sym (R:=R) (x:=Y) (y:=X))
    | [ |- ?R ?A ?X ?Y ] => apply (equiv_sym (R:=R A) (x:=Y) (y:=X))
    | [ |- ?R ?A ?B ?X ?Y ] => apply (equiv_sym (R:=R A B) (x:=Y) (y:=X))
    | [ |- ?R ?A ?B ?C ?X ?Y ] => apply (equiv_sym (R:=R A B C) (x:=Y) (y:=X))
  end.

Ltac trans Y := 
  match goal with
    | [ |- @equiv ?A ?R ?s ?X ?Z ] => apply (equiv_trans (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?X ?Z ] => apply (equiv_trans (R:=R) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?X ?Z ] => apply (equiv_trans (R:=R A) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?B ?X ?Z ] => apply (equiv_trans (R:=R A B) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?B ?C ?X ?Z ] => apply (equiv_trans (R:=R A B C) (x:=X) (y:=Y) (z:=Z))
  end.

(* Bug, rebinding notation *)
Notation " x == y " := (equiv x y) (at level 70, no associativity).

Ltac rew H := clrewrite H.

(** Why have to rebind it, again ? *)
Lemma setoideq_eq [ sa : Setoid a eqa ] : forall x y, eqa x y -> x = y.
Proof.
  admit.
Qed.

Print setoideq_eq.

Implicit Arguments setoideq_eq [[a] [eqa] [sa]].

Ltac setoideq :=
  match goal with
    [ |- @eq ?A ?X ?Y ] => apply (setoideq_eq (a:=A) X Y)
  end.

