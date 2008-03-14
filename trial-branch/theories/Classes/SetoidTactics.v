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
 * Institution: LRI, CNRS UMR 8623 - Universit�copyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.

Set Implicit Arguments.
Unset Strict Implicit.

Require Export Coq.Classes.SetoidClass.

Ltac rew H := clrewrite H.

Lemma setoideq_eq [ sa : Setoid a eqa ] : forall x y, eqa x y -> x = y.
Proof.
  admit.
Qed.

Implicit Arguments setoideq_eq [[a] [eqa] [sa]].

Ltac setoideq :=
  match goal with
    [ |- @eq ?A ?X ?Y ] => apply (setoideq_eq (a:=A) X Y)
  end.

Ltac setoid_tactic :=
  match goal with
    | [ H : ?eq ?x ?y |- ?eq ?y ?x ] => sym ; apply H
    | [ |- ?eq ?x ?x ] => refl
    | [ H : ?eq ?x ?y, H' : ?eq ?y ?z |- ?eq' ?x ?z ] => trans y ; [ apply H | apply H' ]
    | [ H : ?eq ?x ?y, H' : ?eq ?z ?y |- ?eq' ?x ?z ] => trans y ; [ apply H | sym ; apply H' ]
    | [ H : ?eq ?y ?x, H' : ?eq ?z ?y |- ?eq' ?x ?z ] => trans y ; [ sym ; apply H | sym ; apply H' ]
    | [ H : ?eq ?y ?x, H' : ?eq ?y ?z |- ?eq' ?x ?z ] => trans y ; [ sym ; apply H | apply H' ]
      
    | [ H : ?eq ?x ?y |- @equiv _ _ _ ?y ?x ] => sym ; apply H
    | [ |- @equiv _ _ _ ?x ?x ] => refl
    | [ H : ?eq ?x ?y, H' : ?eq ?y ?z |- @equiv _ _ _ ?x ?z ] => trans y ; [ apply H | apply H' ]
    | [ H : ?eq ?x ?y, H' : ?eq ?z ?y |- @equiv _ _ _ ?x ?z ] => trans y ; [ apply H | sym ; apply H' ]
    | [ H : ?eq ?y ?x, H' : ?eq ?z ?y |- @equiv _ _ _ ?x ?z ] => trans y ; [ sym ; apply H | sym ; apply H' ]
    | [ H : ?eq ?y ?x, H' : ?eq ?y ?z |- @equiv _ _ _ ?x ?z ] => trans y ; [ sym ; apply H | apply H' ]

    | [ H : @equiv ?A ?R ?s ?x ?y |- @equiv _ _ _ ?y ?x ] => sym ; apply H
    | [ |- @equiv _ _ _ ?x ?x ] => refl
    | [ H : @equiv ?A ?R ?s ?x ?y, H' : @equiv ?A ?R ?s ?y ?z |- @equiv _ _ _ ?x ?z ] => trans y ; [ apply H | apply H' ]
    | [ H : @equiv ?A ?R ?s ?x ?y, H' : @equiv ?A ?R ?s ?z ?y |- @equiv _ _ _ ?x ?z ] => trans y ; [ apply H | sym ; apply H' ]
    | [ H : @equiv ?A ?R ?s ?y ?x, H' : @equiv ?A ?R ?s ?z ?y |- @equiv _ _ _ ?x ?z ] => trans y ; [ sym ; apply H | sym ; apply H' ]
    | [ H : @equiv ?A ?R ?s ?y ?x, H' : @equiv ?A ?R ?s ?y ?z |- @equiv _ _ _ ?x ?z ] => trans y ; [ sym ; apply H | apply H' ]

    | [ H : not (@equiv ?A ?R ?s ?X ?X) |- _ ] => elim H ; refl
    | [ H : not (@equiv ?A ?R ?s ?X ?Y), H' : @equiv ?A ?R ?s ?Y ?X |- _ ] => elim H ; sym ; apply H
    | [ H : not (@equiv ?A ?R ?s ?X ?Y), H' : ?R ?Y ?X |- _ ] => elim H ; sym ; apply H
    | [ H : not (@equiv ?A ?R ?s ?X ?Y) |- False ] => elim H ; clear H ; setoid_tac
  end.
