(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Notations.
Require Import Logic.

(** Useful tactics *)

Ltac rewrite_all Eq := match type of Eq with
  ?a = ?b =>
     generalize Eq; clear Eq;
     match goal with
    | H : context [a] |- _ => intro Eq; rewrite Eq in H; rewrite_all Eq
    | _ => intro Eq
    end
 end.
