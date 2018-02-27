(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Basic facts about Prop as a type *)

(** An intuitionistic theorem from topos theory [[LambekScott]]

References:

[[LambekScott]] Jim Lambek, Phil J. Scott, Introduction to higher
order categorical logic, Cambridge Studies in Advanced Mathematics
(Book 7), 1988.

*)

Theorem injection_is_involution_in_Prop
  (f : Prop -> Prop)
  (inj : forall A B, (f A <-> f B) -> (A <-> B))
  (ext : forall A B, A <-> B -> f A <-> f B)
  : forall A, f (f A) <-> A.
Proof.
intros.
enough (f (f (f A)) <-> f A) by (apply inj; assumption).
split; intro H.
- now_show (f A).
  enough (f A <-> True) by firstorder.
  enough (f (f A) <-> f True) by (apply inj; assumption).
  split; intro H'.
  + now_show (f True).
    enough (f (f (f A)) <-> f True) by firstorder.
    apply ext; firstorder.
  + now_show (f (f A)).
    enough (f (f A) <-> True) by firstorder.
    apply inj; firstorder.
- now_show (f (f (f A))).
  enough (f A <-> f (f (f A))) by firstorder.
  apply ext.
  split; intro H'.
  + now_show (f (f A)).
    enough (f A <-> f (f A)) by firstorder.
    apply ext; firstorder.
  + now_show A.
    enough (f A <-> A) by firstorder.
    apply inj; firstorder.
Defined.
