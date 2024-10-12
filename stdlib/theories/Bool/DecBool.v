(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

Definition ifdec (A B:Prop) (C:Type) (H:{A} + {B}) (x y:C) : C :=
  if H then x else y.


Theorem ifdec_left :
  forall (A B:Prop) (C:Set) (H:{A} + {B}),
    ~ B -> forall x y:C, ifdec H x y = x.
Proof.
  intros A B C H **; case H; auto.
  intro; absurd B; trivial.
Qed.

Theorem ifdec_right :
  forall (A B:Prop) (C:Set) (H:{A} + {B}),
    ~ A -> forall x y:C, ifdec H x y = y.
Proof.
  intros A B C H **; case H; auto.
  intro; absurd A; trivial.
Qed.

Unset Implicit Arguments.
