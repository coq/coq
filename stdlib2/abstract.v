(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From stdlib Require Import prelude ssreflect datatypes equality nat.

(* Constants for abstract: and [: name ] intro pattern *)
Definition abstract_lock := unit.
Definition abstract_key := tt.

Definition abstract (statement : Type) (id : nat) (lock : abstract_lock) :=
  let: tt := lock in statement.

Notation "<hidden n >" := (abstract _ n _).
Notation "T (* n *)" := (abstract T n abstract_key).

Register abstract_lock as plugins.ssreflect.abstract_lock.
Register abstract_key as plugins.ssreflect.abstract_key.
Register abstract as plugins.ssreflect.abstract.

(* To focus non-ssreflect tactics on a subterm, eg vm_compute. *)
(* Usage:                                                      *)
(*   elim/abstract_context: (pattern) => G defG.               *)
(*   vm_compute; rewrite {}defG {G}.                           *)
(* Note that vm_cast are not stored in the proof term          *)
(* for reductions occuring in the context, hence               *)
(*   set here := pattern; vm_compute in (value of here)        *)
(* blows up at Qed time.                                       *)
Lemma abstract_context T (P : T -> Type) x :
  (forall Q, Q = P -> Q x) -> P x.
Proof. by move=> /(_ P); apply. Qed.
