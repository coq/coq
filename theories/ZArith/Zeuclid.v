(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Attributes deprecated(since="8.20",
  note="Use floor division or truncation division in BinInt instead.").

From Stdlib.Classes Require Import Morphisms.
From Stdlib.ZArith Require Import BinInt.

#[local]
Set Warnings "-deprecated-library-file".
From Stdlib.Numbers.Integer.Abstract Require Import ZDivEucl.

Local Open Scope Z_scope.

(** * Definitions of division for binary integers, Euclid convention. *)

(** In this convention, the remainder is always positive.
    For other conventions, see [Z.div] and [Z.quot] in file [BinIntDef].
    To avoid collision with the other divisions, we place this one
    under a module.
*)

Module ZEuclid.

 Definition modulo a b := Z.modulo a (Z.abs b).
 Definition div a b := (Z.sgn b) * (Z.div a (Z.abs b)).

#[global]
 Instance mod_wd : Proper (eq==>eq==>eq) modulo.
 Proof. congruence. Qed.
#[global]
 Instance div_wd : Proper (eq==>eq==>eq) div.
 Proof. congruence. Qed.

 Theorem div_mod a b : b<>0 -> a = b*(div a b) + modulo a b.
 Proof.
  intros Hb. unfold div, modulo.
  rewrite Z.mul_assoc. rewrite Z.sgn_abs. apply Z.div_mod.
  now destruct b.
 Qed.

 Lemma mod_always_pos a b : b<>0 -> 0 <= modulo a b < Z.abs b.
 Proof.
  intros Hb. unfold modulo.
  apply Z.mod_pos_bound.
  destruct b; compute; trivial. now destruct Hb.
 Qed.

 Lemma mod_bound_pos a b : 0<=a -> 0<b -> 0 <= modulo a b < b.
 Proof.
  intros _ Hb. rewrite <- (Z.abs_eq b) at 3 by Z.order.
  apply mod_always_pos. Z.order.
 Qed.

 Include ZEuclidProp Z Z Z.

End ZEuclid.
