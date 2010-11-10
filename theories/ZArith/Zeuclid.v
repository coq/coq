(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Morphisms BinInt Zdiv_def ZBinary ZDivEucl.
Local Open Scope Z_scope.

(** * Definitions of division for binary integers, Euclid convention. *)

(** In this convention, the remainder is always positive.
    For other conventions, see file Zdiv_def.
    To avoid collision with the other divisions, we place this one
    under a module.
*)

Module ZEuclid.

 Definition modulo a b := Zmod a (Zabs b).
 Definition div a b := (Zsgn b) * (Zdiv a (Zabs b)).

 Instance mod_wd : Proper (eq==>eq==>eq) modulo.
 Proof. congruence. Qed.
 Instance div_wd : Proper (eq==>eq==>eq) div.
 Proof. congruence. Qed.

 Theorem div_mod : forall a b, b<>0 ->
  a = b*(div a b) + modulo a b.
 Proof.
  intros a b Hb. unfold div, modulo.
  rewrite Zmult_assoc. rewrite Z.sgn_abs. apply Z.div_mod.
  now destruct b.
 Qed.

 Lemma mod_always_pos : forall a b, b<>0 ->
  0 <= modulo a b < Zabs b.
 Proof.
  intros a b Hb. unfold modulo.
  apply Z.mod_pos_bound.
  destruct b; compute; trivial. now destruct Hb.
 Qed.

 Lemma mod_bound_pos : forall a b, 0<=a -> 0<b -> 0 <= modulo a b < b.
 Proof.
  intros a b _ Hb. rewrite <- (Z.abs_eq b) at 3 by z_order.
  apply mod_always_pos. z_order.
 Qed.

 Include ZEuclidProp Z Z Z.

End ZEuclid.
