(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export NZAxioms.
Require Import NZPow.

(** We obtain integers by postulating that successor of predecessor
    is identity. *)

Module Type ZAxiom (Import Z : NZAxiomsSig').
 Axiom succ_pred : forall n, S (P n) == n.
End ZAxiom.

(** For historical reasons, ZAxiomsMiniSig isn't just NZ + ZAxiom,
    we also add an [opp] function, that can be seen as a shortcut
    for [sub 0]. *)

Module Type Opp (Import T:Typ).
 Parameter Inline opp : t -> t.
End Opp.

Module Type OppNotation (T:Typ)(Import O : Opp T).
 Notation "- x" := (opp x) (at level 35, right associativity).
End OppNotation.

Module Type Opp' (T:Typ) := Opp T <+ OppNotation T.

Module Type IsOpp (Import Z : NZAxiomsSig')(Import O : Opp' Z).
 Declare Instance opp_wd : Proper (eq==>eq) opp.
 Axiom opp_0 : - 0 == 0.
 Axiom opp_succ : forall n, - (S n) == P (- n).
End IsOpp.

Module Type ZAxiomsMiniSig := NZOrdAxiomsSig <+ ZAxiom <+ Opp <+ IsOpp.
Module Type ZAxiomsMiniSig' := NZOrdAxiomsSig' <+ ZAxiom <+ Opp' <+ IsOpp.

(** Other functions and their specifications *)

(** Absolute value *)

Module Type HasAbs(Import Z : ZAxiomsMiniSig').
 Parameter Inline abs : t -> t.
 Axiom abs_eq : forall n, 0<=n -> abs n == n.
 Axiom abs_neq : forall n, n<=0 -> abs n == -n.
End HasAbs.

(** A sign function *)

Module Type HasSgn (Import Z : ZAxiomsMiniSig').
 Parameter Inline sgn : t -> t.
 Axiom sgn_null : forall n, n==0 -> sgn n == 0.
 Axiom sgn_pos : forall n, 0<n -> sgn n == 1.
 Axiom sgn_neg : forall n, n<0 -> sgn n == -(1).
End HasSgn.

(** Parity functions *)

Module Type Parity (Import Z : ZAxiomsMiniSig').
 Parameter Inline even odd : t -> bool.
 Definition Even n := exists m, n == 2*m.
 Definition Odd n := exists m, n == 2*m+1.
 Axiom even_spec : forall n, even n = true <-> Even n.
 Axiom odd_spec : forall n, odd n = true <-> Odd n.
End Parity.

(** For the power function, we just add to NZPow an addition spec *)

Module Type ZPowSpecNeg (Import Z : ZAxiomsMiniSig')(Import P : Pow' Z).
 Axiom pow_neg : forall a b, b<0 -> a^b == 0.
End ZPowSpecNeg.


(** Let's group everything *)

Module Type ZAxiomsSig :=
  ZAxiomsMiniSig <+ HasCompare <+ HasAbs <+ HasSgn <+ Parity
   <+ NZPow.NZPow <+ ZPowSpecNeg.
Module Type ZAxiomsSig' :=
  ZAxiomsMiniSig' <+ HasCompare <+ HasAbs <+ HasSgn <+ Parity
   <+ NZPow.NZPow' <+ ZPowSpecNeg.


(** Division is left apart, since many different flavours are available *)
