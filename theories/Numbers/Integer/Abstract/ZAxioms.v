(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Export NZAxioms.
Require Import Bool NZParity NZPow NZSqrt NZLog NZGcd NZDiv NZBits.

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

Module Type OppCstNotation (Import A : NZAxiomsSig)(Import B : Opp A).
 Notation "- 1" := (opp one).
 Notation "- 2" := (opp two).
End OppCstNotation.

Module Type ZAxiomsMiniSig := NZOrdAxiomsSig <+ ZAxiom <+ Opp <+ IsOpp.
Module Type ZAxiomsMiniSig' := NZOrdAxiomsSig' <+ ZAxiom <+ Opp' <+ IsOpp
 <+ OppCstNotation.


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
 Axiom sgn_neg : forall n, n<0 -> sgn n == -1.
End HasSgn.

(** Divisions *)

(** First, the usual Coq convention of Truncated-Toward-Bottom
    (a.k.a Floor). We simply extend the NZ signature. *)

Module Type ZDivSpecific (Import A:ZAxiomsMiniSig')(Import B : DivMod' A).
 Axiom mod_pos_bound : forall a b, 0 < b -> 0 <= a mod b < b.
 Axiom mod_neg_bound : forall a b, b < 0 -> b < a mod b <= 0.
End ZDivSpecific.

Module Type ZDiv (Z:ZAxiomsMiniSig) := NZDiv.NZDiv Z <+ ZDivSpecific Z.
Module Type ZDiv' (Z:ZAxiomsMiniSig) := NZDiv.NZDiv' Z <+ ZDivSpecific Z.

(** Then, the Truncated-Toward-Zero convention.
    For not colliding with Floor operations, we use different names
*)

Module Type QuotRem (Import A : Typ).
 Parameters Inline quot rem : t -> t -> t.
End QuotRem.

Module Type QuotRemNotation (A : Typ)(Import B : QuotRem A).
 Infix "÷" := quot (at level 40, left associativity).
 Infix "rem" := rem (at level 40, no associativity).
End QuotRemNotation.

Module Type QuotRem' (A : Typ) := QuotRem A <+ QuotRemNotation A.

Module Type QuotRemSpec (Import A : ZAxiomsMiniSig')(Import B : QuotRem' A).
 Declare Instance quot_wd : Proper (eq==>eq==>eq) quot.
 Declare Instance rem_wd : Proper (eq==>eq==>eq) B.rem.
 Axiom quot_rem : forall a b, b ~= 0 -> a == b*(a÷b) + (a rem b).
 Axiom rem_bound_pos : forall a b, 0<=a -> 0<b -> 0 <= a rem b < b.
 Axiom rem_opp_l : forall a b, b ~= 0 -> (-a) rem b == - (a rem b).
 Axiom rem_opp_r : forall a b, b ~= 0 -> a rem (-b) == a rem b.
End QuotRemSpec.

Module Type ZQuot (Z:ZAxiomsMiniSig) := QuotRem Z <+ QuotRemSpec Z.
Module Type ZQuot' (Z:ZAxiomsMiniSig) := QuotRem' Z <+ QuotRemSpec Z.

(** For all other functions, the NZ axiomatizations are enough. *)

(** Let's group everything *)

Module Type ZAxiomsSig := ZAxiomsMiniSig <+ OrderFunctions
   <+ HasAbs <+ HasSgn <+ NZParity.NZParity
   <+ NZPow.NZPow <+ NZSqrt.NZSqrt <+ NZLog.NZLog2 <+ NZGcd.NZGcd
   <+ ZDiv <+ ZQuot <+ NZBits.NZBits <+ NZSquare.

Module Type ZAxiomsSig' := ZAxiomsMiniSig' <+ OrderFunctions'
   <+ HasAbs <+ HasSgn <+ NZParity.NZParity
   <+ NZPow.NZPow' <+ NZSqrt.NZSqrt' <+ NZLog.NZLog2 <+ NZGcd.NZGcd'
   <+ ZDiv' <+ ZQuot' <+ NZBits.NZBits' <+ NZSquare.
