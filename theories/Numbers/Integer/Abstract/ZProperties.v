(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export ZAxioms ZMaxMin ZSgnAbs ZParity ZPow ZDivTrunc ZDivFloor
 ZGcd ZLcm NZLog NZSqrt ZBits.

(** This functor summarizes all known facts about Z. *)

Module Type ZProp (Z:ZAxiomsSig) :=
 ZMaxMinProp Z <+ ZSgnAbsProp Z <+ ZParityProp Z <+ ZPowProp Z
 <+ NZSqrtProp Z Z <+ NZSqrtUpProp Z Z
 <+ NZLog2Prop Z Z Z <+ NZLog2UpProp Z Z Z
 <+ ZDivProp Z <+ ZQuotProp Z <+ ZGcdProp Z <+ ZLcmProp Z
 <+ ZBitsProp Z.
