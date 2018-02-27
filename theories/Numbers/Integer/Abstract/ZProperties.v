(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export ZAxioms ZMaxMin ZSgnAbs ZParity ZPow ZDivTrunc ZDivFloor
 ZGcd ZLcm NZLog NZSqrt ZBits.

(** The two following functors summarize all known facts about N.

    - [ZBasicProp] provides properties of basic functions:
      + - * min max <= <

    - [ZExtraProp] provides properties of advanced functions:
      pow, sqrt, log2, div, gcd, and bitwise functions.

    If necessary, the earlier all-in-one functor [ZProp]
    could be re-obtained via [ZBasicProp <+ ZExtraProp] *)

Module Type ZBasicProp (Z:ZAxiomsMiniSig) := ZMaxMinProp Z.

Module Type ZExtraProp (Z:ZAxiomsSig)(P:ZBasicProp Z) :=
 ZSgnAbsProp Z P <+ ZParityProp Z P <+ ZPowProp Z P
 <+ NZSqrtProp Z Z P <+ NZSqrtUpProp Z Z P
 <+ NZLog2Prop Z Z Z P <+ NZLog2UpProp Z Z Z P
 <+ ZDivProp Z P <+ ZQuotProp Z P <+ ZGcdProp Z P <+ ZLcmProp Z P
 <+ ZBitsProp Z P.
