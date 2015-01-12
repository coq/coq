(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export NAxioms.
Require Import NMaxMin NParity NPow NSqrt NLog NDiv NGcd NLcm NBits.

(** The two following functors summarize all known facts about N.

    - [NBasicProp] provides properties of basic functions:
      + - * min max <= <

    - [NExtraProp] provides properties of advanced functions:
      pow, sqrt, log2, div, gcd, and bitwise functions.

    If necessary, the earlier all-in-one functor [NProp]
    could be re-obtained via [NBasicProp <+ NExtraProp] *)

Module Type NBasicProp (N:NAxiomsMiniSig) := NMaxMinProp N.

Module Type NExtraProp (N:NAxiomsSig)(P:NBasicProp N) :=
 NParityProp N P <+ NPowProp N P <+ NSqrtProp N P
  <+ NLog2Prop N P <+ NDivProp N P <+ NGcdProp N P <+ NLcmProp N P
  <+ NBitsProp N P.
