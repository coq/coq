(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export NAxioms.
Require Import NMaxMin NParity NPow NSqrt NLog NDiv NDiv0 NGcd NLcm NLcm0 NBits.

(** The two following functors summarize all known facts about N.

    - [NBasicProp] provides properties of basic functions:
      + - * min max <= <

    - [NExtraProp] provides properties of advanced functions:
      pow, sqrt, log2, div, gcd, and bitwise functions.
      [NExtraProp0] additionally assumes a / 0 == 0 and a mod 0 == a.

    If necessary, the earlier all-in-one functor [NProp]
    could be re-obtained via [NBasicProp <+ NExtraProp] *)

Module Type NBasicProp (N:NAxiomsMiniSig) := NMaxMinProp N.

Module Type NExtraPreProp (N:NAxiomsSig)(P:NBasicProp N) :=
 NParityProp N P <+ NPowProp N P <+ NSqrtProp N P <+ NLog2Prop N P <+ NGcdProp N P.

Module Type NExtraProp (N:NAxiomsSig)(P:NBasicProp N) :=
 NExtraPreProp N P <+ NDivProp N P <+ NLcmProp N P <+ NBitsProp N P.

Module Type NExtraProp0 (N:NAxiomsSig)(P:NBasicProp N)(D0:NZDivSpec0 N N N)(E:NExtraPreProp N P).
 Module Private_NDivProp := Nop <+ NDivProp N P.
 Include NDivProp0 N P D0.
 Module Private_NLcmProp := Nop <+ NLcmProp N P Private_NDivProp E.
 Include NLcmProp0 N P D0 E.
 Include NBitsProp N P E E Private_NDivProp E.
End NExtraProp0.
