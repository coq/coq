(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* "Fourier's method to solve linear inequations/equations systems.".*)

Require Export Field.
Require Export DiscrR.
Require Export Fourier_util.
Declare ML Module "fourier_plugin".

Ltac fourier := abstract (fourierz; field; discrR).

Ltac fourier_eq := apply Rge_antisym; fourier.
