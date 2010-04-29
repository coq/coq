(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* "Fourier's method to solve linear inequations/equations systems.".*)

Require Export LegacyRing.
Require Export LegacyField.
Require Export DiscrR.
Require Export Fourier_util.
Declare ML Module "fourier_plugin".

Ltac fourier := abstract (fourierz; field; discrR).

Ltac fourier_eq := apply Rge_antisym; fourier.
