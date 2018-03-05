(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* "Fourier's method to solve linear inequations/equations systems.".*)

Require Export Field.
Require Export DiscrR.
Require Export Fourier_util.
Declare ML Module "fourier_plugin".

Ltac fourier := abstract (compute [IZR IPR IPR_2] in *; fourierz; field; discrR).

Ltac fourier_eq := apply Rge_antisym; fourier.
