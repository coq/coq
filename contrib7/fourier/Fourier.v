(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

(* "Fourier's method to solve linear inequations/equations systems.".*)

Declare ML Module "quote".
Declare ML Module "ring".
Declare ML Module "fourier".
Declare ML Module "fourierR".
Declare ML Module "field".

Require Export Fourier_util.
Require Export Field.
Require Export DiscrR.

Tactic Definition Fourier  :=
  Abstract (FourierZ;Field;DiscrR).

Tactic Definition FourierEq  :=
  Apply Rge_ge_eq ; Fourier.

