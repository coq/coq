(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

(* "Fourier's method to solve linear inequations/equations systems.".*)

Declare ML Module "quote".
Declare ML Module "ring".
Declare ML Module "fourier".
Declare ML Module "fourierR".

Require Export Fourier_util.

Grammar tactic simple_tactic:ast:=
  fourier
  ["Fourier" constrarg_list($arg)] ->
  [(Fourier ($LIST $arg))].

Tactic Definition FourierEq  :=
  Apply Rge_ge_eq ; Fourier.

