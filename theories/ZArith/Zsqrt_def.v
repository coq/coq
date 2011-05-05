(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Definition of a square root function for Z. *)

Require Import BinPos BinInt.

Notation Zsqrtrem := Z.sqrtrem (only parsing).
Notation Zsqrt := Z.sqrt (only parsing).
Notation Zsqrtrem_spec := Z.sqrtrem_spec (only parsing).
Notation Zsqrt_spec := Z.sqrt_spec (only parsing).
Notation Zsqrt_neg := Z.sqrt_neg (only parsing).
Notation Zsqrtrem_sqrt := Z.sqrtrem_sqrt (only parsing).
