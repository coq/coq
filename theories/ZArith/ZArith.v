(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Library for manipulating integers based on binary encoding *)

Require Export ZArith_base.

(** Extra modules using [Omega] or [Ring]. *)

Require Export Zcomplements.
Require Export Zsqrt.
Require Export Zpower.
Require Export Zdiv.
Require Export Zlogarithm.

Export ZArithRing.

(** Final Z module, cumulating ZBinary.Z and Zdiv.Z *)

Module Z := Zdiv.Z.
