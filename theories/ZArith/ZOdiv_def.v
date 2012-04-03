(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import BinInt.

Notation ZOdiv_eucl := Z.quotrem (only parsing).
Notation ZOdiv := Z.quot (only parsing).
Notation ZOmod := Z.rem (only parsing).

Notation ZOdiv_eucl_correct := Z.quotrem_eq.
