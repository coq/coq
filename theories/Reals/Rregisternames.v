(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Reals.

(*****************************************************************)
(** *   Register names in the Reals library used by plugins      *)
(*****************************************************************)

Register R as reals.R.type.
Register R0 as reals.R.R0.
Register R1 as reals.R.R1.
Register Rle as reals.R.Rle.
Register Rplus as reals.R.Rplus.
Register Ropp as reals.R.Ropp.
Register Rminus as reals.R.Rminus.
Register Rmult as reals.R.Rmult.
Register Rinv as reals.R.Rinv.
Register Rdiv as reals.R.Rdiv.
Register IZR as reals.R.IZR.
Register Rabs as reals.R.Rabs.
Register sqrt as reals.R.sqrt.
Register powerRZ as reals.R.powerRZ.
