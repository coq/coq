(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** The Floats library is split in 6 theories:
- FloatClass: define the [float_class] inductive
- PrimFloat: define the floating-point values and operators as kernel primitives
- SpecFloat: specify the floating-point operators with binary integers
- FloatOps: define conversion functions between [spec_float] and [float]
- FloatAxioms: state properties of the primitive operators w.r.t. [spec_float]
- FloatLemmas: prove a few results involving Z.frexp and Z.ldexp

For a brief overview of the Floats library,
see {{https://coq.inria.fr/distrib/current/refman/language/coq-library.html#floats-library}}

N.B.: This library only offers a bit-level specification of floating-point
arithmetic. For a more complete set of theorems, including links with real
arithmetic, see the Flocq library {{https://flocq.gitlabpages.inria.fr/}} *)

Require Export FloatClass.
Require Export PrimFloat.
Require Export SpecFloat.
Require Export FloatOps.
Require Export FloatAxioms.
Require Export FloatLemmas.
