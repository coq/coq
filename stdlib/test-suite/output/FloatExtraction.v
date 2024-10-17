(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

From Stdlib Require Import Floats ExtrOCamlFloats.

From Stdlib Require Import List. Import ListNotations.

(* from Require Import ExtrOcamlBasic. *)
Extract Inductive list => list [ "[]" "( :: )" ].

Local Open Scope float_scope.

(* Avoid exponents with less than three digits as they are usually
   displayed with two digits (1e7 is displayed 1e+07) except on
   Windows where three digits are used (1e+007). *)
Definition list_floats :=
  [nan; infinity; neg_infinity; zero; one; two;
   0.5; 0.01; -0.5; -0.01; 1.7e+308; -1.7e-308].

Recursive Extraction list_floats.

Definition discr a b c := b * b - 4.0 * a * c.

Definition x1 a b c := (- b - sqrt (discr a b c)) / (2.0 * a).

Recursive Extraction x1.
