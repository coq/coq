(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Binary Numerical Datatypes *)

Set Implicit Arguments.

(** [positive] is a datatype representing the strictly positive integers
   in a binary way. Starting from 1 (represented by [xH]), one can
   add a new least significant digit via [xO] (digit 0) or [xI] (digit 1).
   Numbers in [positive] will also be denoted using a decimal notation;
   e.g. [6%positive] will abbreviate [xO (xI xH)] *)

Inductive positive : Set :=
  | xI : positive -> positive
  | xO : positive -> positive
  | xH : positive.

Delimit Scope positive_scope with positive.
Bind Scope positive_scope with positive.
Arguments xO _%positive.
Arguments xI _%positive.

(** [N] is a datatype representing natural numbers in a binary way,
    by extending the [positive] datatype with a zero.
    Numbers in [N] will also be denoted using a decimal notation;
    e.g. [6%N] will abbreviate [Npos (xO (xI xH))] *)

Inductive N : Set :=
  | N0 : N
  | Npos : positive -> N.

Delimit Scope N_scope with N.
Bind Scope N_scope with N.
Arguments Npos _%positive.

(** [Z] is a datatype representing the integers in a binary way.
    An integer is either zero or a strictly positive number
    (coded as a [positive]) or a strictly negative number
    (whose opposite is stored as a [positive] value).
    Numbers in [Z] will also be denoted using a decimal notation;
    e.g. [(-6)%Z] will abbreviate [Zneg (xO (xI xH))] *)

Inductive Z : Set :=
  | Z0 : Z
  | Zpos : positive -> Z
  | Zneg : positive -> Z.

Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.
Arguments Zpos _%positive.
Arguments Zneg _%positive.
