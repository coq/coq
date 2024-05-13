(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type ('value, 'vaccu, 'vfun, 'vprod, 'vfix, 'vcofix, 'vblock) kind =
  | Vaccu of 'vaccu
  | Vfun of 'vfun
  | Vprod of 'vprod
  | Vfix of 'vfix
  | Vcofix of 'vcofix
  | Vconst of int
  | Vblock of 'vblock
  | Vint64 of int64
  | Vfloat64 of float
  | Vstring of string
  | Varray of 'value Parray.t
