(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type cmp =
  | Eq
  | Lt | Le
  | Gt | Ge

val wit_comparison : (cmp, cmp, cmp) Genarg.genarg_type

type 'i test =
  | Test of cmp * 'i * 'i

val wit_test : (int Locus.or_var test, int Locus.or_var test, int test) Genarg.genarg_type
