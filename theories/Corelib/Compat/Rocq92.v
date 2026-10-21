(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Compatibility file for making Rocq act similar to Coq v9.2 *)

(* When adding Rocq93.v, uncomment the following line *)
(* Require Export Corelib.Compat.Rocq93. *)

#[export] Set Warnings "-deprecated-since-9.3".

#[export] Set Inline Abstract Subproof.

#[export] Set Asymmetric Patterns No Implicits.

#[export] Unset Proof Using Clear Unused.
