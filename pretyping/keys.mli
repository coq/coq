(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type key

val declare_equiv_keys : key -> key -> unit
(** Declare two keys as being equivalent. *)

val equiv_keys : key -> key -> bool
(** Check equivalence of keys. *)

val constr_key : Environ.env -> ('a -> ('a, 't, 'u, 'i, 'r) Constr.kind_of_term) -> 'a -> key option
(** Compute the head key of a term. *)

val pr_keys : (Names.GlobRef.t -> Pp.t) -> Pp.t
(** Pretty-print the mapping *)
