(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

val constr_key : ('a -> ('a, 't, 'u, 'i) Constr.kind_of_term) -> 'a -> key option
(** Compute the head key of a term. *)

val pr_keys : (Names.GlobRef.t -> Pp.t) -> Pp.t
(** Pretty-print the mapping *)
