(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2017     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

type key

val declare_equiv_keys : key -> key -> unit
(** Declare two keys as being equivalent. *)

val equiv_keys : key -> key -> bool
(** Check equivalence of keys. *)

val constr_key : ('a -> ('a, 't, 'u, 'i) Constr.kind_of_term) -> 'a -> key option
(** Compute the head key of a term. *)

val pr_keys : (Names.global_reference -> Pp.t) -> Pp.t
(** Pretty-print the mapping *)
