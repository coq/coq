(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2015     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Typed grammar entries *)

type 'a t
(** Typed grammar entries. We need to defined them here so that they are
    marshallable and defined before the Pcoq.Gram module. They are basically
    unique names made of a universe and an entry name. They should be kept
    synchronized with the {!Pcoq} entries though. *)

type repr = string * string
(** Representation of entries. *)

(** Table of Coq statically defined grammar entries *)

type universe

(** There are four predefined universes: "prim", "constr", "tactic", "vernac" *)

val get_univ : string -> universe
val univ_name : universe -> string

val uprim : universe
val uconstr : universe
val utactic : universe
val uvernac : universe

(** {5 Uniquely defined entries} *)

val create : universe -> string -> 'a t
(** Create an entry. They should be synchronized with the entries defined in
    {!Pcoq}. *)

(** {5 Meta-programming} *)

val repr : 'a t -> repr

val unsafe_of_name : (string * string) -> 'a t
