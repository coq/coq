(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** The modules defined below represent a {e local context}
    as defined by Chapter 4 in the Reference Manual:

    A {e local context} is an ordered list of of {e local declarations}
    of names that we call {e variables}.

    A {e local declaration} of some variable can be either:
    - a {e local assumption}, or
    - a {e local definition}.

    {e Local assumptions} are denoted in the Reference Manual as [(name : typ)] and
    {e local definitions} are there denoted as [(name := value : typ)].
*)

open Names

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel :
sig
  (** Representation of {e local declarations}.

      [(name, None, typ)] represents a {e local assumption}.

      [(name, Some value, typ)] represents a {e local definition}.
   *)
  module Declaration :
  sig
    type t = Name.t * Constr.t option * Constr.t

    (** Map all terms in a given declaration. *)
    val map : (Constr.t -> Constr.t) -> t -> t

    (** Reduce all terms in a given declaration to a single value. *)
    val fold : (Constr.t -> 'a -> 'a) -> t -> 'a -> 'a

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : (Constr.t -> bool) -> t -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : (Constr.t -> bool) -> t -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : t -> t -> bool
  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type t = Declaration.t list

  (** empty rel-context *)
  val empty : t

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  val add : Declaration.t -> t -> t

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index outside the range. *)
  val lookup : int -> t -> Declaration.t

  (** Map all terms in a given rel-context. *)
  val map : (Constr.t -> Constr.t) -> t -> t

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> Declaration.t -> 'a) -> init:'a -> t -> 'a

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a

  (** Perform a given action on every declaration in a given rel-context. *)
  val iter : (Constr.t -> unit) -> t -> unit

  (** Return the number of {e local declarations} in a given context. *)
  val length : t -> int

  (** Return the number of {e local assumptions} in a given rel-context. *)
  val nhyps : t -> int

  (** Map a given rel-context to a list where each {e local assumption} is mapped to [true]
      and each {e local definition} is mapped to [false]. *)
  val to_tags : t -> bool list

  (** [extended_list n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args]. Example: for [x:T, y:=c, z:U] and [n]=2, it gives [Rel 5, Rel 3]. *)
  val to_extended_list : int -> t -> Constr.t list

  (** [extended_vect n Γ] does the same, returning instead an array. *)
  val to_extended_vect : int -> t -> Constr.t array
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named :
sig
  (** Representation of {e local declarations}.

      [(id, None, typ)] represents a {e local assumption}.

      [(id, Some value, typ)] represents a {e local definition}.
   *)
  module Declaration :
  sig
    type t = Id.t * Constr.t option * Constr.t

    (** Map all terms in a given declaration. *)
    val map : (Constr.t -> Constr.t) -> t -> t

    (** Reduce all terms in a given declaration to a single value. *)
    val fold : (Constr.t -> 'a -> 'a) -> t -> 'a -> 'a

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : (Constr.t -> bool) -> t -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : (Constr.t -> bool) -> t -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : t -> t -> bool
  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type t = Declaration.t list

  (** empty named-context *)
  val empty : t

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  val add : Declaration.t -> t -> t

  (** Return a declaration designated by an identifier of the variable bound in that declaration.
      @raise Not_found if the designated identifier is not bound in a given named-context. *)
  val lookup : Id.t -> t -> Declaration.t

  (** Map all terms in a given named-context. *)
  val map : (Constr.t -> Constr.t) -> t -> t

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> Declaration.t -> 'a) -> init:'a -> t -> 'a

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a

  (** Perform a given action on every declaration in a given named-context. *)
  val iter : (Constr.t -> unit) -> t -> unit

  (** Return the number of {e local declarations} in a given named-context. *)
  val length : t -> int

  (** Check whether given two named-contexts are equal. *)
  val equal : t -> t -> bool

  (** Return the set of all identifiers bound in a given named-context. *)
  val to_vars : t -> Id.Set.t

  (** [instance_from_named_context Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  val to_instance : t -> Constr.t list
end

module NamedList :
sig
  module Declaration :
  sig
    type t = Id.t list * Constr.t option * Constr.t
    val map : (Constr.t -> Constr.t) -> t -> t
  end

  type t = Declaration.t list

  val fold : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a
end

type section_context = Named.t
