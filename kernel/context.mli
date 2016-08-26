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
  module Declaration :
  sig
    (* local declaration *)
    type t = LocalAssum of Name.t * Constr.t            (** name, type *)
           | LocalDef of Name.t * Constr.t * Constr.t   (** name, value, type *)

    (** Return the name bound by a given declaration. *)
    val get_name : t -> Name.t

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    val get_value : t -> Constr.t option

    (** Return the type of the name bound by a given declaration. *)
    val get_type : t -> Constr.t

    (** Set the name that is bound by a given declaration. *)
    val set_name : Name.t -> t -> t

    (** Set the type of the bound variable in a given declaration. *)
    val set_type : Constr.t -> t -> t

    (** Return [true] iff a given declaration is a local assumption. *)
    val is_local_assum : t -> bool

    (** Return [true] iff a given declaration is a local definition. *)
    val is_local_def : t -> bool

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : (Constr.t -> bool) -> t -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : (Constr.t -> bool) -> t -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : t -> t -> bool

    (** Map the name bound by a given declaration. *)
    val map_name : (Name.t -> Name.t) -> t -> t

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    val map_value : (Constr.t -> Constr.t) -> t -> t

    (** Map the type of the name bound by a given declaration. *)
    val map_type : (Constr.t -> Constr.t) -> t -> t

    (** Map all terms in a given declaration. *)
    val map_constr : (Constr.t -> Constr.t) -> t -> t

    (** Perform a given action on all terms in a given declaration. *)
    val iter_constr : (Constr.t -> unit) -> t -> unit

    (** Reduce all terms in a given declaration to a single value. *)
    val fold_constr : (Constr.t -> 'a -> 'a) -> t -> 'a -> 'a

    val to_tuple : t -> Name.t * Constr.t option * Constr.t
  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type t = Declaration.t list

  (** empty rel-context *)
  val empty : t

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  val add : Declaration.t -> t -> t

  (** Return the number of {e local declarations} in a given context. *)
  val length : t -> int

  (** Check whether given two rel-contexts are equal. *)
  val equal : t -> t -> bool

  (** Return the number of {e local assumptions} in a given rel-context. *)
  val nhyps : t -> int

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index outside the range. *)
  val lookup : int -> t -> Declaration.t

  (** Map all terms in a given rel-context. *)
  val map : (Constr.t -> Constr.t) -> t -> t

  (** Perform a given action on every declaration in a given rel-context. *)
  val iter : (Constr.t -> unit) -> t -> unit

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> Declaration.t -> 'a) -> init:'a -> t -> 'a

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a

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
  (** Representation of {e local declarations}. *)
  module Declaration :
  sig
    type t = LocalAssum of Id.t * Constr.t            (** identifier, type *)
           | LocalDef of Id.t * Constr.t * Constr.t   (** identifier, value, type *)

    (** Return the identifier bound by a given declaration. *)
    val get_id : t -> Id.t

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    val get_value : t -> Constr.t option

    (** Return the type of the name bound by a given declaration. *)
    val get_type : t -> Constr.t

    (** Set the identifier that is bound by a given declaration. *)
    val set_id : Id.t -> t -> t

    (** Set the type of the bound variable in a given declaration. *)
    val set_type : Constr.t -> t -> t

    (** Return [true] iff a given declaration is a local assumption. *)
    val is_local_assum : t -> bool

    (** Return [true] iff a given declaration is a local definition. *)
    val is_local_def : t -> bool

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : (Constr.t -> bool) -> t -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : (Constr.t -> bool) -> t -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : t -> t -> bool

    (** Map the identifier bound by a given declaration. *)
    val map_id : (Id.t -> Id.t) -> t -> t

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    val map_value : (Constr.t -> Constr.t) -> t -> t

    (** Map the type of the name bound by a given declaration. *)
    val map_type : (Constr.t -> Constr.t) -> t -> t

    (** Map all terms in a given declaration. *)
    val map_constr : (Constr.t -> Constr.t) -> t -> t

    (** Perform a given action on all terms in a given declaration. *)
    val iter_constr : (Constr.t -> unit) -> t -> unit

    (** Reduce all terms in a given declaration to a single value. *)
    val fold_constr : (Constr.t -> 'a -> 'a) -> t -> 'a -> 'a

    val to_tuple : t -> Id.t * Constr.t option * Constr.t
    val of_tuple : Id.t * Constr.t option * Constr.t -> t

    (** Convert [Rel.Declaration.t] value to the corresponding [Named.Declaration.t] value.
        The function provided as the first parameter determines how to translate "names" to "ids". *)
    val of_rel_decl : (Name.t -> Id.t) -> Rel.Declaration.t -> t

    (** Convert [Named.Declaration.t] value to the corresponding [Rel.Declaration.t] value. *)
    (* TODO: Move this function to [Rel.Declaration] module and rename it to [of_named]. *)
    val to_rel_decl : t -> Rel.Declaration.t
  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type t = Declaration.t list

  (** empty named-context *)
  val empty : t

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  val add : Declaration.t -> t -> t

  (** Return the number of {e local declarations} in a given named-context. *)
  val length : t -> int

  (** Return a declaration designated by an identifier of the variable bound in that declaration.
      @raise Not_found if the designated identifier is not bound in a given named-context. *)
  val lookup : Id.t -> t -> Declaration.t

  (** Check whether given two rel-contexts are equal. *)
  val equal : t -> t -> bool

  (** Map all terms in a given named-context. *)
  val map : (Constr.t -> Constr.t) -> t -> t

  (** Perform a given action on every declaration in a given named-context. *)
  val iter : (Constr.t -> unit) -> t -> unit

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> Declaration.t -> 'a) -> init:'a -> t -> 'a

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a

  (** Return the set of all identifiers bound in a given named-context. *)
  val to_vars : t -> Id.Set.t

  (** [instance_from_named_context Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  val to_instance : t -> Constr.t list
end

module Compacted :
sig
  module Declaration :
  sig
    type t =
      | LocalAssum of Id.t list * Constr.t
      | LocalDef of Id.t list * Constr.t * Constr.t

    val map_constr : (Constr.t -> Constr.t) -> t -> t
    val of_named_decl : Named.Declaration.t -> t
    val to_named_context : t -> Named.t
  end

  type t = Declaration.t list

  val fold : (Declaration.t -> 'a -> 'a) -> t -> init:'a -> 'a
end
