(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
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

type ('a,'r) pbinder_annot = { binder_name : 'a; binder_relevance : 'r }

val eq_annot : ('a -> 'a -> bool) -> ('r -> 'r -> bool) ->
  ('a,'r) pbinder_annot -> ('a,'r) pbinder_annot -> bool

val hash_annot : ('a -> int) -> ('a,Sorts.relevance) pbinder_annot -> int

val map_annot : ('a -> 'b) -> ('a,'r) pbinder_annot -> ('b,'r) pbinder_annot

val map_annot_relevance : ('r -> 'r) -> ('a,'r) pbinder_annot -> ('a,'r) pbinder_annot

val map_annot_relevance_het : ('r1 -> 'r2) -> ('a,'r1) pbinder_annot -> ('a,'r2) pbinder_annot

val make_annot : 'a -> 'r -> ('a,'r) pbinder_annot

val binder_name : ('a,'r) pbinder_annot -> 'a
val binder_relevance : ('a,'r) pbinder_annot -> 'r

val annotR : 'a -> ('a,Sorts.relevance) pbinder_annot
(** Always Relevant *)

val nameR : Id.t -> (Name.t,Sorts.relevance) pbinder_annot
(** Relevant + Name *)

val anonR : (Name.t,Sorts.relevance) pbinder_annot
(** Relevant + Anonymous *)

(** Representation of contexts that can capture anonymous as well as non-anonymous variables.
    Individual declarations are then designated by de Bruijn indexes. *)
module Rel :
sig
  module Declaration :
  sig
    (* local declaration *)
    type ('constr, 'types, 'r) pt =
    | LocalAssum of (Name.t,'r) pbinder_annot * 'types            (** name, type *)
    | LocalDef of (Name.t,'r) pbinder_annot * 'constr * 'types   (** name, value, type *)

    val get_annot : (_,_,'r) pt -> (Name.t,'r) pbinder_annot

    (** Return the name bound by a given declaration. *)
    val get_name : ('c, 't,'r) pt -> Name.t

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    val get_value : ('c, 't, 'r) pt -> 'c option

    (** Return the type of the name bound by a given declaration. *)
    val get_type : ('c, 't, 'r) pt -> 't

    val get_relevance : ('c, 't, 'r) pt -> 'r

    val set_annot : (Name.t,'r) pbinder_annot -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Set the name that is bound by a given declaration. *)
    val set_name : Name.t -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Set the type of the bound variable in a given declaration. *)
    val set_type : 't -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Return [true] iff a given declaration is a local assumption. *)
    val is_local_assum : ('c, 't, 'r) pt -> bool

    (** Return [true] iff a given declaration is a local definition. *)
    val is_local_def : ('c, 't, 'r) pt -> bool

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : ('c -> bool) -> ('c, 'c, 'r) pt -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : ('c -> bool) -> ('c, 'c, 'r) pt -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : ('r -> 'r -> bool) -> ('c -> 'c -> bool) ->
      ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt -> bool

    (** Map the name bound by a given declaration. *)
    val map_name : (Name.t -> Name.t) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Map the relevance *)
    val map_relevance : ('r -> 'r) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    val map_value : ('c -> 'c) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Map the type of the name bound by a given declaration. *)
    val map_type : ('t -> 't) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Map all terms in a given declaration. *)
    val map_constr : ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

    (** Map all terms in a given declaration. *)
    val map_constr_with_relevance : ('r -> 'r) -> ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

    (** Map all terms, with an heterogeneous function. *)
    val map_constr_het : ('r1 -> 'r2) -> ('a -> 'b) -> ('a, 'a, 'r1) pt -> ('b, 'b, 'r2) pt

    (** Perform a given action on all terms in a given declaration. *)
    val iter_constr : ('c -> unit) -> ('c, 'c, 'r) pt -> unit

    (** Reduce all terms in a given declaration to a single value. *)
    val fold_constr : ('c -> 'a -> 'a) -> ('c, 'c, 'r) pt -> 'a -> 'a

    val to_tuple : ('c, 't, 'r) pt -> (Name.t,'r) pbinder_annot * 'c option * 't

    (** Turn [LocalDef] into [LocalAssum], identity otherwise. *)
    val drop_body : ('c, 't, 'r) pt -> ('c, 't, 'r) pt
  end

  (** Rel-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types, 'r) pt = ('constr, 'types, 'r) Declaration.pt list

  (** empty rel-context *)
  val empty : ('c, 't, 'r) pt

  (** Return a new rel-context enriched by with a given inner-most declaration. *)
  val add : ('c, 't, 'r) Declaration.pt -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

  (** Return the number of {e local declarations} in a given rel-context. *)
  val length : ('c, 't, 'r) pt -> int

  (** Check whether given two rel-contexts are equal. *)
  val equal : ('r -> 'r -> bool) -> ('c -> 'c -> bool) ->
    ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt -> bool

  (** Return the number of {e local assumptions} in a given rel-context. *)
  val nhyps : ('c, 't, 'r) pt -> int

  (** Return a declaration designated by a given de Bruijn index.
      @raise Not_found if the designated de Bruijn index outside the range. *)
  val lookup : int -> ('c, 't, 'r) pt -> ('c, 't, 'r) Declaration.pt

  (** Map all terms in a given rel-context. *)
  val map : ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

  (** Map all terms in a given rel-context. *)
  val map_with_relevance : ('r -> 'r) -> ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

  (** Map all terms in a given named-context. *)
  val map_het : ('r1 -> 'r2) -> ('c -> 'd) -> ('c, 'c, 'r1) pt -> ('d, 'd, 'r2) pt

  (** Map all terms in a given rel-context taking into account the
      position of the binder in the context starting at 1. *)
  val map_with_binders : (int -> 'c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

  (** Perform a given action on every declaration in a given rel-context. *)
  val iter : ('c -> unit) -> ('c, 'c, 'r) pt -> unit

  (** Reduce all terms in a given rel-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> ('c, 't, 'r) Declaration.pt -> 'a) -> init:'a -> ('c, 't, 'r) pt -> 'a

  (** Reduce all terms in a given rel-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (('c, 't, 'r) Declaration.pt -> 'a -> 'a) -> ('c, 't, 'r) pt -> init:'a -> 'a

  (** Return the set of all named variables bound in a given rel-context. *)
  val to_vars : ('c, 't, 'r) pt -> Id.Set.t

  (** Map a given rel-context to a list where each {e local
      assumption} is mapped to [true] and each {e local definition} is
      mapped to [false]. The resulting list is in reverse order
      compared to the order of declarations in the context. *)
  val to_tags : ('c, 't, 'r) pt -> bool list

  (** Turn all [LocalDef] into [LocalAssum], leave [LocalAssum] unchanged. *)
  val drop_bodies : ('c, 't, 'r) pt -> ('c, 't, 'r) pt

  (** [chop_nhyps n Γ] returns [Γ'',Γ'] such that [Γ]=[Γ'Γ''], [Γ''] has
      [n] hypotheses (i.e. [LocalAssum]), excluding local definitions
      (i.e. [LocalDef]), and [Γ''], if [n] non zero, starts with an
      hypothesis (i.e., [Γ''] has the form [x:A;Γ'''], i.e., local
      definitions at the junction of the [n] hypotheses are put in
      [Γ'] rather than in [Γ''] *)
  val chop_nhyps : int -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt * ('c, 't, 'r) pt

  (** [instance mk n Γ] builds an instance [args] such that [Γ,Δ ⊢ args:Γ]
      with n = |Δ| and with the {e local definitions} of [Γ] skipped in
      [args] where [mk] is used to build the corresponding variables.
      Example: for [x:T, y:=c, z:U] and [n]=2, it gives [mk 5, mk 3]. *)
  val instance : (int -> 'v) -> int -> ('c, 't, 'r) pt -> 'v array

  (** [instance_list] is like [instance] but returning a list. *)
  val instance_list : (int -> 'v) -> int -> ('c, 't, 'r) pt -> 'v list

  val to_extended_vect : (int -> 'r) -> int -> ('c, 't, 'r) pt -> 'r array
    [@@ocaml.deprecated "(8.15) Use synonymous [Context.Rel.instance]"]

  val to_extended_list : (int -> 'r) -> int -> ('c, 't, 'r) pt -> 'r list
    [@@ocaml.deprecated "(8.15) Use synonymous [Context.Rel.instance_list]"]
end

(** This module represents contexts that can capture non-anonymous variables.
    Individual declarations are then designated by the identifiers they bind. *)
module Named :
sig
  (** Representation of {e local declarations}. *)
  module Declaration :
  sig
    type ('constr, 'types, 'r) pt =
      | LocalAssum of (Id.t,'r) pbinder_annot * 'types             (** identifier, type *)
      | LocalDef of (Id.t,'r) pbinder_annot * 'constr * 'types    (** identifier, value, type *)

    val get_annot : (_,_,'r) pt -> (Id.t,'r) pbinder_annot

    (** Return the identifier bound by a given declaration. *)
    val get_id : ('c, 't, 'r) pt -> Id.t

    (** Return [Some value] for local-declarations and [None] for local-assumptions. *)
    val get_value : ('c, 't, 'r) pt -> 'c option

    (** Return the type of the name bound by a given declaration. *)
    val get_type : ('c, 't, 'r) pt -> 't

    val get_relevance : ('c, 't, 'r) pt -> 'r

    (** Set the identifier that is bound by a given declaration. *)
    val set_id : Id.t -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Set the type of the bound variable in a given declaration. *)
    val set_type : 't -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Return [true] iff a given declaration is a local assumption. *)
    val is_local_assum : ('c, 't, 'r) pt -> bool

    (** Return [true] iff a given declaration is a local definition. *)
    val is_local_def : ('c, 't, 'r) pt -> bool

    (** Check whether any term in a given declaration satisfies a given predicate. *)
    val exists : ('c -> bool) -> ('c, 'c, 'r) pt -> bool

    (** Check whether all terms in a given declaration satisfy a given predicate. *)
    val for_all : ('c -> bool) -> ('c, 'c, 'r) pt -> bool

    (** Check whether the two given declarations are equal. *)
    val equal : ('r -> 'r -> bool) -> ('c -> 'c -> bool) ->
      ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt -> bool

    (** Map the identifier bound by a given declaration. *)
    val map_id : (Id.t -> Id.t) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** For local assumptions, this function returns the original local assumptions.
        For local definitions, this function maps the value in the local definition. *)
    val map_value : ('c -> 'c) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Map the type of the name bound by a given declaration. *)
    val map_type : ('t -> 't) -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Map all terms in a given declaration. *)
    val map_constr : ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

    (** Map all terms in a given declaration. *)
    val map_constr_with_relevance : ('r -> 'r) -> ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

    (** Map all terms, with an heterogeneous function. *)
    val map_constr_het : ('r1 -> 'r2) -> ('a -> 'b) -> ('a, 'a, 'r1) pt -> ('b, 'b, 'r2) pt

    (** Perform a given action on all terms in a given declaration. *)
    val iter_constr : ('c -> unit) -> ('c, 'c, 'r) pt -> unit

    (** Reduce all terms in a given declaration to a single value. *)
    val fold_constr : ('c -> 'a -> 'a) -> ('c, 'c, 'r) pt -> 'a -> 'a

    val to_tuple : ('c, 't, 'r) pt -> (Id.t,'r) pbinder_annot * 'c option * 't
    val of_tuple : (Id.t,'r) pbinder_annot * 'c option * 't -> ('c, 't, 'r) pt

    (** Turn [LocalDef] into [LocalAssum], identity otherwise. *)
    val drop_body : ('c, 't, 'r) pt -> ('c, 't, 'r) pt

    (** Convert [Rel.Declaration.t] value to the corresponding [Named.Declaration.t] value.
        The function provided as the first parameter determines how to translate "names" to "ids". *)
    val of_rel_decl : (Name.t -> Id.t) -> ('c, 't, 'r) Rel.Declaration.pt -> ('c, 't, 'r) pt

    (** Convert [Named.Declaration.t] value to the corresponding [Rel.Declaration.t] value. *)
    (* TODO: Move this function to [Rel.Declaration] module and rename it to [of_named]. *)
    val to_rel_decl : ('c, 't, 'r) pt -> ('c, 't, 'r) Rel.Declaration.pt
  end

  (** Named-context is represented as a list of declarations.
      Inner-most declarations are at the beginning of the list.
      Outer-most declarations are at the end of the list. *)
  type ('constr, 'types, 'r) pt = ('constr, 'types, 'r) Declaration.pt list

  (** empty named-context *)
  val empty : ('c, 't, 'r) pt

  (** Return a new named-context enriched by with a given inner-most declaration. *)
  val add : ('c, 't, 'r) Declaration.pt -> ('c, 't, 'r) pt -> ('c, 't, 'r) pt

  (** Return the number of {e local declarations} in a given named-context. *)
  val length : ('c, 't, 'r) pt -> int

  (** Return a declaration designated by an identifier of the variable bound in that declaration.
      @raise Not_found if the designated identifier is not bound in a given named-context. *)
  val lookup : Id.t -> ('c, 't, 'r) pt -> ('c, 't, 'r) Declaration.pt

  (** Check whether given two named-contexts are equal. *)
  val equal : ('r -> 'r -> bool) -> ('c -> 'c -> bool) ->
    ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt -> bool

  (** Map all terms in a given named-context. *)
  val map : ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

  (** Map all terms in a given rel-context. *)
  val map_with_relevance : ('r -> 'r) -> ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt

  (** Map all terms in a given named-context. *)
  val map_het : ('r1 -> 'r2) -> ('c -> 'd) -> ('c, 'c, 'r1) pt -> ('d, 'd, 'r2) pt

  (** Perform a given action on every declaration in a given named-context. *)
  val iter : ('c -> unit) -> ('c, 'c, 'r) pt -> unit

  (** Reduce all terms in a given named-context to a single value.
      Innermost declarations are processed first. *)
  val fold_inside : ('a -> ('c, 't, 'r) Declaration.pt -> 'a) -> init:'a -> ('c, 't, 'r) pt -> 'a

  (** Reduce all terms in a given named-context to a single value.
      Outermost declarations are processed first. *)
  val fold_outside : (('c, 't, 'r) Declaration.pt -> 'a -> 'a) -> ('c, 't, 'r) pt -> init:'a -> 'a

  (** Return the set of all identifiers bound in a given named-context. *)
  val to_vars : ('c, 't, 'r) pt -> Id.Set.t

  (** Turn all [LocalDef] into [LocalAssum], leave [LocalAssum] unchanged. *)
  val drop_bodies : ('c, 't, 'r) pt -> ('c, 't, 'r) pt

  (** [to_instance Ω] builds an instance [args] in reverse order such
      that [Ω ⊢ args:Ω] where [Ω] is a named-context and with the local
      definitions of [Ω] skipped. Example: for [id1:T,id2:=c,id3:U], it
      gives [Var id1, Var id3]. All [idj] are supposed distinct. *)
  val to_instance : (Id.t -> 'v) -> ('c, 't, 'r) pt -> 'v list
    [@@ocaml.deprecated "(8.15) [to_instance] was missing a [List.rev] to comply to its specification; rely on [instance] for the correct specification or use [List.rev (instance ...)] for strict compatibility"]

  (** [instance Ω] builds an instance [args] such
      that [Ω ⊢ args:Ω] where [Ω] is a named-context and with the
      local definitions of [Ω] skipped. Example: for the context
      [id1:T,id2:=c,id3:U] (which is internally represented by a list
      with [id3] at the head), it gives [Var id1, Var id3]. All [idj]
      are supposed distinct. *)
  val instance : (Id.t -> 'v) -> ('c, 't, 'r) pt -> 'v array

  (** [instance_list] is like [instance] but returning a list. *)
  val instance_list : (Id.t -> 'v) -> ('c, 't, 'r) pt -> 'v list
end

module Compacted :
sig
  module Declaration :
  sig
    type ('constr, 'types, 'r) pt =
      | LocalAssum of (Id.t,'r) pbinder_annot list * 'types
      | LocalDef of (Id.t,'r) pbinder_annot list * 'constr * 'types

    val map_constr : ('c -> 'c) -> ('c, 'c, 'r) pt -> ('c, 'c, 'r) pt
    val of_named_decl : ('c, 't, 'r) Named.Declaration.pt -> ('c, 't, 'r) pt
    val to_named_context : ('c, 't, 'r) pt -> ('c, 't, 'r) Named.pt
  end

  type ('constr, 'types, 'r) pt = ('constr, 'types, 'r) Declaration.pt list

  val fold : (('c, 't, 'r) Declaration.pt -> 'a -> 'a) -> ('c, 't, 'r) pt -> init:'a -> 'a
end
