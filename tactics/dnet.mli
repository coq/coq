(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Generic discrimination net implementation over recursive
   types. This module implements a association data structure similar
   to tries but working on any types (not just lists). It is a term
   indexing datastructure, a generalization of the discrimination nets
   described for example in W.W.McCune, 1992, related also to
   generalized tries [Hinze, 2000].

   You can add pairs of (term,identifier) into a dnet, where the
   identifier is *unique*, and search terms in a dnet filtering a
   given pattern (retrievial of instances). It returns all identifiers
   associated with terms matching the pattern. It also works the other
   way around : You provide a set of patterns and a term, and it
   returns all patterns which the term matches (retrievial of
   generalizations). That's why you provide *patterns* everywhere.

   Warning 1: Full unification doesn't work as for now. Make sure the
   set of metavariables in the structure and in the queries are
   distincts, or you'll get unexpected behaviours.

   Warning 2: This structure is perfect, i.e. the set of candidates
   returned is equal to the set of solutions. Beware of de Bruijn
   shifts and sorts subtyping though (which makes the comparison not
   symmetric, see term_dnet.ml).

   The complexity of the search is (almost) the depth of the term.

   To use it, you have to provide a module (Datatype) with the datatype
   parametrized on the recursive argument. example:

   type btree =                      type 'a btree0 =
   | Leaf                    ===>    | Leaf
   | Node of btree * btree           | Node of 'a * 'a

*)

(** datatype you want to build a dnet on *)
module type Datatype =
sig
  (** parametric datatype. ['a] is morally the recursive argument *)
  type 'a t

  (** non-recursive mapping of subterms *)
  val map : ('a -> 'b) -> 'a t -> 'b t
  val map2 : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  (** non-recursive folding of subterms *)
  val fold : ('a -> 'b -> 'a) -> 'a -> 'b t -> 'a
  val fold2 : ('a -> 'b -> 'c -> 'a) -> 'a -> 'b t -> 'c t -> 'a

  (** comparison of constructors *)
  val compare : unit t -> unit t -> int

  (** for each constructor, is it not-parametric on 'a? *)
  val terminal : 'a t -> bool

  (** [choose f w] applies f on ONE of the subterms of w *)
  val choose : ('a -> 'b) -> 'a t -> 'b
end

module type S =
sig
  type t

  (** provided identifier type *)
  type ident

  (** provided metavariable type *)
  type meta

  (** provided parametrized datastructure *)
  type 'a structure

  (** returned sets of solutions *)
  module Idset : Set.S with type elt=ident

  (** a pattern is a term where each node can be a unification
     variable *)
  type term_pattern =
    | Term of term_pattern structure
    | Meta of meta

  val empty : t

  (** [add t w i] adds a new association (w,i) in t. *)
  val add : t -> term_pattern -> ident -> t

  (** [find_all t] returns all identifiers contained in t. *)
  val find_all : t -> Idset.t

  (** [fold_pattern f acc p dn] folds f on each meta of p, passing the
     meta and the sub-dnet under it. The result includes:
     - Some set if identifiers were gathered on the leafs of the term
     - None if the pattern contains no leaf (only Metas at the leafs).
  *)
  val fold_pattern :
    ('a -> (Idset.t * meta * t) -> 'a) -> 'a -> term_pattern -> t -> Idset.t option * 'a

  (** [find_match p t] returns identifiers of all terms matching p in
     t. *)
  val find_match : term_pattern -> t -> Idset.t

  (** set operations on dnets *)
  val inter : t -> t -> t
  val union : t -> t -> t

  (** apply a function on each identifier and node of terms in a dnet *)
  val map : (ident -> ident) -> (unit structure -> unit structure) -> t -> t

  val map_metas : (meta -> meta) -> t -> t
end

module Make :
  functor (T:Datatype) ->
  functor (Ident:Set.OrderedType) ->
  functor (Meta:Set.OrderedType) ->
    S with type ident = Ident.t
      and  type meta = Meta.t
      and  type 'a structure = 'a T.t
