(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Univ

(** {6 Support for universe polymorphism } *)

module Variance :
sig
  (** A universe position in the instance given to a cumulative
     inductive can be the following. Note there is no Contravariant
     case because [forall x : A, B <= forall x : A', B'] requires [A =
     A'] as opposed to [A' <= A]. *)
  type t = Irrelevant | Covariant | Invariant

  (** [check_subtype x y] holds if variance [y] is also an instance of [x] *)
  val check_subtype : t -> t -> bool

  val sup : t -> t -> t

  val pr : t -> Pp.t

  val equal : t -> t -> bool

end

(** {6 Universe instances} *)

module Instance :
sig
  type t
  (** A universe instance represents a vector of argument universes
      to a polymorphic definition (constant, inductive or constructor). *)

  val empty : t
  val is_empty : t -> bool

  val of_array : Level.t array -> t
  val to_array : t -> Level.t array

  val append : t -> t -> t
  (** To concatenate two instances, used for discharge *)

  val equal : t -> t -> bool
  (** Equality *)

  val length : t -> int
  (** Instance length *)

  val hcons : t -> t
  (** Hash-consing. *)

  val hash : t -> int
  (** Hash value *)

  val share : t -> t * int
  (** Simultaneous hash-consing and hash-value computation *)

  val pr : (Level.t -> Pp.t) -> ?variance:Variance.t array -> t -> Pp.t
  (** Pretty-printing, no comments *)

  val levels : t -> Level.Set.t
  (** The set of levels in the instance *)

end

val enforce_eq_instances : Instance.t constraint_function

val enforce_eq_variance_instances : Variance.t array -> Instance.t constraint_function
val enforce_leq_variance_instances : Variance.t array -> Instance.t constraint_function

type 'a puniverses = 'a * Instance.t
val out_punivs : 'a puniverses -> 'a
val in_punivs : 'a -> 'a puniverses

val eq_puniverses : ('a -> 'a -> bool) -> 'a puniverses -> 'a puniverses -> bool

(** A vector of universe levels with universe Constraints.t,
    representing local universe variables and associated Constraints.t;
    the names are user-facing names for printing *)

module UContext :
sig
  type t

  val make : Names.Name.t array -> Instance.t constrained -> t

  val empty : t
  val is_empty : t -> bool

  val instance : t -> Instance.t
  val constraints : t -> Constraints.t

  val union : t -> t -> t
  (** Keeps the order of the instances *)

  val size : t -> int
  (** The number of universes in the context *)

  val names : t -> Names.Name.t array
  (** Return the user names of the universes *)

  val refine_names : Names.Name.t array -> t -> t
  (** Use names to name the possibly yet unnamed universes *)

  val sort_levels : Level.t array -> Level.t array
  (** Arbitrary choice of linear order of the variables *)

  val of_context_set : (Instance.t -> Names.Name.t array) -> ContextSet.t -> t
  (** Build a vector of universe levels assuming a function generating names *)

  val to_context_set : t -> ContextSet.t
  (** Discard the names and order of the universes *)

end
(** A value in a universe context. *)
type 'a in_universe_context = 'a * UContext.t

module AbstractContext :
sig
  type t
  (** An abstract context serves to quantify over a graph of universes
      represented using de Bruijn indices, as in:
      u0, ..., u(n-1), Var i < Var j, .., Var k <= Var l |- term(Var 0 .. Var (n-1))
      \-------------/  \-------------------------------/    \---------------------/
      names for        constraints expressed on de Bruijn   judgement in abstract
      printing         representation of the n univ vars    context expected to
                                                            use de Bruijn indices
  *)

  val make : Names.Name.t array -> Constraints.t -> t
  (** Build an abstract context. Constraints may be between universe
     variables. *)

  val repr : t -> UContext.t
  (** [repr ctx] is [(Var(0), ... Var(n-1) |= cstr] where [n] is the length of
      the context and [cstr] the abstracted Constraints.t. *)

  val empty : t
  val is_empty : t -> bool

  val size : t -> int

  val union : t -> t -> t
  (** The constraints are expected to be relative to the concatenated set of universes *)

  val instantiate : Instance.t -> t -> Constraints.t
  (** Generate the set of instantiated Constraints.t **)

  val names : t -> Names.Name.t array
  (** Return the names of the bound universe variables *)

end

type 'a univ_abstracted = {
  univ_abstracted_value : 'a;
  univ_abstracted_binder : AbstractContext.t;
}
(** A value with bound universe levels. *)

val map_univ_abstracted : ('a -> 'b) -> 'a univ_abstracted -> 'b univ_abstracted

(** {6 Substitution} *)

val subst_univs_level_abstract_universe_context :
  universe_level_subst -> AbstractContext.t -> AbstractContext.t
val subst_univs_level_instance : universe_level_subst -> Instance.t -> Instance.t
(** Level to universe substitutions. *)

(** Substitution of instances *)
val subst_instance_instance : Instance.t -> Instance.t -> Instance.t
val subst_instance_universe : Instance.t -> Universe.t -> Universe.t
val subst_instance_sort : Instance.t -> Sorts.t -> Sorts.t

val make_instance_subst : Instance.t -> universe_level_subst
(** Creates [u(0) ↦ 0; ...; u(n-1) ↦ n - 1] out of [u(0); ...; u(n - 1)] *)

val abstract_universes : UContext.t -> Instance.t * AbstractContext.t
(** TODO: move universe abstraction out of the kernel *)

val make_abstract_instance : AbstractContext.t -> Instance.t

(** {6 Pretty-printing of universes. } *)

val pr_universe_context : (Level.t -> Pp.t) -> ?variance:Variance.t array ->
  UContext.t -> Pp.t
val pr_abstract_universe_context : (Level.t -> Pp.t) -> ?variance:Variance.t array ->
  AbstractContext.t -> Pp.t

(** {6 Hash-consing } *)

val hcons_universe_context : UContext.t -> UContext.t
val hcons_abstract_universe_context : AbstractContext.t -> AbstractContext.t
