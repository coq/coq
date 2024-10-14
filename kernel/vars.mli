(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr

(** {6 Occur checks } *)

(** [closedn n M] is true iff [M] is a (de Bruijn) closed term under n binders *)
val closedn : int -> constr -> bool

(** [closed0 M] is true iff [M] is a (de Bruijn) closed term *)
val closed0 : constr -> bool

(** [noccurn n M] returns true iff [Rel n] does NOT occur in term [M]  *)
val noccurn : int -> constr -> bool

(** [noccur_between n m M] returns true iff [Rel p] does NOT occur in term [M]
  for n <= p < n+m *)
val noccur_between : int -> int -> constr -> bool

(** Checking function for terms containing existential- or
   meta-variables.  The function [noccur_with_meta] does not consider
   meta-variables applied to some terms (intended to be its local
   context) (for existential variables, it is necessarily the case) *)
val noccur_with_meta : int -> int -> constr -> bool

(** {6 Relocation and substitution } *)

(** [exliftn el c] lifts [c] with arbitrary complex lifting [el] *)
val exliftn : Esubst.lift -> constr -> constr

(** [liftn n k c] lifts by [n] indices greater than or equal to [k] in [c]
   Note that with respect to substitution calculi's terminology, [n]
   is the _shift_ and [k] is the _lift_. *)
val liftn : int -> int -> constr -> constr

(** [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> constr -> constr

(** Same as [liftn] for a context *)
val liftn_rel_context : int -> int -> rel_context -> rel_context

(** Same as [lift] for a context *)
val lift_rel_context : int -> rel_context -> rel_context

(** The type [substl] is the type of substitutions [u₁..un] of type
    some well-typed context Δ and defined in some environment Γ.
    Typing of substitutions is defined by:
    - Γ ⊢ ∅ : ∅,
    - Γ ⊢ u₁..u{_n-1} : Δ and Γ ⊢ u{_n} : An\[u₁..u{_n-1}\] implies
      Γ ⊢ u₁..u{_n} : Δ,x{_n}:A{_n}
    - Γ ⊢ u₁..u{_n-1} : Δ and Γ ⊢ un : A{_n}\[u₁..u{_n-1}\] implies
      Γ ⊢ u₁..u{_n} : Δ,x{_n}:=c{_n}:A{_n} when Γ ⊢ u{_n} ≡ c{_n}\[u₁..u{_n-1}\]

    Note that [u₁..un] is represented as a list with [un] at the head of
    the list, i.e. as [[un;...;u₁]].

    A [substl] differs from an [instance] in that it includes the
    terms bound by lets while the latter does not. Also, their
    internal representations are in opposite order. *)

type substl = constr list

(** The type [instance] is the type of instances [u₁..un] of a
    well-typed context Δ (relatively to some environment Γ). Typing of
    instances is defined by:
    - Γ ⊢ ∅ : ∅,
    - Γ ⊢ u₁..u{_n} : Δ and Γ ⊢ u{_n+1} : A{_n+1}\[ϕ(Δ,u₁..u{_n})\] implies
      Γ ⊢ u₁..u{_n+1} : Δ,x{_n+1}:A{_n+1}
    - Γ ⊢ u₁..u{_n} : Δ implies
      Γ ⊢ u₁..u{_n} : Δ,x{_n+1}:=c{_n+1}:A{_n+1}
    where [ϕ(Δ,u₁..u{_n})] is the substitution obtained by adding lets
    of Δ to the instance so as to get a substitution (see
    [subst_of_rel_context_instance] below).

    Note that [u₁..un] is represented as an array with [u1] at the
    head of the array, i.e. as [[u₁;...;un]]. In particular, it can
    directly be used with [mkApp] to build an applicative term
    [f u₁..un] whenever [f] is of some type [forall Δ, T].

    An [instance] differs from a [substl] in that it does not include
    the terms bound by lets while the latter does. Also, their
    internal representations are in opposite order.

    An [instance_list] is the same as an [instance] but using a list
    instead of an array. *)

type instance = constr array
type instance_list = constr list

(** Let [Γ] be a context interleaving declarations [x₁:T₁..xn:Tn]
   and definitions [y₁:=c₁..yp:=cp] in some context [Γ₀]. Let
   [u₁..un] be an {e instance} of [Γ], i.e. an instance in [Γ₀]
   of the [xi]. Then, [subst_of_rel_context_instance_list Γ u₁..un]
   returns the corresponding {e substitution} of [Γ], i.e. the
   appropriate interleaving [σ] of the [u₁..un] with the [c₁..cp],
   all of them in [Γ₀], so that a derivation [Γ₀, Γ, Γ₁|- t:T]
   can be instantiated into a derivation [Γ₀, Γ₁ |- t[σ]:T[σ]] using
   [substnl σ |Γ₁| t].
   Note that the instance [u₁..un] is represented starting with [u₁],
   as if usable in [applist] while the substitution is
   represented the other way round, i.e. ending with either [u₁] or
   [c₁], as if usable for [substl]. *)
val subst_of_rel_context_instance : Constr.rel_context -> instance -> substl
val subst_of_rel_context_instance_list : Constr.rel_context -> instance_list -> substl

(** Take an index in an instance of a context and returns its index wrt to
    the full context (e.g. 2 in [x:A;y:=b;z:C] is 3, i.e. a reference to z) *)
val adjust_rel_to_rel_context : ('a, 'b, 'r) Context.Rel.pt -> int -> int

(** [substnl [a₁;...;an] k c] substitutes in parallel [a₁],...,[an]
    for respectively [Rel(k+1)],...,[Rel(k+n)] in [c]; it relocates
    accordingly indexes in [an],...,[a1] and [c]. In terms of typing, if
    Γ ⊢ a{_n}..a₁ : Δ and Γ, Δ, Γ' ⊢ c : T with |Γ'|=k, then
    Γ, Γ' ⊢ [substnl [a₁;...;an] k c] : [substnl [a₁;...;an] k T]. *)
val substnl : substl -> int -> constr -> constr

(** [substl σ c] is a short-hand for [substnl σ 0 c] *)
val substl : substl -> constr -> constr

(** [substl a c] is a short-hand for [substnl [a] 0 c] *)
val subst1 : constr -> constr -> constr

(** [substnl_decl [a₁;...;an] k Ω] substitutes in parallel [a₁], ..., [an] for
    respectively [Rel(k+1)], ..., [Rel(k+n)] in a declaration [Ω]; it relocates
    accordingly indexes in [a₁],...,[an] and [c]. In terms of typing, if
    Γ ⊢ a{_n}..a₁ : Δ and Γ, Δ, Γ', Ω ⊢ with |Γ'|=[k], then
    Γ, Γ', [substnl_decl [a₁;...;an]] k Ω ⊢. *)
val substnl_decl : substl -> int -> Constr.rel_declaration -> Constr.rel_declaration

(** [substl_decl σ Ω] is a short-hand for [substnl_decl σ 0 Ω] *)
val substl_decl : substl -> Constr.rel_declaration -> Constr.rel_declaration

(** [subst1_decl a Ω] is a short-hand for [substnl_decl [a] 0 Ω] *)
val subst1_decl : constr -> Constr.rel_declaration -> Constr.rel_declaration

(** [substnl_rel_context [a₁;...;an] k Ω] substitutes in parallel [a₁], ..., [an]
    for respectively [Rel(k+1)], ..., [Rel(k+n)] in a context [Ω]; it relocates
    accordingly indexes in [a₁],...,[an] and [c]. In terms of typing, if
    Γ ⊢ a{_n}..a₁ : Δ and Γ, Δ, Γ', Ω ⊢ with |Γ'|=[k], then
    Γ, Γ', [substnl_rel_context [a₁;...;an]] k Ω ⊢. *)
val substnl_rel_context : substl -> int -> Constr.rel_context -> Constr.rel_context

(** [substl_rel_context σ Ω] is a short-hand for [substnl_rel_context σ 0 Ω] *)
val substl_rel_context : substl -> Constr.rel_context -> Constr.rel_context

(** [subst1_rel_context a Ω] is a short-hand for [substnl_rel_context [a] 0 Ω] *)
val subst1_rel_context : constr -> Constr.rel_context -> Constr.rel_context

(** [esubst lift σ c] substitutes [c] with arbitrary complex substitution [σ],
    using [lift] to lift subterms where necessary. *)
val esubst : (int -> 'a -> constr) -> 'a Esubst.subs -> constr -> constr

(** [replace_vars k [(id₁,c₁);...;(idn,cn)] t] substitutes [Var idj] by
    [cj] in [t]. *)
val replace_vars : (Id.t * constr) list -> constr -> constr

(** [substn_vars k [id₁;...;idn] t] substitutes [Var idj] by [Rel j+k-1] in [t].
   If two names are identical, the one of least index is kept. In terms of
   typing, if Γ,x{_n}:U{_n},...,x₁:U₁,Γ' ⊢ t:T, together with id{_j}:T{_j} and
   Γ,x{_n}:U{_n},...,x₁:U₁,Γ' ⊢ T{_j}\[id{_j+1}..id{_n}:=x{_j+1}..x{_n}\] ≡ Uj,
   then Γ\\{id₁,...,id{_n}\},x{_n}:U{_n},...,x₁:U₁,Γ' ⊢ [substn_vars
   (|Γ'|+1) [id₁;...;idn] t] : [substn_vars (|Γ'|+1) [id₁;...;idn]
   T]. *)
val substn_vars : int -> Id.t list -> constr -> constr

(** [subst_vars [id1;...;idn] t] is a short-hand for [substn_vars
   [id1;...;idn] 1 t]: it substitutes [Var idj] by [Rel j] in [t]. If
   two names are identical, the one of least index is kept. *)
val subst_vars : Id.t list -> constr -> constr

(** [subst_var id t] is a short-hand for [substn_vars [id] 1 t]: it
    substitutes [Var id] by [Rel 1] in [t]. *)
val subst_var : Id.t -> constr -> constr

(** Expand lets in context *)
val smash_rel_context : rel_context -> rel_context

(** {3 Substitution of universes} *)

open UVars

(** Level substitutions for polymorphism. *)

val subst_univs_level_constr : sort_level_subst -> constr -> constr
val subst_univs_level_context : sort_level_subst -> Constr.rel_context -> Constr.rel_context

(** Instance substitution for polymorphism. *)
val subst_instance_constr : Instance.t -> constr -> constr
val subst_instance_context : Instance.t -> Constr.rel_context -> Constr.rel_context

val univ_instantiate_constr : Instance.t -> constr univ_abstracted -> constr
(** Ignores the constraints carried by [univ_abstracted]. *)

val map_constr_relevance : (Sorts.relevance -> Sorts.relevance) -> Constr.t -> Constr.t
(** Modifies the relevances in the head node (not in subterms) *)

val sort_and_universes_of_constr : ?init:Sorts.QVar.Set.t * Univ.Level.Set.t -> constr -> Sorts.QVar.Set.t * Univ.Level.Set.t

val universes_of_constr : ?init:Univ.Level.Set.t -> constr -> Univ.Level.Set.t

type ('a,'s,'u,'r) univ_visitor = {
  visit_sort : 'a -> 's -> 'a;
  visit_instance : 'a -> 'u -> 'a;
  visit_relevance : 'a -> 'r -> 'a;
}

val visit_kind_univs : ('acc, 'sort, 'instance, 'relevance) univ_visitor ->
  'acc ->
  (_, _, 'sort, 'instance, 'relevance) Constr.kind_of_term ->
  'acc

(** {3 Low-level cached lift type} *)

type substituend
val make_substituend : constr -> substituend
val lift_substituend : int -> substituend -> constr
