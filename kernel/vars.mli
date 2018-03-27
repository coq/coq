(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
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

(** [exliftn el c] lifts [c] with lifting [el] *)
val exliftn : Esubst.lift -> constr -> constr

(** [liftn n k c] lifts by [n] indexes above or equal to [k] in [c] *)
val liftn : int -> int -> constr -> constr

(** [lift n c] lifts by [n] the positive indexes in [c] *)
val lift : int -> constr -> constr

(** The type [substl] is the type of substitutions [u₁..un] of type
    some context Δ and defined in some environment Γ. Typing of
    substitutions is defined by:
    - Γ ⊢ ∅ : ∅,
    - Γ ⊢ u₁..u{_n-1} : Δ and Γ ⊢ u{_n} : An\[u₁..u{_n-1}\] implies
      Γ ⊢ u₁..u{_n} : Δ,x{_n}:A{_n}
    - Γ ⊢ u₁..u{_n-1} : Δ and Γ ⊢ un : A{_n}\[u₁..u{_n-1}\] implies
      Γ ⊢ u₁..u{_n} : Δ,x{_n}:=c{_n}:A{_n} when Γ ⊢ u{_n} ≡ c{_n}\[u₁..u{_n-1}\]

    Note that [u₁..un] is represented as a list with [un] at the head of
    the list, i.e. as [[un;...;u₁]]. *)

type substl = constr list

(** Let [Γ] be a context interleaving declarations [x₁:T₁..xn:Tn]
   and definitions [y₁:=c₁..yp:=cp] in some context [Γ₀]. Let
   [u₁..un] be an {e instance} of [Γ], i.e. an instance in [Γ₀]
   of the [xi]. Then, [subst_of_rel_context_instance Γ u₁..un]
   returns the corresponding {e substitution} of [Γ], i.e. the
   appropriate interleaving [σ] of the [u₁..un] with the [c₁..cp],
   all of them in [Γ₀], so that a derivation [Γ₀, Γ, Γ₁|- t:T]
   can be instantiated into a derivation [Γ₀, Γ₁ |- t[σ]:T[σ]] using
   [substnl σ |Γ₁| t].
   Note that the instance [u₁..un] is represented starting with [u₁],
   as if usable in [applist] while the substitution is
   represented the other way round, i.e. ending with either [u₁] or
   [c₁], as if usable for [substl]. *)
val subst_of_rel_context_instance : Constr.rel_context -> constr list -> substl

(** For compatibility: returns the substitution reversed *)
val adjust_subst_to_rel_context : Constr.rel_context -> constr list -> constr list

(** Take an index in an instance of a context and returns its index wrt to
    the full context (e.g. 2 in [x:A;y:=b;z:C] is 3, i.e. a reference to z) *)
val adjust_rel_to_rel_context : ('a, 'b) Context.Rel.pt -> int -> int

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

(** [substnl_decl [a₁;...;an] k Ω] substitutes in parallel [a₁], ..., [an]
    for respectively [Rel(k+1)], ..., [Rel(k+n)] in [Ω]; it relocates
    accordingly indexes in [a₁],...,[an] and [c]. In terms of typing, if
    Γ ⊢ a{_n}..a₁ : Δ and Γ, Δ, Γ', Ω ⊢ with |Γ'|=[k], then
    Γ, Γ', [substnl_decl [a₁;...;an]] k Ω ⊢. *)
val substnl_decl : substl -> int -> Constr.rel_declaration -> Constr.rel_declaration

(** [substl_decl σ Ω] is a short-hand for [substnl_decl σ 0 Ω] *)
val substl_decl : substl -> Constr.rel_declaration -> Constr.rel_declaration

(** [subst1_decl a Ω] is a short-hand for [substnl_decl [a] 0 Ω] *)
val subst1_decl : constr -> Constr.rel_declaration -> Constr.rel_declaration

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

(** {3 Substitution of universes} *)

open Univ

(** Level substitutions for polymorphism. *)

val subst_univs_level_constr : universe_level_subst -> constr -> constr
val subst_univs_level_context : Univ.universe_level_subst -> Constr.rel_context -> Constr.rel_context

(** Instance substitution for polymorphism. *)
val subst_instance_constr : Instance.t -> constr -> constr
val subst_instance_context : Instance.t -> Constr.rel_context -> Constr.rel_context
