(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Explicit substitutions *)

(** {6 Explicit substitutions } *)
(** Explicit substitutions for some type of terms ['a].

    Assuming terms enjoy a notion of typability Γ ⊢ t : A, where Γ is a
    telescope and A a type, substitutions can be typed as Γ ⊢ σ : Δ, where
    as a first approximation σ is a list of terms u₁; ...; uₙ s.t.
    Δ := (x₁ : A₁), ..., (xₙ : Aₙ) and Γ ⊢ uᵢ : Aᵢ{u₁...uᵢ₋₁} for all 1 ≤ i ≤ n.

    Substitutions can be applied to terms as follows, and furthermore
    if Γ ⊢ σ : Δ and Δ ⊢ t : A, then Γ ⊢ t{σ} : A{σ}.

    We make the typing rules explicit below, but we omit the explicit De Bruijn
    fidgetting and leave relocations implicit in terms and types.

*)
type 'a subs

(** Derived constructors granting basic invariants *)

(** Assuming |Γ| = n, Γ ⊢ subs_id n : Γ *)
val subs_id : int -> 'a subs

(** Assuming Γ ⊢ σ : Δ and Γ ⊢ t : A{σ}, then Γ ⊢ subs_cons t σ : Δ, A *)
val subs_cons: 'a -> 'a subs -> 'a subs

(** Assuming Γ ⊢ σ : Δ and |Ξ| = n, then Γ, Ξ ⊢ subs_shft (n, σ) : Δ *)
val subs_shft: int * 'a subs -> 'a subs

(** Unary variant of {!subst_liftn}. *)
val subs_lift: 'a subs -> 'a subs

(** Assuming Γ ⊢ σ : Δ and |Ξ| = n, then Γ, Ξ ⊢ subs_liftn n σ : Δ, Ξ *)
val subs_liftn: int -> 'a subs -> 'a subs

(** [expand_rel k subs] expands de Bruijn [k] in the explicit substitution
    [subs]. The result is either (Inl(lams,v)) when the variable is
    substituted by value [v] under [lams] binders (i.e. v *has* to be
    shifted by [lams]), or (Inr (k',p)) when the variable k is just relocated
    as k'; p is None if the variable points inside subs and Some(k) if the
    variable points k bindings beyond subs (cf argument of ESID).
*)
val expand_rel: int -> 'a subs -> (int * 'a, int * int option) Util.union

(** Tests whether a substitution behaves like the identity *)
val is_subs_id: 'a subs -> bool

(** Composition of substitutions: [comp mk_clos s1 s2] computes a
    substitution equivalent to applying s2 then s1. Argument
    mk_clos is used when a closure has to be created, i.e. when
    s1 is applied on an element of s2.
*)

(** {6 Compact representation } *)
(** Compact representation of explicit relocations
    - [ELSHFT(l,n)] == lift of [n], then apply [lift l].
    - [ELLFT(n,l)] == apply [l] to de Bruijn > [n] i.e under n binders.

    Invariant ensured by the private flag: no lift contains two consecutive
    [ELSHFT] nor two consecutive [ELLFT].

    Relocations are a particular kind of substitutions that only contain
    variables. In particular, [el_*] enjoys the same typing rules as the
    equivalent substitution function [subs_*].
*)
type lift = private
  | ELID
  | ELSHFT of lift * int
  | ELLFT of int * lift

(** For arbitrary Γ: Γ ⊢ el_id : Γ *)
val el_id : lift

(** Assuming Γ ⊢ σ : Δ and |Ξ| = n, then Γ, Ξ ⊢ el_shft (n, σ) : Δ *)
val el_shft : int -> lift -> lift

(** Assuming Γ ⊢ σ : Δ and |Ξ| = n, then Γ, Ξ ⊢ el_liftn n σ : Δ, Ξ *)
val el_liftn : int -> lift -> lift

(** Unary variant of {!subst_liftn}. *)
val el_lift : lift -> lift

(** Assuming Γ₁, A, Γ₂ ⊢ σ : Δ₁, A, Δ₂ and Δ₁, A, Δ₂ ⊢ n : A,
    then Γ₁, A, Γ₂ ⊢ reloc_rel n σ : A *)
val reloc_rel : int -> lift -> int

val is_lift_id : lift -> bool

(** Lift applied to substitution: [lift_subst mk_clos el s] computes a
    substitution equivalent to applying el then s. Argument
    mk_clos is used when a closure has to be created, i.e. when
    el is applied on an element of s.

    That is, if Γ ⊢ e : Δ and Δ ⊢ σ : Ξ, then Γ ⊢ lift_subst mk e σ : Ξ.
*)
val lift_subst : (lift -> 'a -> 'b) -> lift -> 'a subs -> 'b subs

(** Debugging utilities *)
module Internal :
sig
type 'a or_rel = REL of int | VAL of int * 'a

(** High-level representation of a substitution. The first component is a list
    that associates a value to an index, and the second component is the
    relocation shift that must be applied to any variable pointing outside of
    the substitution. *)
val repr : 'a subs -> 'a or_rel list * int
end
