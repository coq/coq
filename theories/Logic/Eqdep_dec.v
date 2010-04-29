(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** We prove that there is only one proof of [x=x], i.e [refl_equal x].
    This holds if the equality upon the set of [x] is decidable.
    A corollary of this theorem is the equality of the right projections
    of two equal dependent pairs.

    Author:   Thomas Kleymann |<tms@dcs.ed.ac.uk>| in Lego
              adapted to Coq by B. Barras

    Credit:   Proofs up to [K_dec] follow an outline by Michael Hedberg

Table of contents:

1. Streicher's K and injectivity of dependent pair hold on decidable types

1.1. Definition of the functor that builds properties of dependent equalities
     from a proof of decidability of equality for a set in Type

1.2. Definition of the functor that builds properties of dependent equalities
     from a proof of decidability of equality for a set in Set

*)

(************************************************************************)
(** * Streicher's K and injectivity of dependent pair hold on decidable types *)

Set Implicit Arguments.

Section EqdepDec.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = refl_equal y.
  Proof.
    intros.
    case u; trivial.
  Qed.

  Variable eq_dec : forall x y:A, x = y \/ x <> y.

  Variable x : A.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec x y with
      | or_introl eqxy => eqxy
      | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu in |- *.
    case (eq_dec x y); intros.
    reflexivity.

    case n; trivial.
  Qed.


  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (refl_equal x)) v.


  Remark nu_left_inv : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv in |- *.
    apply trans_sym_eq.
  Qed.


  Theorem eq_proofs_unicity : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv with (u := p1).
    elim nu_left_inv with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Qed.

  Theorem K_dec :
    forall P:x = x -> Prop, P (refl_equal x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity with x (refl_equal x) p.
    trivial.
  Qed.

  (** The corollary *)

  Let proj (P:A -> Prop) (exP:ex P) (def:P x) : P x :=
    match exP with
      | ex_intro x' prf =>
        match eq_dec x' x with
          | or_introl eqprf => eq_ind x' P prf x eqprf
          | _ => def
        end
    end.


  Theorem inj_right_pair :
    forall (P:A -> Prop) (y y':P x),
      ex_intro P x y = ex_intro P x y' -> y = y'.
  Proof.
    intros.
    cut (proj (ex_intro P x y) y = proj (ex_intro P x y') y).
    simpl in |- *.
    case (eq_dec x x).
    intro e.
    elim e using K_dec; trivial.

    intros.
    case n; trivial.

    case H.
    reflexivity.
  Qed.

End EqdepDec.

Require Import EqdepFacts.

(** We deduce axiom [K] for (decidable) types *)
Theorem K_dec_type :
  forall A:Type,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (x:A) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof.
  intros A eq_dec x P H p.
  elim p using K_dec; intros.
  case (eq_dec x0 y); [left|right]; assumption.
  trivial.
Qed.

Theorem K_dec_set :
  forall A:Set,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (x:A) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
Proof fun A => K_dec_type (A:=A).

(** We deduce the [eq_rect_eq] axiom for (decidable) types *)
Theorem eq_rect_eq_dec :
  forall A:Type,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (p:A) (Q:A -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
Proof.
  intros A eq_dec.
  apply (Streicher_K__eq_rect_eq A (K_dec_type eq_dec)).
Qed.

(** We deduce the injectivity of dependent equality for decidable types *)
Theorem eq_dep_eq_dec :
  forall A:Type,
    (forall x y:A, {x = y} + {x <> y}) ->
     forall (P:A->Type) (p:A) (x y:P p), eq_dep A P p x p y -> x = y.
Proof (fun A eq_dec => eq_rect_eq__eq_dep_eq A (eq_rect_eq_dec eq_dec)).

Unset Implicit Arguments.

(************************************************************************)
(** ** Definition of the functor that builds properties of dependent equalities on decidable sets in Type *)

(** The signature of decidable sets in [Type] *)

Module Type DecidableType.

  Parameter U:Type.
  Axiom eq_dec : forall x y:U, {x = y} + {x <> y}.

End DecidableType.

(** The module [DecidableEqDep] collects equality properties for decidable
    set in [Type] *)

Module DecidableEqDep (M:DecidableType).

  Import M.

  (** Invariance by Substitution of Reflexive Equality Proofs *)

  Lemma eq_rect_eq :
    forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
  Proof eq_rect_eq_dec eq_dec.

  (** Injectivity of Dependent Equality *)

  Theorem eq_dep_eq :
    forall (P:U->Type) (p:U) (x y:P p), eq_dep U P p x p y -> x = y.
  Proof (eq_rect_eq__eq_dep_eq U eq_rect_eq).

  (** Uniqueness of Identity Proofs (UIP) *)

  Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
  Proof (eq_dep_eq__UIP U eq_dep_eq).

  (** Uniqueness of Reflexive Identity Proofs *)

  Lemma UIP_refl : forall (x:U) (p:x = x), p = refl_equal x.
  Proof (UIP__UIP_refl U UIP).

  (** Streicher's axiom K *)

  Lemma Streicher_K :
    forall (x:U) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
  Proof (K_dec_type eq_dec).

  (** Injectivity of equality on dependent pairs in [Type] *)

  Lemma inj_pairT2 :
    forall (P:U -> Type) (p:U) (x y:P p),
      existT P p x = existT P p y -> x = y.
  Proof eq_dep_eq__inj_pairT2 U eq_dep_eq.

  (** Proof-irrelevance on subsets of decidable sets *)

  Lemma inj_pairP2 :
    forall (P:U -> Prop) (x:U) (p q:P x),
      ex_intro P x p = ex_intro P x q -> p = q.
  Proof.
    intros.
    apply inj_right_pair with (A:=U).
    intros x0 y0; case (eq_dec x0 y0); [left|right]; assumption.
    assumption.
  Qed.

End DecidableEqDep.

(************************************************************************)
(** ** Definition of the functor that builds properties of dependent equalities on decidable sets in Set *)

(** The signature of decidable sets in [Set] *)

Module Type DecidableSet.

  Parameter U:Type.
  Axiom eq_dec : forall x y:U, {x = y} + {x <> y}.

End DecidableSet.

(** The module [DecidableEqDepSet] collects equality properties for decidable
    set in [Set] *)

Module DecidableEqDepSet (M:DecidableSet).

  Import M.
  Module N:=DecidableEqDep(M).

  (** Invariance by Substitution of Reflexive Equality Proofs *)

  Lemma eq_rect_eq :
    forall (p:U) (Q:U -> Type) (x:Q p) (h:p = p), x = eq_rect p Q x p h.
  Proof eq_rect_eq_dec eq_dec.

  (** Injectivity of Dependent Equality *)

  Theorem eq_dep_eq :
    forall (P:U->Type) (p:U) (x y:P p), eq_dep U P p x p y -> x = y.
  Proof N.eq_dep_eq.

  (** Uniqueness of Identity Proofs (UIP) *)

  Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
  Proof N.UIP.

  (** Uniqueness of Reflexive Identity Proofs *)

  Lemma UIP_refl : forall (x:U) (p:x = x), p = refl_equal x.
  Proof N.UIP_refl.

  (** Streicher's axiom K *)

  Lemma Streicher_K :
    forall (x:U) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.
  Proof N.Streicher_K.

  (** Proof-irrelevance on subsets of decidable sets *)

  Lemma inj_pairP2 :
    forall (P:U -> Prop) (x:U) (p q:P x),
      ex_intro P x p = ex_intro P x q -> p = q.
  Proof N.inj_pairP2.

  (** Injectivity of equality on dependent pairs in [Type] *)

  Lemma inj_pair2 :
    forall (P:U -> Type) (p:U) (x y:P p),
      existS P p x = existS P p y -> x = y.
  Proof eq_dep_eq__inj_pair2 U N.eq_dep_eq.

  (** Injectivity of equality on dependent pairs with second component
      in [Type] *)

  Notation inj_pairT2 := inj_pair2.

End DecidableEqDepSet.

  (** From decidability to inj_pair2 **)
Lemma inj_pair2_eq_dec : forall A:Type, (forall x y:A, {x=y}+{x<>y}) ->
   ( forall (P:A -> Type) (p:A) (x y:P p), existT P p x = existT P p y -> x = y ).
Proof.
  intros A eq_dec.
  apply eq_dep_eq__inj_pair2.
  apply eq_rect_eq__eq_dep_eq.
  unfold Eq_rect_eq.
  apply eq_rect_eq_dec.
  apply eq_dec.
Qed.
