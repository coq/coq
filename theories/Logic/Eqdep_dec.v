(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* Created by Bruno Barras, Jan 1998 *)
(* Made a module instance for EqdepFacts by Hugo Herbelin, Mar 2006 *)

(** We prove that there is only one proof of [x=x], i.e [eq_refl x].
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
(* Set Universe Polymorphism. *)

Section EqdepDec.

  Variable A : Type.

  Let comp (x y y':A) (eq1:x = y) (eq2:x = y') : y = y' :=
    eq_ind _ (fun a => a = y') eq2 _ eq1.

  Remark trans_sym_eq : forall (x y:A) (u:x = y), comp u u = eq_refl y.
  Proof.
    intros.
    case u; trivial.
  Qed.

  Variable x : A.

  Variable eq_dec : forall y:A, x = y \/ x <> y.

  Let nu (y:A) (u:x = y) : x = y :=
    match eq_dec y with
      | or_introl eqxy => eqxy
      | or_intror neqxy => False_ind _ (neqxy u)
    end.

  Let nu_constant : forall (y:A) (u v:x = y), nu u = nu v.
    intros.
    unfold nu.
    destruct (eq_dec y) as [Heq|Hneq].
    reflexivity.

    case Hneq; trivial.
  Qed.


  Let nu_inv (y:A) (v:x = y) : x = y := comp (nu (eq_refl x)) v.


  Remark nu_left_inv_on : forall (y:A) (u:x = y), nu_inv (nu u) = u.
  Proof.
    intros.
    case u; unfold nu_inv.
    apply trans_sym_eq.
  Qed.


  Theorem eq_proofs_unicity_on : forall (y:A) (p1 p2:x = y), p1 = p2.
  Proof.
    intros.
    elim nu_left_inv_on with (u := p1).
    elim nu_left_inv_on with (u := p2).
    elim nu_constant with y p1 p2.
    reflexivity.
  Qed.

  Theorem K_dec_on :
    forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
  Proof.
    intros.
    elim eq_proofs_unicity_on with x (eq_refl x) p.
    trivial.
  Qed.

  (** The corollary *)

  Let proj (P:A -> Prop) (exP:ex P) (def:P x) : P x :=
    match exP with
      | ex_intro _ x' prf =>
        match eq_dec x' with
          | or_introl eqprf => eq_ind x' P prf x (eq_sym eqprf)
          | _ => def
        end
    end.


  Theorem inj_right_pair_on :
    forall (P:A -> Prop) (y y':P x),
      ex_intro P x y = ex_intro P x y' -> y = y'.
  Proof.
    intros.
    cut (proj (ex_intro P x y) y = proj (ex_intro P x y') y).
    simpl.
    destruct (eq_dec x) as [Heq|Hneq].
    elim Heq using K_dec_on; trivial.

    intros.
    case Hneq; trivial.

    case H.
    reflexivity.
  Qed.

End EqdepDec.

(** Now we prove the versions that require decidable equality for the entire type
    rather than just on the given element.  The rest of the file uses this total
    decidable equality.  We could do everything using decidable equality at a point
    (because the induction rule for [eq] is really an induction rule for
    [{ y : A | x = y }]), but we don't currently, because changing everything
    would break backward compatibility and no-one has yet taken the time to define
    the pointed versions, and then re-define the non-pointed versions in terms of
    those. *)

Theorem eq_proofs_unicity A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall (y:A) (p1 p2:x = y), p1 = p2.
Proof (@eq_proofs_unicity_on A x (eq_dec x)).

Theorem K_dec A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall P:x = x -> Prop, P (eq_refl x) -> forall p:x = x, P p.
Proof (@K_dec_on A x (eq_dec x)).

Theorem inj_right_pair A (eq_dec : forall x y : A, x = y \/ x <> y) (x : A)
: forall (P:A -> Prop) (y y':P x),
    ex_intro P x y = ex_intro P x y' -> y = y'.
Proof (@inj_right_pair_on A x (eq_dec x)).

Require Import EqdepFacts.

(** We deduce axiom [K] for (decidable) types *)
Theorem K_dec_type :
  forall A:Type,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros A eq_dec x P H p.
  elim p using K_dec; intros.
  case (eq_dec x0 y); [left|right]; assumption.
  trivial.
Qed.

Theorem K_dec_set :
  forall A:Set,
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (x:A) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
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

Theorem UIP_dec :
  forall (A:Type),
    (forall x y:A, {x = y} + {x <> y}) ->
    forall (x y:A) (p1 p2:x = y), p1 = p2.
Proof (fun A eq_dec => eq_dep_eq__UIP A (eq_dep_eq_dec eq_dec)).

Unset Implicit Arguments.

(************************************************************************)
(** ** Definition of the functor that builds properties of dependent equalities on decidable sets in Type *)

(** The signature of decidable sets in [Type] *)

Module Type DecidableType.

  Monomorphic Parameter U:Type.
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

  Lemma UIP_refl : forall (x:U) (p:x = x), p = eq_refl x.
  Proof (UIP__UIP_refl U UIP).

  (** Streicher's axiom K *)

  Lemma Streicher_K :
    forall (x:U) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
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

  Parameter U:Set.
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
  Proof (eq_rect_eq__eq_dep_eq U eq_rect_eq).

  (** Uniqueness of Identity Proofs (UIP) *)

  Lemma UIP : forall (x y:U) (p1 p2:x = y), p1 = p2.
  Proof (eq_dep_eq__UIP U eq_dep_eq).

  (** Uniqueness of Reflexive Identity Proofs *)

  Lemma UIP_refl : forall (x:U) (p:x = x), p = eq_refl x.
  Proof (UIP__UIP_refl U UIP).

  (** Streicher's axiom K *)

  Lemma Streicher_K :
    forall (x:U) (P:x = x -> Prop), P (eq_refl x) -> forall p:x = x, P p.
  Proof (K_dec_type eq_dec).

  (** Proof-irrelevance on subsets of decidable sets *)

  Lemma inj_pairP2 :
    forall (P:U -> Prop) (x:U) (p q:P x),
      ex_intro P x p = ex_intro P x q -> p = q.
  Proof N.inj_pairP2.

  (** Injectivity of equality on dependent pairs in [Type] *)

  Lemma inj_pair2 :
    forall (P:U -> Type) (p:U) (x y:P p),
      existT P p x = existT P p y -> x = y.
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
  unfold Eq_rect_eq, Eq_rect_eq_on.
  intros; apply eq_rect_eq_dec.
  apply eq_dec.
Qed.

  (** Examples of short direct proofs of unicity of reflexivity proofs
      on specific domains *)

Lemma UIP_refl_unit (x : tt = tt) : x = eq_refl tt.
Proof.
  change (match tt as b return tt = b -> Prop with
          | tt => fun x => x = eq_refl tt
          end x).
  destruct x; reflexivity.
Defined.

Lemma UIP_refl_bool (b:bool) (x : b = b) : x = eq_refl.
Proof.
  destruct b.
  - change (match true as b return true=b -> Prop with
            | true => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
  - change (match false as b return false=b -> Prop with
            | false => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
Defined.

Lemma UIP_refl_nat (n:nat) (x : n = n) : x = eq_refl.
Proof.
  induction n.
  - change (match 0 as n return 0=n -> Prop with
            | 0 => fun x => x = eq_refl
            | _ => fun _ => True
            end x).
    destruct x; reflexivity.
  - specialize IHn with (f_equal pred x).
    change eq_refl with (f_equal S (@eq_refl _ n)).
    rewrite <- IHn; clear IHn.
    change (match S n as n' return S n = n' -> Prop with
            | 0 => fun _ => True
            | S n' => fun x =>
                x = f_equal S (f_equal pred x)
            end x).
  pattern (S n) at 2 3, x.
  destruct x; reflexivity.
Defined.
