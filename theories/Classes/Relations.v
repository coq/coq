(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based setoids, tactics and standard instances.
   TODO: explain clrewrite, clsubstitute and so on.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Import Coq.Program.Program.
Require Import Coq.Classes.Init.

Set Implicit Arguments.
Unset Strict Implicit.

Definition relationT A := A -> A -> Type.
Definition relation A := A -> A -> Prop.

Definition inverse A (R : relation A) : relation A := flip R.

Lemma inverse_inverse : forall A (R : relation A), inverse (inverse R) = R.
Proof. intros ; unfold inverse. apply (flip_flip R). Qed.

Definition complementT A (R : relationT A) := fun x y => ! R x y.

Definition complement A (R : relation A) := fun x y => ~ R x y.

(** These are convertible. *)

Lemma complementT_flip : forall A (R : relationT A), complementT (flip R) = flip (complementT R).
Proof. reflexivity. Qed.

Lemma complement_inverse : forall A (R : relation A), complement (inverse R) = inverse (complement R).
Proof. reflexivity. Qed.

(** We rebind relations in separate classes to be able to overload each proof. *)

Class Reflexive A (R : relationT A) :=
  reflexive : forall x, R x x.

Class Irreflexive A (R : relationT A) := 
  irreflexive : forall x, R x x -> False.

Class Symmetric A (R : relationT A) := 
  symmetric : forall x y, R x y -> R y x.

Class Asymmetric A (R : relationT A) := 
  asymmetric : forall x y, R x y -> R y x -> False.

Class Transitive A (R : relationT A) := 
  transitive : forall x y z, R x y -> R y z -> R x z.

Implicit Arguments Reflexive [A].
Implicit Arguments Irreflexive [A].
Implicit Arguments Symmetric [A].
Implicit Arguments Asymmetric [A].
Implicit Arguments Transitive [A].

Hint Resolve @irreflexive : ord.

(** We can already dualize all these properties. *)

Program Instance [ Reflexive A R ] => flip_reflexive : Reflexive A (flip R) :=
  reflexive := reflexive (R:=R).

Program Instance [ Irreflexive A R ] => flip_irreflexive : Irreflexive A (flip R) :=
  irreflexive := irreflexive (R:=R).

Program Instance [ Symmetric A R ] => flip_symmetric : Symmetric A (flip R).

  Solve Obligations using unfold flip ; program_simpl ; eapply symmetric ; eauto.

Program Instance [ Asymmetric A R ] => flip_asymmetric : Asymmetric A (flip R).
  
  Solve Obligations using program_simpl ; unfold flip in * ; intros ; eapply asymmetric ; eauto.

Program Instance [ Transitive A R ] => flip_transitive : Transitive A (flip R).

  Solve Obligations using unfold flip ; program_simpl ; eapply transitive ; eauto.

(** Have to do it again for Prop. *)

Program Instance [ Reflexive A (R : relation A) ] => inverse_reflexive : Reflexive A (inverse R) :=
  reflexive := reflexive (R:=R).

Program Instance [ Irreflexive A (R : relation A) ] => inverse_irreflexive : Irreflexive A (inverse R) :=
  irreflexive := irreflexive (R:=R).

Program Instance [ Symmetric A (R : relation A) ] => inverse_symmetric : Symmetric A (inverse R).

  Solve Obligations using unfold inverse, flip ; program_simpl ; eapply symmetric ; eauto.

Program Instance [ Asymmetric A (R : relation A) ] => inverse_asymmetric : Asymmetric A (inverse R).
  
  Solve Obligations using program_simpl ; unfold inverse, flip in * ; intros ; eapply asymmetric ; eauto.

Program Instance [ Transitive A (R : relation A) ] => inverse_transitive : Transitive A (inverse R).

  Solve Obligations using unfold inverse, flip ; program_simpl ; eapply transitive ; eauto.

Program Instance [ Reflexive A (R : relation A) ] => 
  reflexive_complement_irreflexive : Irreflexive A (complement R).

  Next Obligation. 
  Proof. 
    unfold complement in * ; intros.
    apply H.
    apply reflexive.
  Qed.

Program Instance [ Irreflexive A (R : relation A) ] => 
  irreflexive_complement_reflexive : Reflexive A (complement R).

  Next Obligation. 
  Proof. 
    unfold complement in * ; intros.
    red ; intros.
    apply (irreflexive H).
  Qed.

Program Instance [ Symmetric A (R : relation A) ] => complement_symmetric : Symmetric A (complement R).

  Next Obligation.
  Proof.
    unfold complement in *.
    red ; intros H'.
    apply (H (symmetric H')).
  Qed.

(** Tactics to solve goals. Each tactic comes in two flavors:
   - a tactic to immediately solve a goal without user intervention
   - a tactic taking input from the user to make progress on a goal *)

Definition relate A (R : relationT A) : relationT A := R.

Ltac relationify_relation R R' :=
  match goal with
    | [ H : context [ R ?x ?y ] |- _ ] => change (R x y) with (R' x y) in H
    | [ |- context [ R ?x ?y ] ] => change (R x y) with (R' x y)
  end.

Ltac relationify R :=
  set (R' := relate R) ; progress (repeat (relationify_relation R R')).

Ltac relation_refl :=
  match goal with
    | [ |- ?R ?X ?X ] => apply (reflexive (R:=R) X)
    | [ H : ?R ?X ?X |- _ ] => apply (irreflexive (R:=R) H)

    | [ |- ?R ?A ?X ?X ] => apply (reflexive (R:=R A) X)
    | [ H : ?R ?A ?X ?X |- _ ] => apply (irreflexive (R:=R A) H)

    | [ |- ?R ?A ?B ?X ?X ] => apply (reflexive (R:=R A B) X)
    | [ H : ?R ?A ?B ?X ?X |- _ ] => apply (irreflexive (R:=R A B) H)

    | [ |- ?R ?A ?B ?C ?X ?X ] => apply (reflexive (R:=R A B C) X)
    | [ H : ?R ?A ?B ?C ?X ?X |- _ ] => apply (irreflexive (R:=R A B C) H)

    | [ |- ?R ?A ?B ?C ?D ?X ?X ] => apply (reflexive (R:=R A B C D) X)
    | [ H : ?R ?A ?B ?C ?D ?X ?X |- _ ] => apply (irreflexive (R:=R A B C D) H)
  end.

Ltac refl := relation_refl.

Ltac relation_sym := 
  match goal with
    | [ H : ?R ?X ?Y |- ?R ?Y ?X ] => apply (symmetric (R:=R) (x:=X) (y:=Y) H)

    | [ H : ?R ?A ?X ?Y |- ?R ?A ?Y ?X ] => apply (symmetric (R:=R A) (x:=X) (y:=Y) H)

    | [ H : ?R ?A ?B ?X ?Y |- ?R ?A ?B ?Y ?X ] => apply (symmetric (R:=R A B) (x:=X) (y:=Y) H)

    | [ H : ?R ?A ?B ?C ?X ?Y |- ?R ?A ?B ?C ?Y ?X ] => apply (symmetric (R:=R A B C) (x:=X) (y:=Y) H)

    | [ H : ?R ?A ?B ?C ?D ?X ?Y |- ?R ?A ?B ?C ?D ?Y ?X ] => apply (symmetric (R:=R A B C D) (x:=X) (y:=Y) H)

  end.

Ltac relation_symmetric := 
  match goal with
    | [ |- ?R ?Y ?X ] => apply (symmetric (R:=R) (x:=X) (y:=Y))

    | [ |- ?R ?A ?Y ?X ] => apply (symmetric (R:=R A) (x:=X) (y:=Y))

    | [ |- ?R ?A ?B ?Y ?X ] => apply (symmetric (R:=R A B) (x:=X) (y:=Y))

    | [ |- ?R ?A ?B ?C ?Y ?X ] => apply (symmetric (R:=R A B C) (x:=X) (y:=Y))

    | [ |- ?R ?A ?B ?C ?D ?Y ?X ] => apply (symmetric (R:=R A B C D) (x:=X) (y:=Y))
  end.

Ltac sym := relation_symmetric.

Ltac relation_trans := 
  match goal with
    | [ H : ?R ?X ?Y, H' : ?R ?Y ?Z |- ?R ?X ?Z ] => 
      apply (transitive (R:=R) (x:=X) (y:=Y) (z:=Z) H H')

    | [ H : ?R ?A ?X ?Y, H' : ?R ?A ?Y ?Z |- ?R ?A ?X ?Z ] => 
      apply (transitive (R:=R A) (x:=X) (y:=Y) (z:=Z) H H')

    | [ H : ?R ?A ?B ?X ?Y, H' : ?R ?A ?B ?Y ?Z |- ?R ?A ?B ?X ?Z ] => 
      apply (transitive (R:=R A B) (x:=X) (y:=Y) (z:=Z) H H')

    | [ H : ?R ?A ?B ?C ?X ?Y, H' : ?R ?A ?B ?C ?Y ?Z |- ?R ?A ?B ?C ?X ?Z ] => 
      apply (transitive (R:=R A B C) (x:=X) (y:=Y) (z:=Z) H H')

    | [ H : ?R ?A ?B ?C ?D ?X ?Y, H' : ?R ?A ?B ?C ?D ?Y ?Z |- ?R ?A ?B ?C ?D ?X ?Z ] => 
      apply (transitive (R:=R A B C D) (x:=X) (y:=Y) (z:=Z) H H')
  end.

Ltac relation_transitive Y := 
  match goal with
    | [ |- ?R ?X ?Z ] => 
      apply (transitive (R:=R) (x:=X) (y:=Y) (z:=Z))

    | [ |- ?R ?A ?X ?Z ] => 
      apply (transitive (R:=R A) (x:=X) (y:=Y) (z:=Z))

    | [ |- ?R ?A ?B ?X ?Z ] => 
      apply (transitive (R:=R A B) (x:=X) (y:=Y) (z:=Z))

    | [ |- ?R ?A ?B ?C ?X ?Z ] => 
      apply (transitive (R:=R A B C) (x:=X) (y:=Y) (z:=Z))

    | [ |- ?R ?A ?B ?C ?D ?X ?Z ] => 
      apply (transitive (R:=R A B C D) (x:=X) (y:=Y) (z:=Z))
  end.

Ltac trans Y := relation_transitive Y.

(** To immediatly solve a goal on setoid equality. *)

Ltac relation_tac := relation_refl || relation_sym || relation_trans.

(** * Morphisms.

   We now turn to the definition of [Morphism] and declare standard instances. 
   These will be used by the [clrewrite] tactic later. *)

(** Respectful morphisms. *)

Definition respectful_depT (A : Type) (R : relationT A) 
  (B : A -> Type) (R' : forall x y, B x -> B y -> Type) : relationT (forall x : A, B x) := 
  fun f g => forall x y : A, R x y -> R' x y (f x) (g y).

Definition respectfulT A (eqa : relationT A) B (eqb : relationT B) : relationT (A -> B) :=
  Eval compute in (respectful_depT eqa (fun _ _ => eqb)).

Definition respectful A (R : relation A) B (R' : relation B) : relation (A -> B) :=
  fun f g => forall x y : A, R x y -> R' (f x) (g y).

(** Notations reminiscent of the old syntax for declaring morphisms.
   We use three + or - for type morphisms, and two for [Prop] ones.
   *)

Notation " R +++> R' " := (@respectfulT _ R _ R') (right associativity, at level 20).
Notation " R ---> R' " := (@respectfulT _ (flip R) _ R') (right associativity, at level 20).

Notation " R ++> R' " := (@respectful _ R _ R') (right associativity, at level 20).
Notation " R --> R' " := (@respectful _ (inverse R) _ R') (right associativity, at level 20).

(** A morphism on a relation [R] is an object respecting the relation (in its kernel). 
   The relation [R] will be instantiated by [respectful] and [A] by an arrow type 
   for usual morphisms. *)

Class Morphism A (R : relationT A) (m : A) :=
  respect : R m m.

Ltac simpl_morphism :=
  try red ; unfold inverse, flip, impl, arrow ; program_simpl ; try tauto ; 
    try (red ; intros) ; try ( solve [ intuition ]).

Ltac obligations_tactic ::= simpl_morphism.

(** The arrow is a reflexive and transitive relation on types. *)

Program Instance arrow_refl : ? Reflexive arrow := 
  reflexive X := id.

Program Instance arrow_trans : ? Transitive arrow := 
  transitive X Y Z f g := g o f.

(** Can't use the definition [notT] as it gives a to universe inconsistency. *)

Program Instance notT_arrow_morphism : 
  Morphism (Type -> Type) (arrow ---> arrow) (fun X : Type => X -> False).

(** Isomorphism. *)

Definition iso (A B : Type) := 
  A -> B * B -> A.

Program Instance iso_refl : ? Reflexive iso.
Program Instance iso_sym : ? Symmetric iso.
Program Instance iso_trans : ? Transitive iso.

Program Instance not_iso_morphism : 
  Morphism (Type -> Type) (iso +++> iso) (fun X : Type => X -> False).

(** Logical implication. *)

Program Instance impl_refl : ? Reflexive impl.
Program Instance impl_trans : ? Transitive impl.

Program Instance not_impl_morphism :
  Morphism (Prop -> Prop) (impl --> impl) not.

(** Logical equivalence. *)

Program Instance iff_refl : ? Reflexive iff.
Program Instance iff_sym : ? Symmetric iff.
Program Instance iff_trans : ? Transitive iff.

Program Instance not_iff_morphism : 
  Morphism (Prop -> Prop) (iff ++> iff) not.

(** We make the type implicit, it can be infered from the relations. *)

Implicit Arguments Morphism [A].

(** If you have a morphism from [RA] to [RB] you have a contravariant morphism 
   from [RA] to [inverse RB]. *)

Program Instance `A` (RA : relation A) `B` (RB : relation B) [ ? Morphism (RA ++> RB) m ] =>
  morph_impl_co_contra_inverse :
  ? Morphism (RA --> inverse RB) m.

  Next Obligation.
  Proof.
    apply respect.
    apply H.
  Qed.

(** Every transitive relation gives rise to a binary morphism on [impl], 
   contravariant in the first argument, covariant in the second. *)

Program Instance [ Transitive A (R : relation A) ] => 
  trans_contra_co_morphism : ? Morphism (R --> R ++> impl) R.

  Next Obligation.
  Proof with auto.
    trans x...
    trans x0...
  Qed.

(** Dually... *)

Program Instance [ Transitive A (R : relation A) ] =>
  trans_co_contra_inv_impl_morphism : ? Morphism (R ++> R --> inverse impl) R.

  Obligations Tactic := idtac.
  
  Next Obligation.
  Proof with auto.
    intros.
    destruct (trans_contra_co_morphism (R:=inverse R)).
    revert respect0.
    unfold respectful, inverse, flip in * ; intros.
    apply respect0 ; auto.
  Qed.

Obligations Tactic := simpl_morphism.

(** With symmetric relations, variance is no issue ! *)

Program Instance [ Symmetric A (R : relation A) ] B (R' : relation B) 
  [ Morphism _ (R ++> R') m ] => 
  sym_contra_morphism : ? Morphism (R --> R') m.

  Next Obligation.
  Proof with auto.
    apply respect.
    sym...
  Qed.

(** Every symmetric and transitive relation gives rise to an equivariant morphism. *)

Program Instance [ Transitive A (R : relation A), Symmetric A R ] => 
  trans_sym_morphism : ? Morphism (R ++> R ++> iff) R.

  Next Obligation.
  Proof with auto.
    split ; intros.
    trans x0... trans x... sym...
  
    trans y... trans y0... sym...
  Qed.

(** The complement of a relation conserves its morphisms. *)

Program Instance `A` (RA : relation A) [ ? Morphism (RA ++> RA ++> iff) R ] => 
  complement_morphism : ? Morphism (RA ++> RA ++> iff) (complement R).

  Next Obligation.
  Proof.
    red ; unfold complement ; intros.
    pose (respect).
    pose (r x y H).
    pose (r0 x0 y0 H0).
    intuition.
  Qed.

(** The inverse too. *)

Program Instance `A` (RA : relation A) [ ? Morphism (RA ++> RA ++> iff) R ] => 
  inverse_morphism : ? Morphism (RA ++> RA ++> iff) (inverse R).

  Next Obligation.
  Proof.
    unfold inverse ; unfold flip.
    apply respect ; auto.
  Qed.

Program Instance [ Transitive A (R : relation A), Symmetric A R ] =>
  trans_sym_contra_co_inv_impl_morphism : ? Morphism (R --> R ++> inverse impl) R.

  Next Obligation.
  Proof with auto.
    trans y...
    sym...
    trans y0...
    sym...
  Qed.

(** Any binary morphism respecting some relations up to [iff] respects 
   them up to [impl] in each way. Very important instances as we need [impl]
   morphisms at the top level when we rewrite. *)

Program Instance `A` (R : relation A) `B` (R' : relation B) 
  [ ? Morphism (R ++> R' ++> iff) m ] => 
  iff_impl_binary_morphism : ? Morphism (R ++> R' ++> impl) m.

  Next Obligation.
  Proof.
    destruct respect with x y x0 y0 ; auto.
  Qed.

Program Instance `A` (R : relation A) `B` (R' : relation B)
  [ ? Morphism (R ++> R' ++> iff) m ] => 
  iff_inverse_impl_binary_morphism : ? Morphism (R ++> R' ++> inverse impl) m.

  Next Obligation.
  Proof.
    destruct respect with x y x0 y0 ; auto.
  Qed.

(** Standard instances for [iff] and [impl]. *)

(** Logical conjunction. *)

Program Instance and_impl_iff_morphism : ? Morphism (impl ++> iff ++> impl) and.

Program Instance and_iff_impl_morphism : ? Morphism (iff ++> impl ++> impl) and.

Program Instance and_iff_morphism : ? Morphism (iff ++> iff ++> iff) and.

(** Logical disjunction. *)

Program Instance or_impl_iff_morphism : ? Morphism (impl ++> iff ++> impl) or.

Program Instance or_iff_impl_morphism : ? Morphism (iff ++> impl ++> impl) or.

Program Instance or_iff_morphism : ? Morphism (iff ++> iff ++> iff) or.

(** Leibniz equality. *)

Program Instance eq_refl : ? Reflexive (@eq A).
Program Instance eq_sym : ? Symmetric (@eq A).
Program Instance eq_trans : ? Transitive (@eq A).

Program Definition eq_morphism A : Morphism (eq ++> eq ++> iff) (eq (A:=A)) :=
  trans_sym_morphism.

Program Instance `A B` (m : A -> B) => arrow_morphism : ? Morphism (eq ++> eq) m.

(** The [PER] typeclass. *)

Class PER (carrier : Type) (pequiv : relationT carrier) :=
  per_sym :> Symmetric pequiv ;
  per_trans :> Transitive pequiv.

(** We can build a PER on the coq function space if we have PERs on the domain and
   codomain. *)

Program Instance [ PER A (R : relation A), PER B (R' : relation B) ] => 
  arrow_per : PER (A -> B)
  (fun f g => forall (x y : A), R x y -> R' (f x) (g y)).

  Next Obligation.
  Proof with auto.
    constructor ; intros...
    assert(R x0 x0) by (trans y0 ; [ auto | sym ; auto ]).
    trans (y x0)...
  Qed.

(** The [Equivalence] typeclass. *)

Class Equivalence (carrier : Type) (equiv : relationT carrier) :=
  equiv_refl :> Reflexive equiv ;
  equiv_sym :> Symmetric equiv ;
  equiv_trans :> Transitive equiv.

(** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

Class [ Equivalence A eqA ] => Antisymmetric (R : relationT A) := 
  antisymmetric : forall x y, R x y -> R y x -> eqA x y.

Program Instance [ eq : Equivalence A eqA, ? Antisymmetric eq R ] => 
  flip_antisymmetric : ? Antisymmetric eq (flip R).

  Solve Obligations using unfold flip ; program_simpl ; eapply antisymmetric ; eauto.

(** Here we build an equivalence instance for functions which relates respectful ones only. *)

Definition respecting [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] : Type := 
  { morph : A -> B | respectful R R' morph morph }.

Ltac obligations_tactic ::= program_simpl.

Program Instance [ Equivalence A (R : relation A), Equivalence B (R' : relation B) ] => 
  respecting_equiv : Equivalence respecting
  (fun (f g : respecting) => forall (x y : A), R x y -> R' (`f x) (`g y)).

  Next Obligation.
  Proof.
    constructor ; intros.
    destruct x ; simpl.
    apply r ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    sym ; apply H.
    sym ; auto.
  Qed.

  Next Obligation.
  Proof.
    constructor ; intros.
    trans ((`y) y0).
    apply H ; auto.
    apply H0. refl.
  Qed.

(** Leibinz equality [eq] is an equivalence relation. *)

Program Instance eq_equivalence : Equivalence A eq.

(** Logical equivalence [iff] is an equivalence relation. *)

Program Instance iff_equivalence : Equivalence Prop iff.

(** The following is not definable. *)
(*
Program Instance [ sa : Equivalence a R, sb : Equivalence b R' ] => equiv_setoid : 
  Equivalence (a -> b)
  (fun f g => forall (x y : a), R x y -> R' (f x) (g y)).
*)
