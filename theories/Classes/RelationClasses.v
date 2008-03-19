(* -*- coq-prog-args: ("-emacs-U" "-top" "Coq.Classes.RelationClasses") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Typeclass-based relations, tactics and standard instances.
   This is the basic theory needed to formalize morphisms and setoids.
 
   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
   91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Require Export Coq.Classes.Init.
Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.
Require Export Coq.Relations.Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.

(** Default relation on a given support. *)

Class DefaultRelation A (R : relation A).

(** To search for the default relation, just call [default_relation]. *)

Definition default_relation [ DefaultRelation A R ] : relation A := R.

(** A notation for applying the default relation to [x] and [y]. *)

Notation " x ===def y " := (default_relation x y) (at level 70, no associativity).

Definition inverse {A} : relation A -> relation A := flip.

Definition complement {A} (R : relation A) : relation A := fun x y => R x y -> False.

Definition pointwise_relation {A B : Type} (R : relation B) : relation (A -> B) := 
  fun f g => forall x : A, R (f x) (g x).

(** These are convertible. *)

Lemma complement_inverse : forall A (R : relation A), complement (inverse R) = inverse (complement R).
Proof. reflexivity. Qed.

(** We rebind relations in separate classes to be able to overload each proof. *)

Class reflexive A (R : relation A) :=
  reflexivity : forall x, R x x.

Class irreflexive A (R : relation A) := 
  irreflexivity : forall x, R x x -> False.

Class symmetric A (R : relation A) := 
  symmetry : forall x y, R x y -> R y x.

Class asymmetric A (R : relation A) := 
  asymmetry : forall x y, R x y -> R y x -> False.

Class transitive A (R : relation A) := 
  transitivity : forall x y z, R x y -> R y z -> R x z.

Implicit Arguments reflexive [A].
Implicit Arguments irreflexive [A].
Implicit Arguments symmetric [A].
Implicit Arguments asymmetric [A].
Implicit Arguments transitive [A].

Hint Resolve @irreflexivity : ord.

(** We can already dualize all these properties. *)

Program Instance [ ! reflexive A R ] => flip_reflexive : reflexive (flip R) :=
  reflexivity := reflexivity (R:=R).

Program Instance [ ! irreflexive A R ] => flip_irreflexive : irreflexive (flip R) :=
  irreflexivity := irreflexivity (R:=R).

Program Instance [ ! symmetric A R ] => flip_symmetric : symmetric (flip R).

  Solve Obligations using unfold flip ; program_simpl ; clapply symmetric.

Program Instance [ ! asymmetric A R ] => flip_asymmetric : asymmetric (flip R).
  
  Solve Obligations using program_simpl ; unfold flip in * ; intros ; clapply asymmetry.

Program Instance [ ! transitive A R ] => flip_transitive : transitive (flip R).

  Solve Obligations using unfold flip ; program_simpl ; clapply transitivity.

(** Have to do it again for Prop. *)

Program Instance [ ! reflexive A (R : relation A) ] => inverse_reflexive : reflexive (inverse R) :=
  reflexivity := reflexivity (R:=R).

Program Instance [ ! irreflexive A (R : relation A) ] => inverse_irreflexive : irreflexive (inverse R) :=
  irreflexivity := irreflexivity (R:=R).

Program Instance [ ! symmetric A (R : relation A) ] => inverse_symmetric : symmetric (inverse R).

  Solve Obligations using unfold inverse, flip ; program_simpl ; clapply symmetric.

Program Instance [ ! asymmetric A (R : relation A) ] => inverse_asymmetric : asymmetric (inverse R).
  
  Solve Obligations using program_simpl ; unfold inverse, flip in * ; intros ; clapply asymmetry.

Program Instance [ ! transitive A (R : relation A) ] => inverse_transitive : transitive (inverse R).

  Solve Obligations using unfold inverse, flip ; program_simpl ; clapply transitivity.

Program Instance [ ! reflexive A (R : relation A) ] => 
  reflexive_complement_irreflexive : irreflexive (complement R).

Program Instance [ ! irreflexive A (R : relation A) ] => 
  irreflexive_complement_reflexive : reflexive (complement R).

  Next Obligation. 
  Proof. 
    red. intros H.
    apply (irreflexivity H).
  Qed.

Program Instance [ ! symmetric A (R : relation A) ] => complement_symmetric : symmetric (complement R).

  Next Obligation.
  Proof.
    red ; intros H'.
    apply (H (symmetry H')).
  Qed.

(** * Standard instances. *)

Ltac reduce_goal :=
  match goal with
    | [ |- _ <-> _ ] => fail 1
    | _ => red ; intros ; try reduce_goal
  end.

Ltac reduce := reduce_goal.

Tactic Notation "apply" "*" constr(t) := 
  first [ refine t | refine (t _) | refine (t _ _) | refine (t _ _ _) | refine (t _ _ _ _) |
    refine (t _ _ _ _ _) | refine (t _ _ _ _ _ _) | refine (t _ _ _ _ _ _ _) ].

Ltac simpl_relation :=
  unfold inverse, flip, impl, arrow ; try reduce ; program_simpl ;
    try ( solve [ intuition ]).

Ltac obligations_tactic ::= simpl_relation.

(** Logical implication. *)

Program Instance impl_refl : reflexive impl.
Program Instance impl_trans : transitive impl.

(** Logical equivalence. *)

Program Instance iff_refl : reflexive iff.
Program Instance iff_sym : symmetric iff.
Program Instance iff_trans : transitive iff.

(** Leibniz equality. *)

Program Instance eq_refl : reflexive (@eq A).
Program Instance eq_sym : symmetric (@eq A).
Program Instance eq_trans : transitive (@eq A).

(** Various combinations of reflexivity, symmetry and transitivity. *)

(** A [PreOrder] is both reflexive and transitive. *)

Class PreOrder A (R : relation A) :=
  preorder_refl :> reflexive R ;
  preorder_trans :> transitive R.

(** A partial equivalence relation is symmetric and transitive. *)

Class PER (carrier : Type) (pequiv : relation carrier) :=
  per_sym :> symmetric pequiv ;
  per_trans :> transitive pequiv.

(** We can build a PER on the Coq function space if we have PERs on the domain and
   codomain. *)

Program Instance [ PER A (R : relation A), PER B (R' : relation B) ] => 
  arrow_per : PER (A -> B)
  (fun f g => forall (x y : A), R x y -> R' (f x) (g y)).

  Next Obligation.
  Proof with auto.
    assert(R x0 x0). 
    transitivity y0... symmetry...
    transitivity (y x0)...
  Qed.

(** The [Equivalence] typeclass. *)

Class Equivalence (carrier : Type) (equiv : relation carrier) :=
  equiv_refl :> reflexive equiv ;
  equiv_sym :> symmetric equiv ;
  equiv_trans :> transitive equiv.

(** We can now define antisymmetry w.r.t. an equivalence relation on the carrier. *)

Class [ Equivalence A eqA ] => antisymmetric (R : relation A) := 
  antisymmetry : forall x y, R x y -> R y x -> eqA x y.

Program Instance [ eq : Equivalence A eqA, antisymmetric eq R ] => 
  flip_antisymmetric : antisymmetric eq (flip R).

Program Instance [ eq : Equivalence A eqA, antisymmetric eq (R : relation A) ] => 
  inverse_antisymmetric : antisymmetric eq (inverse R).

(** Leibinz equality [eq] is an equivalence relation. *)

Program Instance eq_equivalence : Equivalence A (@eq A).

(** Logical equivalence [iff] is an equivalence relation. *)

Program Instance iff_equivalence : Equivalence Prop iff.

(** The following is not definable. *)
(*
Program Instance [ sa : Equivalence a R, sb : Equivalence b R' ] => equiv_setoid : 
  Equivalence (a -> b)
  (fun f g => forall (x y : a), R x y -> R' (f x) (g y)).
*)

Definition relation_equivalence {A : Type} : relation (relation A) :=
  fun (R R' : relation A) => forall x y, R x y <-> R' x y.

Infix "==rel" := relation_equivalence (at level 70).

Program Instance relation_equivalence_equivalence :
  Equivalence (relation A) relation_equivalence.

  Next Obligation.
  Proof.
    unfold relation_equivalence in *.
    apply transitivity with (y x0 y0) ; [ apply H | apply H0 ].
  Qed.
