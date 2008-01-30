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

(** We first define setoids on a carrier, it amounts to an equivalence relation. 
   Now [equiv] is overloaded for every [Setoid].
*)

Require Export Coq.Relations.Relations.

Class Setoid (carrier : Type) (equiv : relation carrier) :=
  equiv_prf : equivalence carrier equiv.

(** Overloaded notations for setoid equivalence and inequivalence. Not to be confused with [eq] and [=]. *)

Definition equiv [ Setoid A R ] : _ := R.

(** Subset objects should be first coerced to their underlying type, but that notation doesn't work in the standard case then. *)

(* Notation " x == y " := (equiv (x :>) (y :>)) (at level 70, no associativity) : type_scope. *)
Notation " x == y " := (equiv x y) (at level 70, no associativity) : type_scope.

Notation " x =/= y " := (~ x == y) (at level 70, no associativity) : type_scope.

Definition equiv_refl [ s : Setoid A R ] : forall x : A, R x x := equiv_refl _ _ equiv_prf.
Definition equiv_sym [ s : Setoid A R ] : forall x y : A, R x y -> R y x := equiv_sym _ _ equiv_prf.
Definition equiv_trans [ s : Setoid A R ] : forall x y z : A, R x y -> R y z -> R x z := equiv_trans _ _ equiv_prf.

Lemma nequiv_sym : forall [ s : Setoid A R ] (x y : A), x =/= y -> y =/= x.
Proof.
  intros ; red ; intros.
  apply equiv_sym in H0...
  apply (H H0).
Qed.

(** Tactics to do some progress on the goal, called by the user. *)

Ltac do_setoid_refl :=
  match goal with
    | [ |- @equiv ?A ?R ?s ?X _ ] => apply (equiv_refl (A:=A) (R:=R) (s:=s) X)
    | [ |- ?R ?X _ ] => apply (equiv_refl (R:=R) X)
    | [ |- ?R ?A ?X _ ] => apply (equiv_refl (R:=R A) X)
    | [ |- ?R ?A ?B ?X _ ] => apply (equiv_refl (R:=R A B) X)
    | [ |- ?R ?A ?B ?C ?X _ ] => apply (equiv_refl (R:=R A B C) X)
  end.

Ltac refl := do_setoid_refl.

Ltac do_setoid_sym := 
  match goal with
    | [ |- @equiv ?A ?R ?s ?X ?Y ] => apply (equiv_sym (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y))
    | [ |- not (@equiv ?A ?R ?s ?X ?Y) ] => apply (nequiv_sym (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y))
    | [ |- ?R ?X ?Y ] => apply (equiv_sym (R:=R) (x:=Y) (y:=X))
    | [ |- ?R ?A ?X ?Y ] => apply (equiv_sym (R:=R A) (x:=Y) (y:=X))
    | [ |- ?R ?A ?B ?X ?Y ] => apply (equiv_sym (R:=R A B) (x:=Y) (y:=X))
    | [ |- ?R ?A ?B ?C ?X ?Y ] => apply (equiv_sym (R:=R A B C) (x:=Y) (y:=X))
  end.

Ltac sym := do_setoid_sym.

Ltac do_setoid_trans Y := 
  match goal with
    | [ |- @equiv ?A ?R ?s ?X ?Z ] => apply (equiv_trans (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?X ?Z ] => apply (equiv_trans (R:=R) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?X ?Z ] => apply (equiv_trans (R:=R A) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?B ?X ?Z ] => apply (equiv_trans (R:=R A B) (x:=X) (y:=Y) (z:=Z))
    | [ |- ?R ?A ?B ?C ?X ?Z ] => apply (equiv_trans (R:=R A B C) (x:=X) (y:=Y) (z:=Z))
  end.

Ltac trans y := do_setoid_trans y.

(** Use the [clsubstitute] command which substitutes an equality in every hypothesis. *)

Ltac clsubst H := 
  match type of H with
    ?x == ?y => clsubstitute H ; clear H x
  end.

Ltac clsubst_nofail :=
  match goal with
    | [ H : ?x == ?y |- _ ] => clsubst H ; clsubst_nofail
    | _ => idtac
  end.
  
(** [subst*] will try its best at substituting every equality in the goal. *)

Tactic Notation "clsubst" "*" := clsubst_nofail.

(** Tactics to immediately solve the goal without user help. *)

Ltac setoid_refl :=
  match goal with
    | [ |- @equiv ?A ?R ?s ?X _ ] => apply (equiv_refl (A:=A) (R:=R) (s:=s) X)
    | [ H : ?X =/= ?X |- _ ] => elim H ; setoid_refl
  end.

Ltac setoid_sym := 
  match goal with
    | [ H : ?X == ?Y |- ?Y == ?X ] => apply (equiv_sym (x:=X) (y:=Y) H)
    | [ H : ?X =/= ?Y |- ?Y =/= ?X ] => apply (nequiv_sym (x:=X) (y:=Y) H)
  end.

Ltac setoid_trans := 
  match goal with
    | [ H : ?X == ?Y, H' : ?Y == ?Z |- @equiv ?A ?R ?s ?X ?Z ] => apply (equiv_trans (A:=A) (R:=R) (s:=s) (x:=X) (y:=Y) (z:=Z) H H')
  end.

(** To immediatly solve a goal on setoid equality. *)

Ltac setoid_tac := setoid_refl || setoid_sym || setoid_trans.

Lemma nequiv_equiv : forall [ Setoid A ] (x y z : A), x =/= y -> y == z -> x =/= z.
Proof.
  intros; intro. 
  assert(z == y) by setoid_sym.
  assert(x == y) by setoid_trans.
  contradiction.
Qed.

Lemma equiv_nequiv : forall [ Setoid A ] (x y z : A), x == y -> y =/= z -> x =/= z.
Proof.
  intros; intro. 
  assert(y == x) by setoid_sym.
  assert(y == z) by setoid_trans.
  contradiction.
Qed.

Open Scope type_scope.

(** Need to fix fresh to not fail if some arguments are not identifiers. *)
(* Ltac setoid_sat ::= *)
(*   match goal with *)
(*     | [ H : ?x == ?y |- _ ] => let name:=fresh "Heq" y x in add_hypothesis name (equiv_sym H) *)
(*     | [ H : ?x =/= ?y |- _ ] => let name:=fresh "Hneq" y x in add_hypothesis name (nequiv_sym H) *)
(*     | [ H : ?x == ?y, H' : ?y == ?z |- _ ] => let name:=fresh "Heq" x z in add_hypothesis name (equiv_trans H H') *)
(*     | [ H : ?x == ?y, H' : ?y =/= ?z |- _ ] => let name:=fresh "Hneq" x z in add_hypothesis name (equiv_nequiv H H') *)
(*     | [ H : ?x =/= ?y, H' : ?y == ?z |- _ ] => let name:=fresh "Hneq" x z in add_hypothesis name (nequiv_equiv H H') *)
(*   end. *)

Ltac setoid_sat :=
  match goal with
    | [ H : ?x == ?y |- _ ] => let name:=fresh "Heq" in add_hypothesis name (equiv_sym H)
    | [ H : ?x =/= ?y |- _ ] => let name:=fresh "Hneq" in add_hypothesis name (nequiv_sym H)
    | [ H : ?x == ?y, H' : ?y == ?z |- _ ] => let name:=fresh "Heq" in add_hypothesis name (equiv_trans H H')
    | [ H : ?x == ?y, H' : ?y =/= ?z |- _ ] => let name:=fresh "Hneq" in add_hypothesis name (equiv_nequiv H H')
    | [ H : ?x =/= ?y, H' : ?y == ?z |- _ ] => let name:=fresh "Hneq" in add_hypothesis name (nequiv_equiv H H')
  end.

Ltac setoid_simplify_one :=
  match goal with
    | [ H : ?x == ?x |- _ ] => clear H
    | [ H : ?x == ?y |- _ ] => clsubst H
    | [ |- ?x =/= ?y ] => let name:=fresh "Hneq" in intro name
  end.

Ltac setoid_simplify := repeat setoid_simplify_one.

Ltac setoid_saturate := repeat setoid_sat.

Ltac setoidify_tac :=
  match goal with
    | [ s : Setoid ?A ?R, H : ?R ?x ?y |- _ ] => change R with (@equiv A R s) in H
    | [ s : Setoid ?A ?R |- context C [ ?R ?x ?y ] ] => change (R x y) with (@equiv A R s x y)
  end.

Ltac setoidify := repeat setoidify_tac.

Definition respectful [ sa : Setoid a eqa, sb : Setoid b eqb ] 
  (m : a -> b) : Prop :=
  forall x y, eqa x y -> eqb (m x) (m y).

Class [ sa : Setoid a eqa, sb : Setoid b eqb ] => 
  Morphism (m : a -> b) :=
  respect : respectful m.

(** Here we build a setoid instance for functions which relates respectful ones only. *)

Definition respecting [ Setoid a R, Setoid b R' ] : Type := 
  { morph : a -> b | respectful morph }.

Ltac obligations_tactic ::= try red ; program_simpl ; try tauto.

Program Instance [ sa : Setoid a R, sb : Setoid b R' ] => 
  arrow_setoid : 
  Setoid ({ morph : a -> b | respectful morph })

  (fun (f g : respecting) => forall (x y : a), R x y -> R' (`f x) (`g y)) :=
  equiv_prf := Build_equivalence _ _ _ _ _.

  Next Obligation.
  Proof.
    trans (y x0) ; eauto.
    apply H.
    refl.
  Qed.

  Next Obligation.
  Proof.
    sym ; apply H.
    sym ; auto.
  Qed.

(** We redefine respect for binary and ternary morphims because we cannot get a satisfying instance of [Setoid (a -> b)] from 
   some arbitrary domain and codomain setoids. We can define it on respectful Coq functions though, see [arrow_setoid] above. *)

Definition binary_respectful [ sa : Setoid a eqa, sb : Setoid b eqb, Setoid c eqc ] (m : a -> b -> c) : Prop :=
  forall x y, eqa x y -> 
    forall z w, eqb z w -> eqc (m x z) (m y w).

Class [ sa : Setoid a eqa, sb : Setoid b eqb, sc : Setoid c eqc ] => BinaryMorphism (m : a -> b -> c) :=
  respect2 : binary_respectful m.

Definition ternary_respectful [ sa : Setoid a eqa, sb : Setoid b eqb, sc : Setoid c eqc, Setoid d eqd ] (m : a -> b -> c -> d) : Prop :=
  forall x y, eqa x y -> forall z w, eqb z w -> forall u v, eqc u v -> eqd (m x z u) (m y w v).

Class [ sa : Setoid a eqa, sb : Setoid b eqb, sc : Setoid c eqc, sd : Setoid d eqd ] => TernaryMorphism (m : a -> b -> c -> d) :=
  respect3 : ternary_respectful m.

(** Definition of the usual morphisms in [Prop]. *)

Program Instance iff_setoid : Setoid Prop iff :=
  equiv_prf := @Build_equivalence _ _ iff_refl iff_trans iff_sym.

Program Instance not_morphism : Morphism Prop iff Prop iff not.

Program Instance and_morphism : ? BinaryMorphism iff_setoid iff_setoid iff_setoid and.

(* We make the setoids implicit, they're always [iff] *)

Implicit Arguments Enriching BinaryMorphism [[!sa] [!sb] [!sc]].

Program Instance or_morphism : ? BinaryMorphism or.

Definition impl (A B : Prop) := A -> B.

Program Instance impl_morphism : ? BinaryMorphism impl.

Next Obligation.
Proof.
  unfold impl. tauto.
Qed.

(** Every setoid relation gives rise to a morphism, in fact every partial setoid does. *)

Program Instance [ Setoid a R ] => setoid_morphism : ? BinaryMorphism R.

Next Obligation.
Proof with auto.
  split ; intros.
  trans x. sym... trans z...
  trans y... trans w... sym...
Qed.
  
Definition iff_morphism : BinaryMorphism iff := setoid_morphism.

Existing Instance iff_morphism.

Implicit Arguments eq [[A]].

Program Instance eq_setoid : Setoid A eq :=
  equiv_prf := Build_equivalence _ _ _ _ _.

Program Instance eq_morphism : BinaryMorphism A eq A eq Prop iff eq.

Program Instance arrow_morphism : BinaryMorphism A eq B eq C eq m.

Implicit Arguments arrow_morphism [[A] [B] [C]].

Program Instance type_setoid : Setoid Type (fun x y => x = y) :=
  equiv_prf := Build_equivalence _ _ _ _ _.

Lemma setoid_subst : forall (x y : Type), x == y -> x -> y.
Proof.
  intros.
  rewrite <- H.
  apply X.
Qed.

Lemma prop_setoid_subst : forall (x y : Prop), x == y -> x -> y.
Proof.
  intros.
  clrewrite <- H.
  apply H0.
Qed.

Program Instance [ sa : Setoid a eqa, sb : Setoid b eqb, sc : Setoid c eqc,
  mg : ? Morphism sb sc g, mf : ? Morphism sa sb f ] => 
  compose_morphism : ? Morphism sa sc (fun x => g (f x)).

Next Obligation.
Proof.
  apply (respect (m0:=mg)).
  apply (respect (m0:=mf)).
  assumption.
Qed.

(** Partial setoids don't require reflexivity so we can build a partial setoid on the function space. *)

Class PartialSetoid (carrier : Type) (equiv : relation carrier) :=
  pequiv_prf : PER carrier equiv.

(** Overloaded notation for partial setoid equivalence. *)

Definition pequiv [ PartialSetoid A R ] : _ := R.

Infix "=~=" := pequiv (at level 70, no associativity) : type_scope.

Definition pequiv_sym [ s : PartialSetoid A R ] : forall x y : A, R x y -> R y x := per_sym _ _ pequiv_prf.
Definition pequiv_trans [ s : PartialSetoid A R ] : forall x y z : A, R x y -> R y z -> R x z := per_trans _ _ pequiv_prf.

Program Instance [ sa : Setoid a R, sb : Setoid b R' ] => arrow_partial_setoid : 
  PartialSetoid (a -> b)
  (fun f g => forall (x y : a), R x y -> R' (f x) (g y)) :=
  pequiv_prf := Build_PER _ _ _ _.

Next Obligation.
Proof.
  sym.
  apply H.
  sym ; assumption.
Qed.

Next Obligation.
Proof.
  trans (y x0).
  apply H ; auto.
  trans y0 ; auto.
  sym ; auto.
  apply H0 ; auto.
Qed.

(** The following is not definable. *)
(*
Program Instance [ sa : Setoid a R, sb : Setoid b R' ] => arrow_setoid : 
  Setoid (a -> b)
  (fun f g => forall (x y : a), R x y -> R' (f x) (g y)) :=
  equiv_prf := Build_equivalence _ _ _ _ _.
*)

(** Reset the default Program tactic. *)

Ltac obligations_tactic ::= program_simpl.
