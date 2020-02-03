(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

Require Import Notations.
Require Import Logic.

(********************************************************************)
(** * Datatypes with zero and one element *)

(** [Empty_set] is a datatype with no inhabitant *)

Inductive Empty_set : Set :=.

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.


(********************************************************************)
(** * The boolean datatype *)

(** [bool] is the datatype of the boolean values [true] and [false] *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

Add Printing If bool.

Declare Scope bool_scope.
Delimit Scope bool_scope with bool.
Bind Scope bool_scope with bool.

Register bool as core.bool.type.
Register true as core.bool.true.
Register false as core.bool.false.

(** Basic boolean operators *)

Definition andb (b1 b2:bool) : bool := if b1 then b2 else false.

Definition orb (b1 b2:bool) : bool := if b1 then true else b2.

Definition implb (b1 b2:bool) : bool := if b1 then b2 else true.

Definition xorb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => false
  end.

Definition negb (b:bool) := if b then false else true.

Infix "||" := orb : bool_scope.
Infix "&&" := andb : bool_scope.

Register andb as core.bool.andb.
Register orb as core.bool.orb.
Register xorb as core.bool.xorb.
Register negb as core.bool.negb.

(** Basic properties of [andb] *)

Lemma andb_prop : forall a b:bool, andb a b = true -> a = true /\ b = true.
Proof.
  destruct a, b; repeat split; assumption.
Qed.
Hint Resolve andb_prop: bool.

Register andb_prop as core.bool.andb_prop.

Lemma andb_true_intro :
  forall b1 b2:bool, b1 = true /\ b2 = true -> andb b1 b2 = true.
Proof.
  destruct b1; destruct b2; simpl; intros [? ?]; assumption.
Qed.
Hint Resolve andb_true_intro: bool.

Register andb_true_intro as core.bool.andb_true_intro.

(** Interpretation of booleans as propositions *)

Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.

Hint Constructors eq_true : eq_true.

Register eq_true as core.eq_true.type.

(** Another way of interpreting booleans as propositions *)

Definition is_true b := b = true.

(** [is_true] can be activated as a coercion by
   ([Local]) [Coercion is_true : bool >-> Sortclass].
*)

(** Additional rewriting lemmas about [eq_true] *)

Lemma eq_true_ind_r :
  forall (P : bool -> Prop) (b : bool), P b -> eq_true b -> P true.
Proof.
  intros P b H H0; destruct H0 in H; assumption.
Defined.

Lemma eq_true_rec_r :
  forall (P : bool -> Set) (b : bool), P b -> eq_true b -> P true.
Proof.
  intros P b H H0; destruct H0 in H; assumption.
Defined.

Lemma eq_true_rect_r :
  forall (P : bool -> Type) (b : bool), P b -> eq_true b -> P true.
Proof.
  intros P b H H0; destruct H0 in H; assumption.
Defined.

(** The [BoolSpec] inductive will be used to relate a [boolean] value
    and two propositions corresponding respectively to the [true]
    case and the [false] case.
    Interest: [BoolSpec] behave nicely with [case] and [destruct].
    See also [Bool.reflect] when [Q = ~P].
*)

Inductive BoolSpec (P Q : Prop) : bool -> Prop :=
  | BoolSpecT : P -> BoolSpec P Q true
  | BoolSpecF : Q -> BoolSpec P Q false.
Hint Constructors BoolSpec : core.


(********************************************************************)
(** * Peano natural numbers *)

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that the constructor name is the letter O.
    Numbers in [nat] can be denoted using a decimal notation;
    e.g. [3%nat] abbreviates [S (S (S O))] *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Declare Scope nat_scope.
Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments S _%nat.

Register nat as num.nat.type.
Register O as num.nat.O.
Register S as num.nat.S.

(********************************************************************)
(** * Container datatypes *)

(* Set Universe Polymorphism. *)

(** [option A] is the extension of [A] with an extra element [None] *)

#[universes(template)]
Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Arguments Some {A} a.
Arguments None {A}.

Register option as core.option.type.
Register Some as core.option.Some.
Register None as core.option.None.

Definition option_map (A B:Type) (f:A->B) (o : option A) : option B :=
  match o with
    | Some a => @Some B (f a)
    | None => @None B
  end.

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

#[universes(template)]
Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

Arguments inl {A B} _ , [A] B _.
Arguments inr {A B} _ , A [B] _.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

#[universes(template)]
Inductive prod (A B:Type) : Type :=
  pair : A -> B -> A * B

where "x * y" := (prod x y) : type_scope.

Add Printing Let prod.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Arguments pair {A B} _ _.

Register prod as core.prod.type.
Register pair as core.prod.intro.
Register prod_rect as core.prod.rect.

Section projections.
  Context {A : Type} {B : Type}.

  Definition fst (p:A * B) := match p with (x, y) => x end.
  Definition snd (p:A * B) := match p with (x, y) => y end.

  Register fst as core.prod.proj1.
  Register snd as core.prod.proj2.

End projections.

Hint Resolve pair inl inr: core.

Lemma surjective_pairing :
  forall (A B:Type) (p:A * B), p = (fst p, snd p).
Proof.
  destruct p; reflexivity.
Qed.

Lemma injective_projections :
  forall (A B:Type) (p1 p2:A * B),
    fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; simpl; intros Hfst Hsnd.
  rewrite Hfst; rewrite Hsnd; reflexivity.
Qed.

Lemma pair_equal_spec :
  forall (A B : Type) (a1 a2 : A) (b1 b2 : B),
    (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof with auto.
  split; intros.
  - split.
    + replace a1 with (fst (a1, b1)); replace a2 with (fst (a2, b2))...
      rewrite H...
    + replace b1 with (snd (a1, b1)); replace b2 with (snd (a2, b2))...
      rewrite H...
  - destruct H; subst...
Qed.

Definition prod_uncurry (A B C:Type) (f:A * B -> C)
  (x:A) (y:B) : C := f (x,y).

Definition prod_curry (A B C:Type) (f:A -> B -> C)
  (p:A * B) : C := match p with (x, y) => f x y end.

Import EqNotations.

Lemma rew_pair : forall A (P Q : A->Type) x1 x2 (y1:P x1) (y2:Q x1) (H:x1=x2),
  (rew H in y1, rew H in y2) = rew [fun x => (P x * Q x)%type] H in (y1,y2).
Proof.
  destruct H. reflexivity.
Defined.

(** Polymorphic lists and some operations *)

#[universes(template)]
Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} a l.

Declare Scope list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

Infix "::" := cons (at level 60, right associativity) : list_scope.

Register list as core.list.type.
Register nil as core.list.nil.
Register cons as core.list.cons.

Local Open Scope list_scope.

Definition length (A : Type) : list A -> nat :=
  fix length l :=
  match l with
   | nil => O
   | _ :: l' => S (length l')
  end.

(** Concatenation of two lists *)

Definition app (A : Type) : list A -> list A -> list A :=
  fix app l m :=
  match l with
   | nil => m
   | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.

(* Unset Universe Polymorphism. *)

(********************************************************************)
(** * The comparison datatype *)

Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.

Register comparison as core.comparison.type.
Register Eq as core.comparison.Eq.
Register Lt as core.comparison.Lt.
Register Gt as core.comparison.Gt.

Lemma comparison_eq_stable : forall c c' : comparison, ~~ c = c' -> c = c'.
Proof.
  destruct c, c'; intro H; reflexivity || destruct H; discriminate.
Qed.

Definition CompOpp (r:comparison) :=
  match r with
    | Eq => Eq
    | Lt => Gt
    | Gt => Lt
  end.

Lemma CompOpp_involutive : forall c, CompOpp (CompOpp c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Lemma CompOpp_inj : forall c c', CompOpp c = CompOpp c' -> c = c'.
Proof.
  destruct c; destruct c'; auto; discriminate.
Qed.

Lemma CompOpp_iff : forall c c', CompOpp c = c' <-> c = CompOpp c'.
Proof.
  split; intros; apply CompOpp_inj; rewrite CompOpp_involutive; auto.
Qed.

(** The [CompareSpec] inductive relates a [comparison] value with three
   propositions, one for each possible case. Typically, it can be used to
   specify a comparison function via some equality and order predicates.
   Interest: [CompareSpec] behave nicely with [case] and [destruct]. *)

Inductive CompareSpec (Peq Plt Pgt : Prop) : comparison -> Prop :=
 | CompEq : Peq -> CompareSpec Peq Plt Pgt Eq
 | CompLt : Plt -> CompareSpec Peq Plt Pgt Lt
 | CompGt : Pgt -> CompareSpec Peq Plt Pgt Gt.
Hint Constructors CompareSpec : core.

(** For having clean interfaces after extraction, [CompareSpec] is declared
    in Prop. For some situations, it is nonetheless useful to have a
    version in Type. Interestingly, these two versions are equivalent. *)

Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type :=
 | CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq
 | CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt
 | CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.
Hint Constructors CompareSpecT : core.

Lemma CompareSpec2Type : forall Peq Plt Pgt c,
 CompareSpec Peq Plt Pgt c -> CompareSpecT Peq Plt Pgt c.
Proof.
 destruct c; intros H; constructor; inversion_clear H; auto.
Defined.

(** As an alternate formulation, one may also directly refer to predicates
 [eq] and [lt] for specifying a comparison, rather that fully-applied
 propositions. This [CompSpec] is now a particular case of [CompareSpec]. *)

Definition CompSpec {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Prop :=
 CompareSpec (eq x y) (lt x y) (lt y x).

Definition CompSpecT {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Type :=
 CompareSpecT (eq x y) (lt x y) (lt y x).
Hint Unfold CompSpec CompSpecT : core.

Lemma CompSpec2Type : forall A (eq lt:A->A->Prop) x y c,
 CompSpec eq lt x y c -> CompSpecT eq lt x y c.
Proof. intros. apply CompareSpec2Type; assumption. Defined.

(******************************************************************)
(** * Misc Other Datatypes *)

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [identity_refl A a] *)
(** Beware: this inductive actually falls into [Prop], as the sole
    constructor has no arguments and [-indices-matter] is not
    activated in the standard library. *)

Inductive identity (A:Type) (a:A) : A -> Type :=
  identity_refl : identity a a.
Hint Resolve identity_refl: core.

Arguments identity_ind [A] a P f y i.
Arguments identity_rec [A] a P f y i.
Arguments identity_rect [A] a P f y i.

Register identity as core.identity.type.
Register identity_refl as core.identity.refl.
Register identity_ind as core.identity.ind.

(** Identity type *)

Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.

Definition IDProp := forall A:Prop, A -> A.
Definition idProp : IDProp := fun A x => x.

Register IDProp as core.IDProp.type.
Register idProp as core.IDProp.idProp.

(* begin hide *)

(* Compatibility *)

Notation prodT := prod (only parsing).
Notation pairT := pair (only parsing).
Notation prodT_rect := prod_rect (only parsing).
Notation prodT_rec := prod_rec (only parsing).
Notation prodT_ind := prod_ind (only parsing).
Notation fstT := fst (only parsing).
Notation sndT := snd (only parsing).
Notation prodT_uncurry := prod_uncurry (only parsing).
Notation prodT_curry := prod_curry (only parsing).

(* end hide *)
