(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Set Implicit Arguments.

Require Import Notations.
Require Import Logic.
Declare ML Module "nat_syntax_plugin".


(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.

(** [bool] is the datatype of the boolean values [true] and [false] *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

Add Printing If bool.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

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

(*******************************)
(** * Properties of [andb]     *)
(*******************************)

Lemma andb_prop : forall a b:bool, andb a b = true -> a = true /\ b = true.
Proof.
  destruct a; destruct b; intros; split; try (reflexivity || discriminate).
Qed.
Hint Resolve andb_prop: bool.

Lemma andb_true_intro :
  forall b1 b2:bool, b1 = true /\ b2 = true -> andb b1 b2 = true.
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.
Hint Resolve andb_true_intro: bool.

(** Interpretation of booleans as propositions *)

Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.

Hint Constructors eq_true : eq_true.

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

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that the constructor name is the letter O.
    Numbers in [nat] can be denoted using a decimal notation;
    e.g. [3%nat] abbreviates [S (S (S O))] *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Delimit Scope nat_scope with nat.
Bind Scope nat_scope with nat.
Arguments Scope S [nat_scope].

(** [Empty_set] has no inhabitant *)

Inductive Empty_set : Set :=.

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity (A:Type) (a:A) : A -> Type :=
  identity_refl : identity a a.
Hint Resolve identity_refl: core.

Implicit Arguments identity_ind [A].
Implicit Arguments identity_rec [A].
Implicit Arguments identity_rect [A].

(** [option A] is the extension of [A] with an extra element [None] *)

Inductive option (A:Type) : Type :=
  | Some : A -> option A
  | None : option A.

Implicit Arguments None [A].

Definition option_map (A B:Type) (f:A->B) o :=
  match o with
    | Some a => Some (f a)
    | None => None
  end.

(** [sum A B], written [A + B], is the disjoint sum of [A] and [B] *)

Inductive sum (A B:Type) : Type :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Type) : Type :=
  pair : A -> B -> prod A B.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Section projections.
  Variables A B : Type.
  Definition fst (p:A * B) := match p with
				| (x, y) => x
                              end.
  Definition snd (p:A * B) := match p with
				| (x, y) => y
                              end.
End projections.

Hint Resolve pair inl inr: core.

Lemma surjective_pairing :
  forall (A B:Type) (p:A * B), p = pair (fst p) (snd p).
Proof.
  destruct p; reflexivity.
Qed.

Lemma injective_projections :
  forall (A B:Type) (p1 p2:A * B),
    fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; simpl in |- *; intros Hfst Hsnd.
  rewrite Hfst; rewrite Hsnd; reflexivity.
Qed.

Definition prod_uncurry (A B C:Type) (f:prod A B -> C)
  (x:A) (y:B) : C := f (pair x y).

Definition prod_curry (A B C:Type) (f:A -> B -> C)
  (p:prod A B) : C := match p with
                       | pair x y => f x y
                       end.

(** Comparison *)

Inductive comparison : Set :=
  | Eq : comparison
  | Lt : comparison
  | Gt : comparison.

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

(** The [CompSpec] inductive will be used to relate a [compare] function
    (returning a comparison answer) and some equality and order predicates.
    Interest: [CompSpec] behave nicely with [destruct]. *)

Inductive CompSpec {A} (eq lt : A->A->Prop)(x y:A) : comparison -> Prop :=
 | CompEq : eq x y -> CompSpec eq lt x y Eq
 | CompLt : lt x y -> CompSpec eq lt x y Lt
 | CompGt : lt y x -> CompSpec eq lt x y Gt.
Hint Constructors CompSpec.


(** Identity *)

Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.

(** Polymorphic lists and some operations *)

Inductive list (A : Type) : Type :=
 | nil : list A
 | cons : A -> list A -> list A.

Implicit Arguments nil [A].
Infix "::" := cons (at level 60, right associativity) : list_scope.
Delimit Scope list_scope with list.
Bind Scope list_scope with list.

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
