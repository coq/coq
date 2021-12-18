(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Set Implicit Arguments.

Require Import Notations.
Require Import Ltac.
Require Import Logic.

(********************************************************************)
(** * Datatypes with zero and one element *)

(** [Empty_set] is a datatype with no inhabitant *)

Inductive Empty_set : Set :=.

Register Empty_set as core.Empty_set.type.

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.

Register unit as core.unit.type.
Register tt as core.unit.tt.

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
Register implb as core.bool.implb.
Register xorb as core.bool.xorb.
Register negb as core.bool.negb.

(** Basic properties of [andb] *)

Lemma andb_prop (a b:bool) : andb a b = true -> a = true /\ b = true.
Proof.
  destruct a, b; repeat split; assumption.
Qed.
#[global]
Hint Resolve andb_prop: bool.

Register andb_prop as core.bool.andb_prop.

Lemma andb_true_intro (b1 b2:bool) :
  b1 = true /\ b2 = true -> andb b1 b2 = true.
Proof.
  destruct b1; destruct b2; simpl; intros [? ?]; assumption.
Qed.
#[global]
Hint Resolve andb_true_intro: bool.

Register andb_true_intro as core.bool.andb_true_intro.

(** Interpretation of booleans as propositions *)

Inductive eq_true : bool -> Prop := is_eq_true : eq_true true.

#[global]
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
#[global]
Hint Constructors BoolSpec : core.

Register BoolSpec as core.BoolSpec.type.
Register BoolSpecT as core.BoolSpec.BoolSpecT.
Register BoolSpecF as core.BoolSpec.BoolSpecF.

(********************************************************************)
(** * Peano natural numbers *)

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that the constructor name is the letter O.
    Numbers in [nat] can be denoted using a decimal notation;
    e.g. [3%nat] abbreviates [S (S (S O))] *)

Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Declare Scope hex_nat_scope.
Delimit Scope hex_nat_scope with xnat.

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

Register sum as core.sum.type.
Register inl as core.sum.inl.
Register inr as core.sum.inr.

Local Set Primitive Projections.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

#[universes(template)]
Record prod (A B:Type) : Type := pair { fst: A ; snd: B }.

Local Unset Primitive Projections.

Notation "x * y" := (prod x y) : type_scope.

Add Printing Let prod.

Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Scheme prod_ind := Induction for prod Sort Prop.
Scheme prod_rec := Induction for prod Sort Set.
Scheme prod_rect := Induction for prod Sort Type.

Register prod as core.prod.type.
Register pair as core.prod.intro.
Register prod_rect as core.prod.rect.

Register fst as core.prod.proj1.
Register snd as core.prod.proj2.

#[global]
Hint Resolve pair inl inr: core.

Lemma surjective_pairing (A B:Type) (p:A * B) : p = (fst p, snd p).
Proof.
  destruct p; reflexivity.
Qed.

Lemma injective_projections (A B:Type) (p1 p2:A * B) :
    fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof.
  destruct p1; destruct p2; simpl; intros Hfst Hsnd.
  rewrite Hfst; rewrite Hsnd; reflexivity.
Qed.

Lemma pair_equal_spec (A B : Type) (a1 a2 : A) (b1 b2 : B) :
    (a1, b1) = (a2, b2) <-> a1 = a2 /\ b1 = b2.
Proof with auto.
  split; intro H.
  - split.
    + replace a1 with (fst (a1, b1)); replace a2 with (fst (a2, b2))...
      rewrite H...
    + replace b1 with (snd (a1, b1)); replace b2 with (snd (a2, b2))...
      rewrite H...
  - destruct H; subst...
Qed.

Definition curry {A B C:Type} (f:A * B -> C)
  (x:A) (y:B) : C := f (x,y).

Definition uncurry {A B C:Type} (f:A -> B -> C)
  (p:A * B) : C := match p with (x, y) => f x y end.

(* These were deprecated in 8.13 but putting the "deprecated"
   attribute on a Definition. Since, such a deprecation likely got
   unnoticed from users, it was decided in 8.15 to put the attribute
   on a Notation instead (thus printing deprecation warning when used)
   and should probably be removed in 8.17 as if it had been
   deprecated(since = "8.15", *)
#[deprecated(since = "8.13", note = "Use curry instead.")]
Definition prod_uncurry_subdef (A B C:Type) : (A * B -> C) -> A -> B -> C := curry.
#[deprecated(since = "8.13", note = "Use curry instead.")]
Notation prod_uncurry := prod_uncurry_subdef.

#[deprecated(since = "8.13", note = "Use uncurry instead.")]
Definition prod_curry_subdef (A B C:Type) : (A -> B -> C) -> A * B -> C := uncurry.
#[deprecated(since = "8.13", note = "Use uncurry instead.")]
Notation prod_curry := prod_curry_subdef.

Import EqNotations.

Lemma rew_pair A (P Q : A->Type) x1 x2 (y1:P x1) (y2:Q x1) (H:x1=x2) :
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

Lemma comparison_eq_stable (c c' : comparison) : ~~ c = c' -> c = c'.
Proof.
  destruct c, c'; intro H; reflexivity || destruct H; discriminate.
Qed.

Definition CompOpp (r:comparison) :=
  match r with
    | Eq => Eq
    | Lt => Gt
    | Gt => Lt
  end.

Lemma CompOpp_involutive c : CompOpp (CompOpp c) = c.
Proof.
  destruct c; reflexivity.
Qed.

Lemma CompOpp_inj c c' : CompOpp c = CompOpp c' -> c = c'.
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
#[global]
Hint Constructors CompareSpec : core.

Register CompareSpec as core.CompareSpec.type.
Register CompEq as core.CompareSpec.CompEq.
Register CompLt as core.CompareSpec.CompLt.
Register CompGt as core.CompareSpec.CompGt.

(** For having clean interfaces after extraction, [CompareSpec] is declared
    in Prop. For some situations, it is nonetheless useful to have a
    version in Type. Interestingly, these two versions are equivalent. *)

Inductive CompareSpecT (Peq Plt Pgt : Prop) : comparison -> Type :=
 | CompEqT : Peq -> CompareSpecT Peq Plt Pgt Eq
 | CompLtT : Plt -> CompareSpecT Peq Plt Pgt Lt
 | CompGtT : Pgt -> CompareSpecT Peq Plt Pgt Gt.
#[global]
Hint Constructors CompareSpecT : core.

Register CompareSpecT as core.CompareSpecT.type.
Register CompEqT as core.CompareSpecT.CompEqT.
Register CompLtT as core.CompareSpecT.CompLtT.
Register CompGtT as core.CompareSpecT.CompGtT.

Lemma CompareSpec2Type Peq Plt Pgt c :
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
#[global]
Hint Unfold CompSpec CompSpecT : core.

Lemma CompSpec2Type : forall A (eq lt:A->A->Prop) x y c,
 CompSpec eq lt x y c -> CompSpecT eq lt x y c.
Proof. intros. apply CompareSpec2Type; assumption. Defined.

(******************************************************************)
(** * Misc Other Datatypes *)

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [identity_refl A a] *)

#[deprecated(since="8.16",note="Use eq instead")]
Notation identity := eq (only parsing).
#[deprecated(since="8.16",note="Use eq_refl instead")]
Notation identity_refl := eq_refl (only parsing).
#[deprecated(since="8.16",note="Use eq_ind instead")]
Notation identity_ind := eq_ind (only parsing).
#[deprecated(since="8.16",note="Use eq_rec instead")]
Notation identity_rec := eq_rec (only parsing).
#[deprecated(since="8.16",note="Use eq_rect instead")]
Notation identity_rect := eq_rect (only parsing).
#[deprecated(since="8.16",note="Use eq_sym instead")]
Notation identity_sym := eq_sym (only parsing).
#[deprecated(since="8.16",note="Use eq_trans instead")]
Notation identity_trans := eq_trans (only parsing).
#[deprecated(since="8.16",note="Use f_equal instead")]
Notation identity_congr := f_equal (only parsing).
#[deprecated(since="8.16",note="Use not_eq_sym instead")]
Notation not_identity_sym := not_eq_sym (only parsing).
#[deprecated(since="8.16",note="Use eq_ind_r instead")]
Notation identity_ind_r := eq_ind_r (only parsing).
#[deprecated(since="8.16",note="Use eq_rec_r instead")]
Notation identity_rec_r := eq_rec_r (only parsing).
#[deprecated(since="8.16",note="Use eq_rect_r instead")]
Notation identity_rect_r := eq_rect_r (only parsing).

Register eq as core.identity.type.
Register eq_refl as core.identity.refl.
Register eq_ind as core.identity.ind.
Register eq_sym as core.identity.sym.
Register eq_trans as core.identity.trans.
Register f_equal as core.identity.congr.

#[deprecated(since="8.16",note="Use eq_refl instead")]
Notation refl_id := eq_refl (only parsing).
#[deprecated(since="8.16",note="Use eq_sym instead")]
Notation sym_id := eq_sym (only parsing).
#[deprecated(since="8.16",note="Use eq_trans instead")]
Notation trans_id := eq_trans (only parsing).
#[deprecated(since="8.16",note="Use not_eq_sym instead")]
Notation sym_not_id := not_eq_sym (only parsing).

(** Identity type *)

Definition ID := forall A:Type, A -> A.
Definition id : ID := fun A x => x.

Definition IDProp := forall A:Prop, A -> A.
Definition idProp : IDProp := fun A x => x.

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
#[deprecated(since = "8.13", note = "Use curry instead.")]
Notation prodT_uncurry := prod_uncurry_subdef (only parsing).
#[deprecated(since = "8.13", note = "Use uncurry instead.")]
Notation prodT_curry := prod_curry_subdef (only parsing).

(* end hide *)
