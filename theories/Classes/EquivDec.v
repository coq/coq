(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Decidable equivalences.
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id$ *)

Set Manual Implicit Arguments.

(** Export notations. *)

Require Export Coq.Classes.Equivalence.

(** The [DecidableSetoid] class asserts decidability of a [Setoid]. It can be useful in proofs to reason more 
   classically. *)

Require Import Coq.Logic.Decidable.

Open Scope equiv_scope.

Class DecidableEquivalence `(equiv : Equivalence A) :=
  setoid_decidable : forall x y : A, decidable (x === y).

(** The [EqDec] class gives a decision procedure for a particular setoid equality. *)

Class EqDec A R {equiv : Equivalence R} :=
  equiv_dec : forall x y : A, { x === y } + { x =/= y }.

(** We define the [==] overloaded notation for deciding equality. It does not take precedence
   of [==] defined in the type scope, hence we can have both at the same time. *)

Notation " x == y " := (equiv_dec (x :>) (y :>)) (no associativity, at level 70) : equiv_scope.

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
  match x with
    | left H => @right _ _ H 
    | right H => @left _ _ H 
  end.

Require Import Coq.Program.Program.

Open Local Scope program_scope.

(** Invert the branches. *)

Program Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x === y } := swap_sumbool (x == y).

(** Overloaded notation for inequality. *)

Infix "<>" := nequiv_dec (no associativity, at level 70) : equiv_scope.

(** Define boolean versions, losing the logical information. *)

Definition equiv_decb `{EqDec A} (x y : A) : bool :=
  if x == y then true else false.

Definition nequiv_decb `{EqDec A} (x y : A) : bool :=
  negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).

(** Decidable leibniz equality instances. *)

Require Import Coq.Arith.Peano_dec.

(** The equiv is burried inside the setoid, but we can recover it by specifying which setoid we're talking about. *)

Program Instance nat_eq_eqdec : EqDec nat eq :=
  equiv_dec := eq_nat_dec.

Require Import Coq.Bool.Bool.

Program Instance bool_eqdec : EqDec bool eq :=
  equiv_dec := bool_dec.

Program Instance unit_eqdec : EqDec unit eq :=
  equiv_dec x y := in_left.

  Next Obligation.
  Proof.
    destruct x ; destruct y.
    reflexivity.
  Qed.

Program Instance prod_eqdec `(EqDec A eq, EqDec B eq) :
  ! EqDec (prod A B) eq :=
  equiv_dec x y := 
    let '(x1, x2) := x in 
    let '(y1, y2) := y in 
    if x1 == y1 then 
      if x2 == y2 then in_left
      else in_right
    else in_right.

  Solve Obligations using unfold complement, equiv ; program_simpl.

Program Instance sum_eqdec `(EqDec A eq, EqDec B eq) :
  EqDec (sum A B) eq :=
  equiv_dec x y := 
    match x, y with
      | inl a, inl b => if a == b then in_left else in_right
      | inr a, inr b => if a == b then in_left else in_right
      | inl _, inr _ | inr _, inl _ => in_right
    end.

  Solve Obligations using unfold complement, equiv ; program_simpl.

(** Objects of function spaces with countable domains like bool have decidable equality. *)

Require Import Coq.Program.FunctionalExtensionality.

Program Instance bool_function_eqdec `(EqDec A eq) : ! EqDec (bool -> A) eq :=
  equiv_dec f g := 
    if f true == g true then
      if f false == g false then in_left
      else in_right
    else in_right.

  Solve Obligations using try red ; unfold equiv, complement ; program_simpl.

  Next Obligation.
  Proof.
    extensionality x.
    destruct x ; auto.
  Qed.

Require Import List.

Program Instance list_eqdec `(eqa : EqDec A eq) : ! EqDec (list A) eq :=
  equiv_dec := 
    fix aux (x : list A) y { struct x } :=
    match x, y with
      | nil, nil => in_left
      | cons hd tl, cons hd' tl' => 
        if hd == hd' then
          if aux tl tl' then in_left else in_right
          else in_right
      | _, _ => in_right
    end.

  Solve Obligations using unfold equiv, complement in * ; program_simpl ; intuition (discriminate || eauto).

  Next Obligation.
  Proof. clear aux. red in H0. subst. 
    destruct y; intuition (discriminate || eauto).
  Defined.
