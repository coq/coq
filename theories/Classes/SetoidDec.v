(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Decidable setoid equality theory.
 *
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Set Implicit Arguments.
Unset Strict Implicit.

(** Export notations. *)

Require Export Coq.Classes.SetoidClass.

(** The [EqDec] class gives a decision procedure for a particular setoid equality. *)

Class [ Setoid A R ] => EqDec :=
  equiv_dec : forall x y : A, { x == y } + { x =/= y }.

(** We define the [==] overloaded notation for deciding equality. It does not take precedence
   of [==] defined in the type scope, hence we can have both at the same time. *)

Notation " x == y " := (equiv_dec (x :>) (y :>)) (no associativity, at level 70).

(** Use program to solve some obligations. *)

Definition swap_sumbool `A B` (x : { A } + { B }) : { B } + { A } :=
  match x with
    | left H => right _ H 
    | right H => left _ H 
  end.

Require Import Coq.Program.Program.

(** Invert the branches. *)

Program Definition nequiv_dec [ EqDec A R ] (x y : A) : { x =/= y } + { x == y } := swap_sumbool (x == y).

(** Overloaded notation for inequality. *)

Infix "=/=" := nequiv_dec (no associativity, at level 70).

(** Define boolean versions, losing the logical information. *)

Definition equiv_decb [ EqDec A R ] (x y : A) : bool :=
  if x == y then true else false.

Definition nequiv_decb [ EqDec A R ] (x y : A) : bool :=
  negb (equiv_decb x y).

Infix "==b" := equiv_decb (no associativity, at level 70).
Infix "<>b" := nequiv_decb (no associativity, at level 70).

(** Decidable leibniz equality instances. *)

Implicit Arguments eq [[A]].

Require Import Coq.Arith.Arith.

Program Instance nat_eqdec : EqDec nat eq :=
  equiv_dec := eq_nat_dec.

Require Import Coq.Bool.Bool.

Program Instance bool_eqdec : EqDec bool eq :=
  equiv_dec := bool_dec.

Program Instance unit_eqdec : EqDec unit eq :=
  equiv_dec x y := left.

  Next Obligation.
  Proof.
    destruct x ; destruct y.
    reflexivity.
  Qed.

Program Instance [ EqDec A eq, EqDec B eq ] => prod_eqdec : EqDec (prod A B) eq :=
  equiv_dec x y := 
    dest x as (x1, x2) in 
    dest y as (y1, y2) in 
    if x1 == y1 then 
      if x2 == y2 then left
      else right
    else right.

  Solve Obligations using unfold equiv ; program_simpl ; try red ; intros ; autoinjections ; discriminates.

(** Objects of function spaces with countable domains like bool have decidable equality. *)

Require Import Coq.Program.FunctionalExtensionality.

Program Instance [ EqDec A eq ] => bool_function_eqdec : EqDec (bool -> A) eq :=
  equiv_dec f g := 
    if f true == g true then
      if f false == g false then left
      else right
    else right.

  Solve Obligations using try red ; unfold equiv ; program_simpl.

  Next Obligation.
  Proof.
    red.
    extensionality x.
    destruct x ; auto.
  Qed.

