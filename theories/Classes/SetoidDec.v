(* -*- coq-prog-args: ("-emacs-U" "-nois") -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certified Haskell Prelude.
 * Author: Matthieu Sozeau
 * Institution: LRI, CNRS UMR 8623 - UniversitÃcopyright Paris Sud
 *              91405 Orsay, France *)

(* $Id: FSetAVL_prog.v 616 2007-08-08 12:28:10Z msozeau $ *)

Set Implicit Arguments.
Unset Strict Implicit.

Require Import Coq.Classes.SetoidClass.

Class [ Setoid A R ] => EqDec :=
  equiv_dec : forall x y : A, { R x y } + { ~ R x y }.

Infix "==" := equiv_dec (no associativity, at level 70).

Require Import Coq.Program.Program.

Program Definition nequiv_dec [ EqDec A R ] (x y : A) : { ~ R x y } + { R x y } :=
  if x == y then right else left.

Infix "<>" := nequiv_dec (no associativity, at level 70).

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

Solve Obligations using program_simpl ; red ; intro ; autoinjections ; discriminates.

Program Instance [ EqDec A eq ] => bool_function_eqdec : EqDec (bool -> A) eq :=
  equiv_dec f g := 
    if f true == g true then
      if f false == g false then left
      else right
    else right.

Require Import Coq.Program.FunctionalExtensionality.

Next Obligation.
Proof.
  extensionality x.
  destruct x ; auto.
Qed.

Next Obligation.
Proof.
  red ; intro ; subst.
  discriminates.
Qed.
