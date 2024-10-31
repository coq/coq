(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** * Decidable equivalences.

   Author: Matthieu Sozeau
   Institution: LRI, CNRS UMR 8623 - University Paris Sud
*)

(** Export notations. *)

Require Export Stdlib.Classes.Equivalence.

(** The [DecidableSetoid] class asserts decidability of a [Setoid].
   It can be useful in proofs to reason more classically. *)

Require Import Stdlib.Logic.Decidable.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.Peano_dec.

Generalizable Variables A B R.

Open Scope equiv_scope.

Class DecidableEquivalence `(equiv : Equivalence A) :=
  setoid_decidable : forall x y : A, decidable (x === y).

(** The [EqDec] class gives a decision procedure for a particular
   setoid equality. *)

Class EqDec A R {equiv : Equivalence R} :=
  equiv_dec : forall x y : A, { x === y } + { x =/= y }.

(** We define the [==] overloaded notation for deciding equality. It does not
   take precedence of [==] defined in the type scope, hence we can have both
   at the same time. *)

Notation " x == y " := (equiv_dec x y) (no associativity, at level 70) : equiv_scope.

Definition swap_sumbool {A B} (x : { A } + { B }) : { B } + { A } :=
  match x with
    | left H => @right _ _ H
    | right H => @left _ _ H
  end.

Local Open Scope program_scope.

(** Invert the branches. *)

Definition nequiv_dec `{EqDec A} (x y : A) : { x =/= y } + { x === y } := 
          swap_sumbool (x == y).


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

(** The equiv is buried inside the setoid, but we can recover it by specifying
   which setoid we're talking about. *)

#[global]
Instance nat_eq_eqdec : EqDec nat eq := eq_nat_dec.

#[global]
Instance bool_eqdec : EqDec bool eq := bool_dec.

#[global]
Instance unit_eqdec : EqDec unit eq.
Proof.
  refine (fun x y => left _).
  abstract (case x, y; reflexivity).
Defined.

#[global]
Instance prod_eqdec `(EqDec A eq, EqDec B eq) :
  EqDec (prod A B) eq.
Proof.
  refine (fun x y =>
    let '(x1, x2) := x in
    let '(y1, y2) := y in
    if x1 == y1 then
      if x2 == y2 then left _
      else right _
    else right _ ).
  all : abstract (cbv [complement equiv] in *; congruence).
Defined.

#[global]
Instance sum_eqdec `(EqDec A eq, EqDec B eq) :
  EqDec (sum A B) eq.
Proof.
  refine (fun x y =>
    match x, y with
      | inl a, inl b => if a == b then left _ else right _
      | inr a, inr b => if a == b then left _ else right _
      | inl _, inr _ | inr _, inl _ => right _
    end ).
  all : abstract (cbv [complement equiv] in *; congruence).
Defined.

(** Objects of function spaces with countable domains like bool have decidable
  equality. Proving the reflection requires functional extensionality though. *)
Require Import FunctionalExtensionality.

#[global]
Instance bool_function_eqdec `(EqDec A eq) : EqDec (bool -> A) eq.
Proof.
  refine (fun f g =>
    if f true == g true then
      if f false == g false then left _
      else right _
    else right _ ).
  all : cbv [complement equiv] in *; try abstract congruence.
  abstract (extensionality x; case x; trivial).
Defined.

Require Import List.

#[global]
Instance list_eqdec `(eqa : EqDec A eq) : EqDec (list A) eq.
  refine (
    fix aux (x y : list A) :=
    match x, y with
      | nil, nil => left _
      | cons hd tl, cons hd' tl' =>
        if hd == hd' then
          if aux tl tl' then left _ else right _
          else right _
      | _, _ => right _
    end ).
  all : abstract (cbv [complement equiv] in *; congruence).
Defined.

Local Set Warnings "-deprecated".
Require Import Stdlib.Program.Program. (* for compat *)
#[global] Obligation Tactic := unfold complement, equiv ; program_simpl.
#[export] Obligation Tactic := unfold complement, equiv ; program_simpl.
