(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(************************************************************************)

Lemma essai : forall x : nat, x = x.
 refine
 ((fun x0 : nat => match x0 with
                   | O => _
                   | S p => _
                   end)).

Restart.

 refine
 (fun x0 : nat => match x0 as n return (n = n) with
                  | O => _
                  | S p => _
                  end). (* OK *)

Restart.

 refine
 (fun x0 : nat => match x0 as n return (n = n) with
                  | O => _
                  | S p => _
                  end). (* OK *)

Restart.

(**
Refine [x0:nat]Cases x0 of O => ? | (S p) => ? end. (* cannot be executed *)
**)

Abort.


(************************************************************************)

Lemma T : nat.

 refine (S _).

Abort.


(************************************************************************)

Lemma essai2 : forall x : nat, x = x.

refine (fix f (x : nat) : x = x := _).

Restart.

 refine
 (fix f (x : nat) : x = x :=
    match x as n return (n = n :>nat) with
    | O => _
    | S p => _
    end).

Restart.

 refine
 (fix f (x : nat) : x = x :=
    match x as n return (n = n) with
    | O => _
    | S p => _
    end).

Restart.

 refine
 (fix f (x : nat) : x = x :=
    match x as n return (n = n :>nat) with
    | O => _
    | S p => f_equal S _
    end).

Restart.

 refine
 (fix f (x : nat) : x = x :=
    match x as n return (n = n :>nat) with
    | O => _
    | S p => f_equal S _
    end).

Abort.


(************************************************************************)
Parameter f : nat * nat -> nat -> nat.

Lemma essai : nat.

 refine (f _ ((fun x : nat => _:nat) 0)).

Restart.

 refine (f _ 0).

Abort.


(************************************************************************)

Parameter P : nat -> Prop.

Lemma essai : {x : nat | x = 1}.

 refine (exist _ 1 _).  (* ECHEC *)

Restart.

(* mais si on contraint par le but alors ca marche : *)
(* Remarque : on peut toujours faire ça *)
 refine (exist _ 1 _:{x : nat | x = 1}).

Restart.

 refine (exist (fun x : nat => x = 1) 1 _).

Abort.


(************************************************************************)

Lemma essai : forall n : nat, {x : nat | x = S n}.

 refine
 (fun n : nat =>
  match n return {x : nat | x = S n} with
  | O => _
  | S p => _
  end).

Restart.

 refine
   (fun n : nat => match n with
                  | O => _
                  | S p => _
                  end).

Restart.

 refine
 (fun n : nat =>
  match n return {x : nat | x = S n} with
  | O => _
  | S p => _
  end).

Restart.

 refine
 (fix f (n : nat) : {x : nat | x = S n} :=
    match n return {x : nat | x = S n} with
    | O => _
    | S p => _
    end).

Restart.

 refine
 (fix f (n : nat) : {x : nat | x = S n} :=
    match n return {x : nat | x = S n} with
    | O => _
    | S p => _
    end).

exists 1. trivial.
elim (f p).
 refine
 (fun (x : nat) (h : x = S p) => exist (fun x : nat => x = S (S p)) (S x) _).
 rewrite h. auto.
Qed.



(* Quelques essais de recurrence bien fondée *)

Require Import Wf.
Require Import Wf_nat.

Lemma essai_wf : nat -> nat.

 refine
 (fun x : nat =>
  well_founded_induction _ (fun _ : nat => nat -> nat)
    (fun (phi0 : nat) (w : forall phi : nat, phi < phi0 -> nat -> nat) =>
     w x _) x x).
exact lt_wf.

Abort.


Require Import Compare_dec.
Require Import Lt.

Lemma fibo : nat -> nat.
 refine
 (well_founded_induction _ (fun _ : nat => nat)
    (fun (x0 : nat) (fib : forall x : nat, x < x0 -> nat) =>
     match zerop x0 with
     | left _ => 1
     | right h1 =>
         match zerop (pred x0) with
         | left _ => 1
         | right h2 => fib (pred x0) _ + fib (pred (pred x0)) _
         end
     end)).
exact lt_wf.
auto with arith.
apply lt_trans with (m := pred x0); auto with arith.
Qed.

