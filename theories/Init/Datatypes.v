(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Notations.
Require Import Logic.

Set Implicit Arguments.

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set :=
    tt : unit.

(** [bool] is the datatype of the booleans values [true] and [false] *)

Inductive bool : Set :=
  | true : bool
  | false : bool.

Add Printing If bool.

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that zero is the letter O, not the numeral 0 *)

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

Inductive identity (A:Type) (a:A) : A -> Set :=
    refl_identity : identity (A:=A) a a.
Hint Resolve refl_identity: core v62.

Implicit Arguments identity_ind [A].
Implicit Arguments identity_rec [A].
Implicit Arguments identity_rect [A].

(** [option A] is the extension of A with a dummy element None *)

Inductive option (A:Set) : Set :=
  | Some : A -> option A
  | None : option A.

Implicit Arguments None [A].

(** [sum A B], equivalently [A + B], is the disjoint sum of [A] and [B] *)
(* Syntax defined in Specif.v *)
Inductive sum (A B:Set) : Set :=
  | inl : A -> sum A B
  | inr : B -> sum A B.

Notation "x + y" := (sum x y) : type_scope.

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod (A B:Set) : Set :=
    pair : A -> B -> prod A B.
Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.

Section projections.
   Variables A B : Set.
   Definition fst (p:A * B) := match p with
                               | (x, y) => x
                               end.
   Definition snd (p:A * B) := match p with
                               | (x, y) => y
                               end.
End projections. 

Hint Resolve pair inl inr: core v62.

Lemma surjective_pairing :
 forall (A B:Set) (p:A * B), p = pair (fst p) (snd p).
Proof.
destruct p; reflexivity.
Qed.

Lemma injective_projections :
 forall (A B:Set) (p1 p2:A * B),
   fst p1 = fst p2 -> snd p1 = snd p2 -> p1 = p2.
Proof.
destruct p1; destruct p2; simpl in |- *; intros Hfst Hsnd.
rewrite Hfst; rewrite Hsnd; reflexivity. 
Qed.


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
