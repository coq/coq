(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i $Id$ i*)

(** [unit] is a singleton datatype with sole inhabitant [tt] *)

Inductive unit : Set := tt : unit.

(** [bool] is the datatype of the booleans values [true] and [false] *)

Inductive bool : Set := true : bool 
                      | false : bool.

Add Printing If bool.

(** [nat] is the datatype of natural numbers built from [O] and successor [S];
    note that zero is the letter O, not the numeral 0 *)

Inductive nat : Set := O : nat 
                     | S : nat->nat.

(** [Empty_set] has no inhabitant *)

Inductive Empty_set:Set :=.

(** [identity A a] is the family of datatypes on [A] whose sole non-empty
    member is the singleton datatype [identity A a a] whose
    sole inhabitant is denoted [refl_identity A a] *)

Inductive identity [A:Set; a:A] : A->Set :=
     refl_identity: (identity A a a).
Hints Resolve refl_identity : core v62.

(** [option A] is the extension of A with a dummy element None *)

Inductive option [A:Set] : Set := Some : A -> (option A) | None : (option A).

(** [sum A B], equivalently [A + B], is the disjoint sum of [A] and [B] *)
(* Syntax defined in Specif.v *)
Inductive sum [A,B:Set] : Set
    := inl : A -> (sum A B)
     | inr : B -> (sum A B).

(** [prod A B], written [A * B], is the product of [A] and [B];
    the pair [pair A B a b] of [a] and [b] is abbreviated [(a,b)] *)

Inductive prod [A,B:Set] : Set := pair : A -> B -> (prod A B).
Add Printing Let prod.

Section projections.
   Variables A,B:Set.
   Definition fst := [p:(prod A B)]Cases p of (pair x y) => x end.
   Definition snd := [p:(prod A B)]Cases p of (pair x y) => y end.
End projections. 

Syntactic Definition Fst := (fst ? ?).
Syntactic Definition Snd := (snd ? ?).

Hints Resolve pair inl inr : core v62.
