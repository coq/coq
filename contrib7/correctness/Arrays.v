(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id$ *)

(**********************************************)
(* Functional arrays, for use in Correctness. *)
(**********************************************)

(* This is an axiomatization of arrays.
 *
 * The type (array N T) is the type of arrays ranging from 0 to N-1 
 * which elements are of type T.
 *
 * Arrays are created with new, accessed with access and modified with store. 
 *
 * Operations of accessing and storing are not guarded, but axioms are.
 * So these arrays can be viewed as arrays where accessing and storing
 * out of the bounds has no effect.
 *)


Require Export ProgInt.

Set Implicit Arguments.


(* The type of arrays *)

Parameter array : Z -> Set -> Set.


(* Functions to create, access and modify arrays *)

Parameter new : (n:Z)(T:Set) T -> (array n T).

Parameter access : (n:Z)(T:Set) (array n T) -> Z -> T.

Parameter store : (n:Z)(T:Set) (array n T) -> Z -> T -> (array n T).


(* Axioms *)

Axiom new_def : (n:Z)(T:Set)(v0:T)
                (i:Z) `0<=i<n` -> (access (new n v0) i) = v0.

Axiom store_def_1 : (n:Z)(T:Set)(t:(array n T))(v:T)
                    (i:Z) `0<=i<n` ->
                    (access (store t i v) i) = v.

Axiom store_def_2 : (n:Z)(T:Set)(t:(array n T))(v:T)
                    (i:Z)(j:Z) `0<=i<n` -> `0<=j<n` ->
		    `i <> j` ->
                    (access (store t i v) j) = (access t j).

Hints Resolve new_def store_def_1 store_def_2 : datatypes v62.

(* A tactic to simplify access in arrays *)

Tactic Definition ArrayAccess i j H :=
    Elim (Z_eq_dec i j); [ 
      Intro H; Rewrite H; Rewrite store_def_1
    | Intro H; Rewrite store_def_2; [ Idtac | Idtac | Idtac | Exact H ] ].

(* Symbolic notation for access *)

Notation "# t [ c ]" := (access t c) (at level 0, t ident)
  V8only (at level 0, t at level 0).
