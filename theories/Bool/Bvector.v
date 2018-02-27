(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Bit vectors. Contribution by Jean Duprat (ENS Lyon). *)

Require Export Bool Sumbool.
Require Vector.
Export Vector.VectorNotations.
Require Import Minus.

Local Open Scope nat_scope.

(**
We build bit vectors in the spirit of List.v.
The size of the vector is a parameter which is too important
to be accessible only via function "length".
The first idea is to build a record with both the list and the length.
Unfortunately, this a posteriori verification leads to
numerous lemmas for handling lengths.
The second idea is to use a dependent type in which the length
is a building parameter. This leads to structural induction that
are slightly more complex and in some cases we will use a proof-term
as definition, since the type inference mechanism for pattern-matching
is sometimes weaker that the one implemented for elimination tactiques.
*)

Section BOOLEAN_VECTORS.

(**
A bit vector is a vector over booleans.
Notice that the LEAST significant bit comes first (little-endian representation).
We extract the least significant bit (head) and the rest of the vector (tail).
We compute bitwise operation on vector: negation, and, or, xor.
We compute size-preserving shifts: to the left (towards most significant bits,
we hence use Vshiftout) and to the right (towards least significant bits,
we use Vshiftin) by inserting a 'carry' bit (logical shift) or by repeating
the most significant bit (arithmetical shift).
NOTA BENE: all shift operations expect predecessor of size as parameter
(they only work on non-empty vectors).
*)

Definition Bvector := Vector.t bool.

Definition Bnil := @Vector.nil bool.

Definition Bcons := @Vector.cons bool.

Definition Bvect_true := Vector.const true.

Definition Bvect_false := Vector.const false.

Definition Blow := @Vector.hd bool.

Definition Bhigh := @Vector.tl bool.

Definition Bsign := @Vector.last bool.

Definition Bneg := @Vector.map _ _ negb.

Definition BVand := @Vector.map2 _ _ _ andb.

Definition BVor := @Vector.map2 _ _ _ orb.

Definition BVxor := @Vector.map2 _ _ _ xorb.

Definition BshiftL (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bcons carry n (Vector.shiftout bv).

Definition BshiftRl (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bhigh (S n) (Vector.shiftin carry bv).

Definition BshiftRa (n:nat) (bv:Bvector (S n)) :=
  Bhigh (S n) (Vector.shiftrepeat bv).

Fixpoint BshiftL_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftL n (BshiftL_iter n bv p') false
  end.

Fixpoint BshiftRl_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRl n (BshiftRl_iter n bv p') false
  end.

Fixpoint BshiftRa_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRa n (BshiftRa_iter n bv p')
  end.

End BOOLEAN_VECTORS.

