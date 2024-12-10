(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** N.B.: Using this encoding of bit vectors is discouraged.
See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v>. *)
Attributes deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.").
Local Set Warnings "-deprecated".

(** Bit vectors. Contribution by Jean Duprat (ENS Lyon). *)

Require Export Bool Sumbool.
#[local] Set Warnings "-stdlib-vector".
Require Vector.
Export Vector.VectorNotations.

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

#[deprecated(since="8.20", note="Consider [list bool] instead. Please open an issue if you would like to keep using Bvector.")]
Definition Bvector := Vector.t bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bnil := @Vector.nil bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bcons := @Vector.cons bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bvect_true := Vector.const true.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bvect_false := Vector.const false.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Blow := @Vector.hd bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bhigh := @Vector.tl bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bsign := @Vector.last bool.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition Bneg := @Vector.map _ _ negb.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BVand := @Vector.map2 _ _ _ andb.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BVor := @Vector.map2 _ _ _ orb.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BVxor := @Vector.map2 _ _ _ xorb.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BVeq m n := @Vector.eqb bool eqb m n.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BshiftL (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bcons carry n (Vector.shiftout bv).

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BshiftRl (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bhigh (S n) (Vector.shiftin carry bv).

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Definition BshiftRa (n:nat) (bv:Bvector (S n)) :=
  Bhigh (S n) (Vector.shiftrepeat bv).

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Fixpoint BshiftL_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftL n (BshiftL_iter n bv p') false
  end.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Fixpoint BshiftRl_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRl n (BshiftRl_iter n bv p') false
  end.

#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Fixpoint BshiftRa_iter (n:nat) (bv:Bvector (S n)) (p:nat) : Bvector (S n) :=
  match p with
    | O => bv
    | S p' => BshiftRa n (BshiftRa_iter n bv p')
  end.

End BOOLEAN_VECTORS.

Module BvectorNotations.
Declare Scope Bvector_scope.
Delimit Scope Bvector_scope with Bvector.
#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Notation "^~ x" := (Bneg _ x) (at level 35, right associativity) : Bvector_scope.
#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Infix    "^&"   := (BVand  _) (at level 40, left  associativity) : Bvector_scope.
#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Infix    "^⊕"   := (BVxor  _) (at level 45, left  associativity) : Bvector_scope.
#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Infix    "^|"   := (BVor   _) (at level 50, left  associativity) : Bvector_scope.
#[deprecated(since="8.20", note="Consider [list bool] instead. See <https://github.com/coq/coq/blob/master/stdlib/theories/Vectors/Vector.v> for details. Please open an issue if you would like to keep using Bvector.")]
Infix    "=?"   := (BVeq _ _) (at level 70, no    associativity) : Bvector_scope.
Open Scope Bvector_scope.
End BvectorNotations.
