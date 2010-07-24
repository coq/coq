(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(** Bit vectors. Contribution by Jean Duprat (ENS Lyon). *)

Require Export Bool Sumbool.
Require Import Minus.

Open Local Scope nat_scope.

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

Section VECTORS.

(**
A vector is a list of size n whose elements belongs to a set A.
If the size is non-zero, we can extract the first component and the
rest of the vector, as well as the last component, or adding or
removing a component (carry) or repeating the last component at the
end of the vector.
We can also truncate the vector and remove its p last components or
reciprocally extend the vector by concatenation.
A unary function over A generates a function on vectors of size n by
applying f pointwise.
A binary function over A generates a function on pairs of vectors of
size n by applying f pointwise.
*)

Variable A : Type.

Inductive vector : nat -> Type :=
  | Vnil : vector 0
  | Vcons : forall (a:A) (n:nat), vector n -> vector (S n).

Definition Vhead (n:nat) (v:vector (S n)) :=
  match v with
  | Vcons a _ _ => a
  end.

Definition Vtail (n:nat) (v:vector (S n)) :=
  match v with
  | Vcons _ _ v => v
  end.

Definition Vlast : forall n:nat, vector (S n) -> A.
Proof.
  induction n as [| n f]; intro v.
  inversion v.
  exact a.

  inversion v as [| n0 a H0 H1].
  exact (f H0).
Defined.

Fixpoint Vconst (a:A) (n:nat) :=
  match n return vector n with
  | O => Vnil
  | S n => Vcons a _ (Vconst a n)
  end.

(** Shifting and truncating *)

Lemma Vshiftout : forall n:nat, vector (S n) -> vector n.
Proof.
  induction n as [| n f]; intro v.
  exact Vnil.

  inversion v as [| a n0 H0 H1].
  exact (Vcons a n (f H0)).
Defined.

Lemma Vshiftin : forall n:nat, A -> vector n -> vector (S n).
Proof.
  induction n as [| n f]; intros a v.
  exact (Vcons a 0 v).

  inversion v as [| a0 n0 H0 H1 ].
  exact (Vcons a (S n) (f a H0)).
Defined.

Lemma Vshiftrepeat : forall n:nat, vector (S n) -> vector (S (S n)).
Proof.
  induction n as [| n f]; intro v.
  inversion v.
  exact (Vcons a 1 v).

  inversion v as [| a n0 H0 H1 ].
  exact (Vcons a (S (S n)) (f H0)).
Defined.

Lemma Vtrunc : forall n p:nat, n > p -> vector n -> vector (n - p).
Proof.
  induction p as [| p f]; intros H v.
  rewrite <- minus_n_O.
  exact v.

  apply (Vshiftout (n - S p)).

  rewrite minus_Sn_m.
  apply f.
  auto with *.
  exact v.
  auto with *.
Defined.

(** Concatenation of two vectors *)

Fixpoint Vextend n p (v:vector n) (w:vector p) : vector (n+p) :=
  match v with
  | Vnil => w
  | Vcons a n' v' => Vcons a (n'+p) (Vextend n' p v' w)
  end.

(** Uniform application on the arguments of the vector *)

Variable f : A -> A.

Fixpoint Vunary n (v:vector n) : vector n :=
  match v with
  | Vnil => Vnil
  | Vcons a n' v' => Vcons (f a) n' (Vunary n' v')
  end.

Variable g : A -> A -> A.

Lemma Vbinary : forall n:nat, vector n -> vector n -> vector n.
Proof.
  induction n as [| n h]; intros v v0.
  exact Vnil.

  inversion v as [| a n0 H0 H1]; inversion v0 as [| a0 n1 H2 H3].
  exact (Vcons (g a a0) n (h H0 H2)).
Defined.

(** Eta-expansion of a vector *)

Definition Vid n : vector n -> vector n :=
  match n with
  | O => fun _ => Vnil
  | _ => fun v => Vcons (Vhead _ v) _ (Vtail _ v)
  end.

Lemma Vid_eq : forall (n:nat) (v:vector n), v = Vid n v.
Proof.
  destruct v; auto.
Qed.

Lemma VSn_eq :
  forall (n : nat) (v : vector (S n)), v = Vcons (Vhead _ v) _ (Vtail _ v).
Proof.
  intros.
  exact (Vid_eq _ v).
Qed.

Lemma V0_eq : forall (v : vector 0), v = Vnil.
Proof.
  intros.
  exact (Vid_eq _ v).
Qed.

End VECTORS.

(* suppressed: incompatible with Coq-Art book
Implicit Arguments Vnil [A].
Implicit Arguments Vcons [A n].
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

Definition Bvector := vector bool.

Definition Bnil := @Vnil bool.

Definition Bcons := @Vcons bool.

Definition Bvect_true := Vconst bool true.

Definition Bvect_false := Vconst bool false.

Definition Blow := Vhead bool.

Definition Bhigh := Vtail bool.

Definition Bsign := Vlast bool.

Definition Bneg := Vunary bool negb.

Definition BVand := Vbinary bool andb.

Definition BVor := Vbinary bool orb.

Definition BVxor := Vbinary bool xorb.

Definition BshiftL (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bcons carry n (Vshiftout bool n bv).

Definition BshiftRl (n:nat) (bv:Bvector (S n)) (carry:bool) :=
  Bhigh (S n) (Vshiftin bool (S n) carry bv).

Definition BshiftRa (n:nat) (bv:Bvector (S n)) :=
  Bhigh (S n) (Vshiftrepeat bool n bv).

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
