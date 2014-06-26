(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import Decidable PeanoNat.
Require Eqdep_dec.
Local Open Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S n : {m : nat | S m = n} + {0 = n}.
Proof.
  induction n.
  - now right.
  - left; exists n; auto.
Defined.

Notation eq_nat_dec := Nat.eq_dec (compat "8.4").

Hint Resolve O_or_S eq_nat_dec: arith.

Theorem dec_eq_nat n m : decidable (n = m).
Proof.
  elim (Nat.eq_dec n m); [left|right]; trivial.
Defined.

Definition UIP_nat:= Eqdep_dec.UIP_dec Nat.eq_dec.

Import EqNotations.

Lemma le_unique: forall m n (h1 h2: m <= n), h1 = h2.
Proof.
fix 3.
destruct h1 as [ | i h1 ]; intros h2.
- set (Return k (le:m<=k) :=
       forall (eq:m=k),
         le_n m = (rew eq in fun (le':m<=m) => le') le).
  refine
     (match h2 as h2' return (Return _ h2') with
        | le_n _ => fun eq => _
        | le_S _ j h2 => fun eq => _
      end eq_refl).
  + rewrite (UIP_nat _ _ eq eq_refl). simpl. reflexivity.
  + exfalso. revert h2. rewrite eq. apply Nat.lt_irrefl.
- set (Return k (le:m<=k) :=
       match k as k' return (m <= k' -> Prop) with
         | 0 => fun _ => True
         | S i' => fun (le':m<=S i') => forall (H':m<=i'), le_S _ _ H' = le'
       end le).
  refine
    (match h2 as h2' return (Return _ h2') with
       | le_n _ => _
       | le_S _ j h2 => fun h1' => _
     end h1).
  + unfold Return; clear. destruct m; simpl.
    * exact I.
    * intros h1'. destruct (Nat.lt_irrefl _ h1').
  + f_equal. apply le_unique.
Qed.

(** For compatibility *)
Require Import Le Lt.
