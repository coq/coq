(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)


(**************************************************************************)
(*          Subtraction (difference between two natural numbers           *)
(**************************************************************************)


Require Lt.
Require Le.

Fixpoint minus [n:nat] : nat -> nat := 
  [m:nat]Cases n m of
            O    _     =>  O
         | (S k) O     => (S k)
         | (S k) (S l) => (minus k l)
        end. 

Lemma minus_plus_simpl : 
	(n,m,p:nat)((minus n m)=(minus (plus p n) (plus p m))).
Proof.
  Induction p; Simpl; Auto with arith.
Qed.
Hints Resolve minus_plus_simpl : arith v62.

Lemma minus_n_O : (n:nat)(n=(minus n O)).
Proof.
Induction n; Simpl; Auto with arith.
Qed.
Hints Resolve minus_n_O : arith v62.

Lemma minus_n_n : (n:nat)(O=(minus n n)).
Proof.
Induction n; Simpl; Auto with arith.
Qed.
Hints Resolve minus_n_n : arith v62.

Lemma plus_minus : (n,m,p:nat)(n=(plus m p))->(p=(minus n m)).
Proof.
Intros n m p; Pattern m n; Apply nat_double_ind; Simpl; Intros.
Replace (minus n0 O) with n0; Auto with arith.
Absurd O=(S (plus n0 p)); Auto with arith.
Auto with arith.
Qed.
Hints Immediate plus_minus : arith v62.

Lemma minus_plus : (n,m:nat)(minus (plus n m) n)=m.
Symmetry; Auto with arith.
Save.
Hints Resolve minus_plus : arith v62.

Lemma le_plus_minus : (n,m:nat)(le n m)->(m=(plus n (minus m n))).
Proof.
Intros n m Le; Pattern n m; Apply le_elim_rel; Simpl; Auto with arith.
Qed.
Hints Resolve le_plus_minus : arith v62.

Lemma le_plus_minus_r : (n,m:nat)(le n m)->(plus n (minus m n))=m.
Proof.
Symmetry; Auto with arith.
Qed.
Hints Resolve le_plus_minus_r : arith v62.


Lemma minus_Sn_m : (n,m:nat)(le m n)->((S (minus n m))=(minus (S n) m)).
Proof.
Intros n m Le; Pattern m n; Apply le_elim_rel; Simpl; Auto with arith.
Qed.
Hints Resolve minus_Sn_m : arith v62.


Lemma lt_minus : (n,m:nat)(le m n)->(lt O m)->(lt (minus n m) n).
Proof.
Intros n m Le; Pattern m n; Apply le_elim_rel; Simpl; Auto with arith.
Intros; Absurd (lt O O); Auto with arith.
Intros p q lepq Hp gtp.
Elim (le_lt_or_eq O p); Auto with arith.
Auto with arith.
Induction 1; Elim minus_n_O; Auto with arith.
Qed.
Hints Resolve lt_minus : arith v62.

Lemma lt_O_minus_lt : (n,m:nat)(lt O (minus n m))->(lt m n).
Proof.
Intros n m; Pattern n m; Apply nat_double_ind; Simpl; Auto with arith.
Intros; Absurd (lt O O); Trivial with arith.
Qed.
Hints Immediate lt_O_minus_lt : arith v62.
