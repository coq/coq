(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Require Le.
Require Lt.

Theorem zerop : (n:nat){n=O}+{lt O n}.
Destruct n; Auto with arith.
Save.

Theorem lt_eq_lt_dec : (n,m:nat){(lt n m)}+{n=m}+{(lt m n)}.
Proof.
Induction n; Induction m; Auto with arith.
Intros q H'; Elim (H q).
Induction 1; Auto with arith.
Auto with arith.
Qed.

Lemma gt_eq_gt_dec : (n,m:nat)({(gt m n)}+{n=m})+{(gt n m)}.
Proof lt_eq_lt_dec.

Lemma le_lt_dec : (n,m:nat) {le n m} + {lt m n}.
Proof.
Induction n.
Auto with arith.
Induction m.
Auto with arith.
Intros q H'; Elim (H q); Auto with arith.
Qed.

Lemma le_le_S_dec : (n,m:nat) {le n m} + {le (S m) n}.
Proof le_lt_dec.

Lemma le_ge_dec : (n,m:nat) {le n m} + {ge n m}.
Proof.
Intros; Elim (le_lt_dec n m); Auto with arith.
Qed.

Theorem le_gt_dec : (n,m:nat){(le n m)}+{(gt n m)}.
Proof le_lt_dec.


Theorem le_lt_eq_dec : (n,m:nat)(le n m)->({(lt n m)}+{n=m}).
Proof.
Intros; Elim (lt_eq_lt_dec n m); Auto with arith.
Intros; Absurd (lt m n); Auto with arith.
Qed.
