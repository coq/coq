(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Equality is decidable on [nat] *)
V7only [Import nat_scope.].
Open Local Scope nat_scope.

(*
Lemma not_eq_sym : (A:Set)(p,q:A)(~p=q) -> ~(q=p).
Proof sym_not_eq.
Hints Immediate not_eq_sym : arith.
*)
Notation not_eq_sym := sym_not_eq.

Implicit Variables Type m,n,p,q:nat.

Require Arith.
Require Peano_dec.
Require Compare_dec.

Definition le_or_le_S := le_le_S_dec.

Definition compare := gt_eq_gt_dec.

Lemma le_dec : (n,m:nat) {le n m} + {le m n}.
Proof le_ge_dec.

Definition lt_or_eq := [n,m:nat]{(gt m n)}+{n=m}.

Lemma le_decide : (n,m:nat)(le n m)->(lt_or_eq n m).
Proof le_lt_eq_dec.

Lemma le_le_S_eq : (p,q:nat)(le p q)->((le (S p) q)\/(p=q)).
Proof le_lt_or_eq.

(* By special request of G. Kahn - Used in Group Theory *)
Lemma discrete_nat : (m, n: nat) (lt m n) ->
   (S m) = n \/ (EX r: nat | n = (S (S (plus m r)))).
Proof.
Intros m n H.
LApply (lt_le_S m n); Auto with arith.
Intro H'; LApply (le_lt_or_eq (S m) n); Auto with arith.
NewInduction 1; Auto with arith.
Right; Exists (minus n (S (S m))); Simpl.
Rewrite (plus_sym m (minus n (S (S m)))).
Rewrite (plus_n_Sm (minus n (S (S m))) m).
Rewrite (plus_n_Sm (minus n (S (S m))) (S m)).
Rewrite (plus_sym (minus n (S (S m))) (S (S m))); Auto with arith.
Qed.

Require Export Wf_nat.

Require Export Min.
