(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Arith.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n:nat.

(** maximum of two natural numbers *)

Fixpoint max [n:nat] : nat -> nat :=  
[m:nat]Cases n m of
          O      _     => m
       | (S n')  O     => n
       | (S n') (S m') => (S (max n' m'))
       end.

(** Simplifications of [max] *)

Lemma max_SS : (n,m:nat)((S (max n m))=(max (S n) (S m))).
Proof.
Auto with arith.
Qed.

Lemma max_sym : (n,m:nat)(max n m)=(max m n).
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

(** [max] and [le] *)

Lemma max_l : (n,m:nat)(le m n)->(max n m)=n.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

Lemma max_r : (n,m:nat)(le n m)->(max n m)=m.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

Lemma le_max_l : (n,m:nat)(le n (max n m)).
Proof.
NewInduction n; Intros; Simpl; Auto with arith.
Elim m; Intros; Simpl; Auto with arith.
Qed.

Lemma le_max_r : (n,m:nat)(le m (max n m)).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Simpl; Auto with arith.
Qed.
Hints Resolve max_r max_l le_max_l le_max_r: arith v62.


(** [max n m] is equal to [n] or [m] *)

Lemma max_dec : (n,m:nat){(max n m)=n}+{(max n m)=m}.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Elim (IHn m);Intro H;Elim H;Auto.
Qed.

Lemma max_case : (n,m:nat)(P:nat->Set)(P n)->(P m)->(P (max n m)).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Intros; Simpl; Auto with arith.
Pattern (max n m); Apply IHn ; Auto with arith.
Qed.

Lemma max_case2 : (n,m:nat)(P:nat->Prop)(P n)->(P m)->(P (max n m)).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Intros; Simpl; Auto with arith.
Pattern (max n m); Apply IHn ; Auto with arith.
Qed.


