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

(** minimum of two natural numbers *)

Fixpoint min [n:nat] : nat -> nat :=  
[m:nat]Cases n m of
          O      _     => O
       | (S n')  O     => O
       | (S n') (S m') => (S (min n' m'))
       end.

(** Simplifications of [min] *)

Lemma min_SS : (n,m:nat)((S (min n m))=(min (S n) (S m))).
Proof.
Auto with arith.
Qed.

Lemma min_sym : (n,m:nat)(min n m)=(min m n).
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

(** [min] and [le] *)

Lemma min_l : (n,m:nat)(le n m)->(min n m)=n.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

Lemma min_r : (n,m:nat)(le m n)->(min n m)=m.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Qed.

Lemma le_min_l : (n,m:nat)(le (min n m) n).
Proof.
NewInduction n; Intros; Simpl; Auto with arith.
Elim m; Intros; Simpl; Auto with arith.
Qed.

Lemma le_min_r : (n,m:nat)(le (min n m) m).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Simpl; Auto with arith.
Qed.
Hints Resolve min_l min_r le_min_l le_min_r : arith v62.

(** [min n m] is equal to [n] or [m] *)

Lemma min_dec : (n,m:nat){(min n m)=n}+{(min n m)=m}.
Proof.
NewInduction n;NewInduction m;Simpl;Auto with arith.
Elim (IHn m);Intro H;Elim H;Auto.
Qed.

Lemma min_case : (n,m:nat)(P:nat->Set)(P n)->(P m)->(P (min n m)).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Intros; Simpl; Auto with arith.
Pattern (min n m); Apply IHn ; Auto with arith.
Qed.

Lemma min_case2 : (n,m:nat)(P:nat->Prop)(P n)->(P m)->(P (min n m)).
Proof.
NewInduction n; Simpl; Auto with arith.
NewInduction m; Intros; Simpl; Auto with arith.
Pattern (min n m); Apply IHn ; Auto with arith.
Qed.
