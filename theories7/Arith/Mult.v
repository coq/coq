(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Export Plus.
Require Export Minus.
Require Export Lt.
Require Export Le.

V7only [Import nat_scope.].
Open Local Scope nat_scope.

Implicit Variables Type m,n,p:nat.

(** Zero property *)

Lemma mult_0_r : (n:nat) (mult n O)=O.
Proof.
Intro; Symmetry; Apply mult_n_O.
Qed.

Lemma mult_0_l : (n:nat) (mult O n)=O.
Proof.
Reflexivity.
Qed.

(** Distributivity *)

Lemma mult_plus_distr : 
      (n,m,p:nat)((mult (plus n m) p)=(plus (mult n p) (mult m p))).
Proof.
Intros; Elim n; Simpl; Intros; Auto with arith.
Elim plus_assoc_l; Elim H; Auto with arith.
Qed.
Hints Resolve mult_plus_distr : arith v62.

Lemma mult_plus_distr_r : (n,m,p:nat) (mult n (plus m p))=(plus (mult n m) (mult n p)).
Proof.
  NewInduction n. Trivial.
  Intros. Simpl. Rewrite (IHn m p). Apply sym_eq. Apply plus_permute_2_in_4.
Qed.

Lemma mult_minus_distr : (n,m,p:nat)((mult (minus n m) p)=(minus (mult n p) (mult m p))).
Proof.
Intros; Pattern n m; Apply nat_double_ind; Simpl; Intros; Auto with arith.
Elim minus_plus_simpl; Auto with arith.
Qed.
Hints Resolve mult_minus_distr : arith v62.

(** Associativity *)

Lemma mult_assoc_r : (n,m,p:nat)((mult (mult n m) p) = (mult n (mult m p))).
Proof.
Intros; Elim n; Intros; Simpl; Auto with arith.
Rewrite mult_plus_distr.
Elim H; Auto with arith.
Qed.
Hints Resolve mult_assoc_r : arith v62.

Lemma mult_assoc_l : (n,m,p:nat)(mult n (mult m p)) = (mult (mult n m) p).
Proof.
Auto with arith.
Qed.
Hints Resolve mult_assoc_l : arith v62.

(** Commutativity *)

Lemma mult_sym : (n,m:nat)(mult n m)=(mult m n).
Proof.
Intros; Elim n; Intros; Simpl; Auto with arith.
Elim mult_n_Sm.
Elim H; Apply plus_sym.
Qed.
Hints Resolve mult_sym : arith v62.

(** 1 is neutral *)

Lemma mult_1_n : (n:nat)(mult (S O) n)=n.
Proof.
Simpl; Auto with arith.
Qed.
Hints Resolve mult_1_n : arith v62.

Lemma mult_n_1 : (n:nat)(mult n (S O))=n.
Proof.
Intro; Elim mult_sym; Auto with arith.
Qed.
Hints Resolve mult_n_1 : arith v62.

(** Compatibility with orders *)

Lemma mult_O_le : (n,m:nat)(m=O)\/(le n (mult m n)).
Proof.
NewInduction m; Simpl; Auto with arith.
Qed.
Hints Resolve mult_O_le : arith v62.

Lemma mult_le_compat_l : (n,m,p:nat) (le n m) -> (le (mult p n) (mult p m)).
Proof.
  NewInduction p as [|p IHp]. Intros. Simpl. Apply le_n.
  Intros. Simpl. Apply le_plus_plus. Assumption.
  Apply IHp. Assumption.
Qed.
Hints Resolve mult_le_compat_l : arith.
V7only [
Notation mult_le := [m,n,p:nat](mult_le_compat_l p n m).
].


Lemma le_mult_right : (m,n,p:nat)(le m n)->(le (mult m p) (mult n p)).
Intros m n p H.
Rewrite mult_sym. Rewrite (mult_sym n).
Auto with arith.
Qed.

Lemma le_mult_mult :
  (m,n,p,q:nat)(le m n)->(le p q)->(le (mult m p) (mult n q)).
Proof.
Intros m n p q Hmn Hpq; NewInduction Hmn.
NewInduction Hpq.
(* m*p<=m*p *)
Apply le_n.
(* m*p<=m*m0 -> m*p<=m*(S m0) *)
Rewrite <- mult_n_Sm; Apply le_trans with (mult m m0).
Assumption.
Apply le_plus_l.
(* m*p<=m0*q -> m*p<=(S m0)*q *)
Simpl; Apply le_trans with (mult m0 q).
Assumption.
Apply le_plus_r.
Qed.

Lemma mult_lt : (m,n,p:nat) (lt n p) -> (lt (mult (S m) n) (mult (S m) p)).
Proof.
  Intro m; NewInduction m. Intros. Simpl. Rewrite <- plus_n_O. Rewrite <- plus_n_O. Assumption.
  Intros. Exact (lt_plus_plus ? ? ? ? H (IHm ? ? H)).
Qed.

Hints Resolve mult_lt : arith.
V7only [
Notation lt_mult_left := mult_lt.
(* Theorem lt_mult_left :
   (x,y,z:nat) (lt x y) -> (lt (mult (S z) x) (mult (S z) y)).
*)
].

Lemma lt_mult_right :
  (m,n,p:nat) (lt m n) -> (lt (0) p) -> (lt (mult m p) (mult n p)).
Intros m n p H H0.
NewInduction p.
Elim (lt_n_n ? H0).
Rewrite mult_sym.
Replace (mult n (S p)) with (mult (S p) n); Auto with arith.
Qed.

Lemma mult_le_conv_1 : (m,n,p:nat) (le (mult (S m) n) (mult (S m) p)) -> (le n p).
Proof.
  Intros m n p H. Elim (le_or_lt n p). Trivial.
  Intro H0. Cut (lt (mult (S m) n) (mult (S m) n)). Intro. Elim (lt_n_n ? H1).
  Apply le_lt_trans with m:=(mult (S m) p). Assumption.
  Apply mult_lt. Assumption.
Qed.

(** n|->2*n and n|->2n+1 have disjoint image *)

V7only [ (* From Zdivides *) ].
Theorem odd_even_lem:
  (p, q : ?)  ~ (plus (mult (2) p) (1)) = (mult (2) q).
Intros p; Elim p; Auto.
Intros q; Case q; Simpl.
Red; Intros; Discriminate.
Intros q'; Rewrite [x, y : ?]  (plus_sym x (S y)); Simpl; Red; Intros;
 Discriminate.
Intros p' H q; Case q.
Simpl; Red; Intros; Discriminate.
Intros q'; Red; Intros H0; Case (H q').
Replace (mult (S (S O)) q') with (minus (mult (S (S O)) (S q')) (2)).
Rewrite <- H0; Simpl; Auto.
Repeat Rewrite [x, y : ?]  (plus_sym x (S y)); Simpl; Auto.
Simpl; Repeat Rewrite [x, y : ?]  (plus_sym x (S y)); Simpl; Auto.
Case q'; Simpl; Auto.
Qed.


(** Tail-recursive mult *)

(** [tail_mult] is an alternative definition for [mult] which is 
    tail-recursive, whereas [mult] is not. This can be useful 
    when extracting programs. *)

Fixpoint mult_acc [s,m,n:nat] : nat := 
   Cases n of 
      O => s
      | (S p) => (mult_acc (tail_plus m s) m p)
    end.

Lemma mult_acc_aux : (n,s,m:nat)(plus s (mult n m))= (mult_acc s m n).
Proof.
NewInduction n as [|p IHp]; Simpl;Auto.
Intros s m; Rewrite <- plus_tail_plus; Rewrite <- IHp.
Rewrite <- plus_assoc_r; Apply (f_equal2 nat nat);Auto.
Rewrite plus_sym;Auto.
Qed.

Definition tail_mult := [n,m:nat](mult_acc O m n).

Lemma mult_tail_mult : (n,m:nat)(mult n m)=(tail_mult n m).
Proof.
Intros; Unfold tail_mult; Rewrite <- mult_acc_aux;Auto.
Qed.

(** [TailSimpl] transforms any [tail_plus] and [tail_mult] into [plus] 
    and [mult] and simplify *)

Tactic Definition TailSimpl := 
   Repeat Rewrite <- plus_tail_plus; 
   Repeat Rewrite <- mult_tail_mult; 
   Simpl. 
