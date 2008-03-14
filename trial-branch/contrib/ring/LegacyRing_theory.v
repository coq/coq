(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Bool.

Set Implicit Arguments.

Section Theory_of_semi_rings.

Variable A : Type.
Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
(* There is also a "weakly decidable" equality on A. That means 
  that if (A_eq x y)=true then x=y but x=y can arise when 
  (A_eq x y)=false. On an abstract ring the function [x,y:A]false
  is a good choice. The proof of A_eq_prop is in this case easy. *)
Variable Aeq : A -> A -> bool.

Infix "+" := Aplus (at level 50, left associativity).
Infix "*" := Amult (at level 40, left associativity).
Notation "0" := Azero.
Notation "1" := Aone.

Record Semi_Ring_Theory : Prop := 
  {SR_plus_comm : forall n m:A, n + m = m + n;
   SR_plus_assoc : forall n m p:A, n + (m + p) = n + m + p;
   SR_mult_comm : forall n m:A, n * m = m * n;
   SR_mult_assoc : forall n m p:A, n * (m * p) = n * m * p;
   SR_plus_zero_left : forall n:A, 0 + n = n;
   SR_mult_one_left : forall n:A, 1 * n = n;
   SR_mult_zero_left : forall n:A, 0 * n = 0;
   SR_distr_left : forall n m p:A, (n + m) * p = n * p + m * p;
(*   SR_plus_reg_left : forall n m p:A, n + m = n + p -> m = p;*)
   SR_eq_prop : forall x y:A, Is_true (Aeq x y) -> x = y}.

Variable T : Semi_Ring_Theory.

Let plus_comm := SR_plus_comm T.
Let plus_assoc := SR_plus_assoc T.
Let mult_comm := SR_mult_comm T.
Let mult_assoc := SR_mult_assoc T.
Let plus_zero_left := SR_plus_zero_left T.
Let mult_one_left := SR_mult_one_left T. 
Let mult_zero_left := SR_mult_zero_left T.
Let distr_left := SR_distr_left T.
(*Let plus_reg_left := SR_plus_reg_left T.*)

Hint Resolve plus_comm plus_assoc mult_comm mult_assoc plus_zero_left
  mult_one_left mult_zero_left distr_left (*plus_reg_left*).

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *) 
Lemma SR_mult_assoc2 : forall n m p:A, n * m * p = n * (m * p).
symmetry  in |- *; eauto. Qed.

Lemma SR_plus_assoc2 : forall n m p:A, n + m + p = n + (m + p).
symmetry  in |- *; eauto. Qed.

Lemma SR_plus_zero_left2 : forall n:A, n = 0 + n.
symmetry  in |- *; eauto. Qed.

Lemma SR_mult_one_left2 : forall n:A, n = 1 * n.
symmetry  in |- *; eauto. Qed.

Lemma SR_mult_zero_left2 : forall n:A, 0 = 0 * n.
symmetry  in |- *; eauto. Qed.

Lemma SR_distr_left2 : forall n m p:A, n * p + m * p = (n + m) * p.
symmetry  in |- *; eauto. Qed.

Lemma SR_plus_permute : forall n m p:A, n + (m + p) = m + (n + p).
intros.
rewrite plus_assoc.
elim (plus_comm m n).
rewrite <- plus_assoc.
reflexivity.
Qed.

Lemma SR_mult_permute : forall n m p:A, n * (m * p) = m * (n * p).
intros.
rewrite mult_assoc.
elim (mult_comm m n).
rewrite <- mult_assoc.
reflexivity.
Qed.

Hint Resolve SR_plus_permute SR_mult_permute.

Lemma SR_distr_right : forall n m p:A, n * (m + p) = n * m + n * p.
intros.
repeat rewrite (mult_comm n).
eauto.
Qed.

Lemma SR_distr_right2 : forall n m p:A, n * m + n * p = n * (m + p).
symmetry  in |- *; apply SR_distr_right. Qed.

Lemma SR_mult_zero_right : forall n:A, n * 0 = 0.
intro; rewrite mult_comm; eauto.
Qed.

Lemma SR_mult_zero_right2 : forall n:A, 0 = n * 0.
intro; rewrite mult_comm; eauto.
Qed.

Lemma SR_plus_zero_right : forall n:A, n + 0 = n.
intro; rewrite plus_comm; eauto.
Qed.
Lemma SR_plus_zero_right2 : forall n:A, n = n + 0.
intro; rewrite plus_comm; eauto.
Qed.

Lemma SR_mult_one_right : forall n:A, n * 1 = n.
intro; elim mult_comm; auto.
Qed.

Lemma SR_mult_one_right2 : forall n:A, n = n * 1.
intro; elim mult_comm; auto.
Qed.
(*
Lemma SR_plus_reg_right : forall n m p:A, m + n = p + n -> m = p.
intros n m p; rewrite (plus_comm m n); rewrite (plus_comm p n); eauto.
Qed.
*)
End Theory_of_semi_rings.

Section Theory_of_rings.

Variable A : Type.

Variable Aplus : A -> A -> A.
Variable Amult : A -> A -> A.
Variable Aone : A.
Variable Azero : A.
Variable Aopp : A -> A.
Variable Aeq : A -> A -> bool.

Infix "+" := Aplus (at level 50, left associativity).
Infix "*" := Amult (at level 40, left associativity).
Notation "0" := Azero.
Notation "1" := Aone.
Notation "- x" := (Aopp x).

Record Ring_Theory : Prop := 
  {Th_plus_comm : forall n m:A, n + m = m + n;
   Th_plus_assoc : forall n m p:A, n + (m + p) = n + m + p;
   Th_mult_comm : forall n m:A, n * m = m * n;
   Th_mult_assoc : forall n m p:A, n * (m * p) = n * m * p;
   Th_plus_zero_left : forall n:A, 0 + n = n;
   Th_mult_one_left : forall n:A, 1 * n = n;
   Th_opp_def : forall n:A, n + - n = 0;
   Th_distr_left : forall n m p:A, (n + m) * p = n * p + m * p;
   Th_eq_prop : forall x y:A, Is_true (Aeq x y) -> x = y}.

Variable T : Ring_Theory.

Let plus_comm := Th_plus_comm T.
Let plus_assoc := Th_plus_assoc T.
Let mult_comm := Th_mult_comm T.
Let mult_assoc := Th_mult_assoc T.
Let plus_zero_left := Th_plus_zero_left T.
Let mult_one_left := Th_mult_one_left T. 
Let opp_def := Th_opp_def T.
Let distr_left := Th_distr_left T.

Hint Resolve plus_comm plus_assoc mult_comm mult_assoc plus_zero_left
  mult_one_left opp_def distr_left.

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *) 
Lemma Th_mult_assoc2 : forall n m p:A, n * m * p = n * (m * p).
symmetry  in |- *; eauto. Qed.

Lemma Th_plus_assoc2 : forall n m p:A, n + m + p = n + (m + p).
symmetry  in |- *; eauto. Qed.

Lemma Th_plus_zero_left2 : forall n:A, n = 0 + n.
symmetry  in |- *; eauto. Qed.

Lemma Th_mult_one_left2 : forall n:A, n = 1 * n.
symmetry  in |- *; eauto. Qed.

Lemma Th_distr_left2 : forall n m p:A, n * p + m * p = (n + m) * p.
symmetry  in |- *; eauto. Qed.

Lemma Th_opp_def2 : forall n:A, 0 = n + - n.
symmetry  in |- *; eauto. Qed.

Lemma Th_plus_permute : forall n m p:A, n + (m + p) = m + (n + p).
intros.
rewrite plus_assoc.
elim (plus_comm m n).
rewrite <- plus_assoc.
reflexivity.
Qed.

Lemma Th_mult_permute : forall n m p:A, n * (m * p) = m * (n * p).
intros.
rewrite mult_assoc.
elim (mult_comm m n).
rewrite <- mult_assoc.
reflexivity.
Qed.

Hint Resolve Th_plus_permute Th_mult_permute.

Lemma aux1 : forall a:A, a + a = a -> a = 0.
intros.
generalize (opp_def a).
pattern a at 1 in |- *.
rewrite <- H.
rewrite <- plus_assoc.
rewrite opp_def.
elim plus_comm.
rewrite plus_zero_left.
trivial.
Qed.

Lemma Th_mult_zero_left : forall n:A, 0 * n = 0.
intros.
apply aux1.
rewrite <- distr_left.
rewrite plus_zero_left.
reflexivity.
Qed.
Hint Resolve Th_mult_zero_left.

Lemma Th_mult_zero_left2 : forall n:A, 0 = 0 * n.
symmetry  in |- *; eauto. Qed.

Lemma aux2 : forall x y z:A, x + y = 0 -> x + z = 0 -> y = z.
intros.
rewrite <- (plus_zero_left y).
elim H0.
elim plus_assoc.
elim (plus_comm y z).
rewrite plus_assoc.
rewrite H.
rewrite plus_zero_left.
reflexivity.
Qed.

Lemma Th_opp_mult_left : forall x y:A, - (x * y) = - x * y.
intros.
apply (aux2 (x:=(x * y)));
 [ apply opp_def | rewrite <- distr_left; rewrite opp_def; auto ].
Qed.
Hint Resolve Th_opp_mult_left.

Lemma Th_opp_mult_left2 : forall x y:A, - x * y = - (x * y).
symmetry  in |- *; eauto. Qed.

Lemma Th_mult_zero_right : forall n:A, n * 0 = 0.
intro; elim mult_comm; eauto.
Qed.

Lemma Th_mult_zero_right2 : forall n:A, 0 = n * 0.
intro; elim mult_comm; eauto.
Qed.

Lemma Th_plus_zero_right : forall n:A, n + 0 = n.
intro; rewrite plus_comm; eauto.
Qed.

Lemma Th_plus_zero_right2 : forall n:A, n = n + 0.
intro; rewrite plus_comm; eauto.
Qed.

Lemma Th_mult_one_right : forall n:A, n * 1 = n.
intro; elim mult_comm; eauto.
Qed.

Lemma Th_mult_one_right2 : forall n:A, n = n * 1.
intro; elim mult_comm; eauto.
Qed.

Lemma Th_opp_mult_right : forall x y:A, - (x * y) = x * - y.
intros; do 2 rewrite (mult_comm x); auto.
Qed.

Lemma Th_opp_mult_right2 : forall x y:A, x * - y = - (x * y).
intros; do 2 rewrite (mult_comm x); auto.
Qed.

Lemma Th_plus_opp_opp : forall x y:A, - x + - y = - (x + y).
intros.
apply (aux2 (x:=(x + y)));
 [ elim plus_assoc; rewrite (Th_plus_permute y (- x)); rewrite plus_assoc;
    rewrite opp_def; rewrite plus_zero_left; auto
 | auto ].
Qed.

Lemma Th_plus_permute_opp : forall n m p:A, - m + (n + p) = n + (- m + p).
eauto. Qed.

Lemma Th_opp_opp : forall n:A, - - n = n.
intro; apply (aux2 (x:=(- n))); [ auto | elim plus_comm; auto ].
Qed.
Hint Resolve Th_opp_opp.

Lemma Th_opp_opp2 : forall n:A, n = - - n.
symmetry  in |- *; eauto. Qed.

Lemma Th_mult_opp_opp : forall x y:A, - x * - y = x * y.
intros; rewrite <- Th_opp_mult_left; rewrite <- Th_opp_mult_right; auto.
Qed.

Lemma Th_mult_opp_opp2 : forall x y:A, x * y = - x * - y.
symmetry  in |- *; apply Th_mult_opp_opp. Qed.

Lemma Th_opp_zero : - 0 = 0.
rewrite <- (plus_zero_left (- 0)).
auto. Qed.
(*
Lemma Th_plus_reg_left : forall n m p:A, n + m = n + p -> m = p.
intros; generalize (f_equal (fun z => - n + z) H).
repeat rewrite plus_assoc.
rewrite (plus_comm (- n) n).
rewrite opp_def.
repeat rewrite Th_plus_zero_left; eauto.
Qed.

Lemma Th_plus_reg_right : forall n m p:A, m + n = p + n -> m = p.
intros.
eapply Th_plus_reg_left with n. 
rewrite (plus_comm n m).
rewrite (plus_comm n p).
auto.
Qed.
*)
Lemma Th_distr_right : forall n m p:A, n * (m + p) = n * m + n * p.
intros.
repeat rewrite (mult_comm n).
eauto.
Qed.

Lemma Th_distr_right2 : forall n m p:A, n * m + n * p = n * (m + p).
symmetry  in |- *; apply Th_distr_right.
Qed.

End Theory_of_rings.

Hint Resolve Th_mult_zero_left (*Th_plus_reg_left*): core.

Unset Implicit Arguments.

Definition Semi_Ring_Theory_of :
  forall (A:Type) (Aplus Amult:A -> A -> A) (Aone Azero:A) 
    (Aopp:A -> A) (Aeq:A -> A -> bool),
    Ring_Theory Aplus Amult Aone Azero Aopp Aeq ->
    Semi_Ring_Theory Aplus Amult Aone Azero Aeq.
intros until 1; case H.
split; intros; simpl in |- *; eauto.
Defined.

(* Every ring can be viewed as a semi-ring : this property will be used
  in Abstract_polynom. *)
Coercion Semi_Ring_Theory_of : Ring_Theory >-> Semi_Ring_Theory.


Section product_ring.

End product_ring.

Section power_ring.

End power_ring.
