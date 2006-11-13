(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id$ *)

Require Export Bool.
Require Export Setoid.

Set Implicit Arguments.

Section Setoid_rings.

Variable A : Type.
Variable Aequiv : A -> A -> Prop.

Infix Local "==" := Aequiv (at level 70, no associativity).

Variable S : Setoid_Theory A Aequiv.

Add Setoid A Aequiv S as Asetoid.

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

Variable plus_morph :
 forall a a0:A, a == a0 -> forall a1 a2:A, a1 == a2 -> a + a1 == a0 + a2.
Variable mult_morph :
  forall a a0:A, a == a0 -> forall a1 a2:A, a1 == a2 -> a * a1 == a0 * a2.
Variable opp_morph : forall a a0:A, a == a0 -> - a == - a0.

Add Morphism Aplus : Aplus_ext.
intros; apply plus_morph; assumption.
Qed.

Add Morphism Amult : Amult_ext.
intros; apply mult_morph; assumption.
Qed.

Add Morphism Aopp : Aopp_ext.
exact opp_morph.
Qed.

Section Theory_of_semi_setoid_rings.

Record Semi_Setoid_Ring_Theory : Prop := 
  {SSR_plus_comm : forall n m:A, n + m == m + n;
   SSR_plus_assoc : forall n m p:A, n + (m + p) == n + m + p;
   SSR_mult_comm : forall n m:A, n * m == m * n;
   SSR_mult_assoc : forall n m p:A, n * (m * p) == n * m * p;
   SSR_plus_zero_left : forall n:A, 0 + n == n;
   SSR_mult_one_left : forall n:A, 1 * n == n;
   SSR_mult_zero_left : forall n:A, 0 * n == 0;
   SSR_distr_left : forall n m p:A, (n + m) * p == n * p + m * p;
   SSR_plus_reg_left : forall n m p:A, n + m == n + p -> m == p;
   SSR_eq_prop : forall x y:A, Is_true (Aeq x y) -> x == y}.

Variable T : Semi_Setoid_Ring_Theory.

Let plus_comm := SSR_plus_comm T.
Let plus_assoc := SSR_plus_assoc T.
Let mult_comm := SSR_mult_comm T.
Let mult_assoc := SSR_mult_assoc T.
Let plus_zero_left := SSR_plus_zero_left T.
Let mult_one_left := SSR_mult_one_left T. 
Let mult_zero_left := SSR_mult_zero_left T.
Let distr_left := SSR_distr_left T.
Let plus_reg_left := SSR_plus_reg_left T.
Let equiv_refl := Seq_refl A Aequiv S.
Let equiv_sym := Seq_sym A Aequiv S.
Let equiv_trans := Seq_trans A Aequiv S.

Hint Resolve plus_comm plus_assoc mult_comm mult_assoc plus_zero_left
  mult_one_left mult_zero_left distr_left plus_reg_left
  equiv_refl (*equiv_sym*).
Hint Immediate equiv_sym.

(* Lemmas whose form is x=y are also provided in form y=x because
  Auto does not symmetry *) 
Lemma SSR_mult_assoc2 : forall n m p:A, n * m * p == n * (m * p).
auto. Qed.

Lemma SSR_plus_assoc2 : forall n m p:A, n + m + p == n + (m + p).
auto. Qed.

Lemma SSR_plus_zero_left2 : forall n:A, n == 0 + n.
auto. Qed.

Lemma SSR_mult_one_left2 : forall n:A, n == 1 * n.
auto. Qed.

Lemma SSR_mult_zero_left2 : forall n:A, 0 == 0 * n.
auto. Qed.

Lemma SSR_distr_left2 : forall n m p:A, n * p + m * p == (n + m) * p.
auto. Qed.

Lemma SSR_plus_permute : forall n m p:A, n + (m + p) == m + (n + p).
intros.
rewrite (plus_assoc n m p).
rewrite (plus_comm n m).
rewrite <- (plus_assoc m n p).
trivial.
Qed.

Lemma SSR_mult_permute : forall n m p:A, n * (m * p) == m * (n * p).
intros.
rewrite (mult_assoc n m p).
rewrite (mult_comm n m).
rewrite <- (mult_assoc m n p).
trivial.
Qed.

Hint Resolve SSR_plus_permute SSR_mult_permute.

Lemma SSR_distr_right : forall n m p:A, n * (m + p) == n * m + n * p.
intros.
rewrite (mult_comm n (m + p)).
rewrite (mult_comm n m).
rewrite (mult_comm n p).
auto.
Qed.

Lemma SSR_distr_right2 : forall n m p:A, n * m + n * p == n * (m + p).
intros.
apply equiv_sym.
apply SSR_distr_right.
Qed.

Lemma SSR_mult_zero_right : forall n:A, n * 0 == 0.
intro; rewrite (mult_comm n 0); auto.
Qed.

Lemma SSR_mult_zero_right2 : forall n:A, 0 == n * 0.
intro; rewrite (mult_comm n 0); auto.
Qed.

Lemma SSR_plus_zero_right : forall n:A, n + 0 == n.
intro; rewrite (plus_comm n 0); auto.
Qed.

Lemma SSR_plus_zero_right2 : forall n:A, n == n + 0.
intro; rewrite (plus_comm n 0); auto.
Qed.

Lemma SSR_mult_one_right : forall n:A, n * 1 == n.
intro; rewrite (mult_comm n 1); auto.
Qed.

Lemma SSR_mult_one_right2 : forall n:A, n == n * 1.
intro; rewrite (mult_comm n 1); auto.
Qed.

Lemma SSR_plus_reg_right : forall n m p:A, m + n == p + n -> m == p.
intros n m p; rewrite (plus_comm m n); rewrite (plus_comm p n).
intro; apply plus_reg_left with n; trivial.
Qed.

End Theory_of_semi_setoid_rings.

Section Theory_of_setoid_rings.

Record Setoid_Ring_Theory : Prop := 
  {STh_plus_comm : forall n m:A, n + m == m + n;
   STh_plus_assoc : forall n m p:A, n + (m + p) == n + m + p;
   STh_mult_comm : forall n m:A, n * m == m * n;
   STh_mult_assoc : forall n m p:A, n * (m * p) == n * m * p;
   STh_plus_zero_left : forall n:A, 0 + n == n;
   STh_mult_one_left : forall n:A, 1 * n == n;
   STh_opp_def : forall n:A, n + - n == 0;
   STh_distr_left : forall n m p:A, (n + m) * p == n * p + m * p;
   STh_eq_prop : forall x y:A, Is_true (Aeq x y) -> x == y}.

Variable T : Setoid_Ring_Theory.

Let plus_comm := STh_plus_comm T.
Let plus_assoc := STh_plus_assoc T.
Let mult_comm := STh_mult_comm T.
Let mult_assoc := STh_mult_assoc T.
Let plus_zero_left := STh_plus_zero_left T.
Let mult_one_left := STh_mult_one_left T. 
Let opp_def := STh_opp_def T.
Let distr_left := STh_distr_left T.
Let equiv_refl := Seq_refl A Aequiv S.
Let equiv_sym := Seq_sym A Aequiv S.
Let equiv_trans := Seq_trans A Aequiv S.

Hint Resolve plus_comm plus_assoc mult_comm mult_assoc plus_zero_left
  mult_one_left opp_def distr_left equiv_refl equiv_sym.

(* Lemmas whose form is x=y are also provided in form y=x because Auto does
  not symmetry *)

Lemma STh_mult_assoc2 : forall n m p:A, n * m * p == n * (m * p).
auto. Qed.

Lemma STh_plus_assoc2 : forall n m p:A, n + m + p == n + (m + p).
auto. Qed.

Lemma STh_plus_zero_left2 : forall n:A, n == 0 + n.
auto. Qed.

Lemma STh_mult_one_left2 : forall n:A, n == 1 * n.
auto. Qed.

Lemma STh_distr_left2 : forall n m p:A, n * p + m * p == (n + m) * p.
auto. Qed.

Lemma STh_opp_def2 : forall n:A, 0 == n + - n.
auto. Qed.

Lemma STh_plus_permute : forall n m p:A, n + (m + p) == m + (n + p).
intros.
rewrite (plus_assoc n m p).
rewrite (plus_comm n m).
rewrite <- (plus_assoc m n p).
trivial.
Qed.

Lemma STh_mult_permute : forall n m p:A, n * (m * p) == m * (n * p).
intros.
rewrite (mult_assoc n m p).
rewrite (mult_comm n m).
rewrite <- (mult_assoc m n p).
trivial.
Qed.

Hint Resolve STh_plus_permute STh_mult_permute.

Lemma Saux1 : forall a:A, a + a == a -> a == 0.
intros.
rewrite <- (plus_zero_left a).
rewrite (plus_comm 0 a).
setoid_replace (a + 0) with (a + (a + - a)); auto.
rewrite (plus_assoc a a (- a)).
rewrite H.
apply opp_def.
Qed.

Lemma STh_mult_zero_left : forall n:A, 0 * n == 0.
intros.
apply Saux1.
rewrite <- (distr_left 0 0 n).
rewrite (plus_zero_left 0).
trivial.
Qed.
Hint Resolve STh_mult_zero_left.

Lemma STh_mult_zero_left2 : forall n:A, 0 == 0 * n.
auto.
Qed.

Lemma Saux2 : forall x y z:A, x + y == 0 -> x + z == 0 -> y == z.
intros.
rewrite <- (plus_zero_left y).
rewrite <- H0.
rewrite <- (plus_assoc x z y).
rewrite (plus_comm z y).
rewrite (plus_assoc x y z).
rewrite H.
auto.
Qed.

Lemma STh_opp_mult_left : forall x y:A, - (x * y) == - x * y.
intros.
apply Saux2 with (x * y); auto.
rewrite <- (distr_left x (- x) y).
rewrite (opp_def x).
auto.
Qed.
Hint Resolve STh_opp_mult_left.

Lemma STh_opp_mult_left2 : forall x y:A, - x * y == - (x * y).
auto.
Qed.

Lemma STh_mult_zero_right : forall n:A, n * 0 == 0.
intro; rewrite (mult_comm n 0); auto.
Qed.

Lemma STh_mult_zero_right2 : forall n:A, 0 == n * 0.
intro; rewrite (mult_comm n 0); auto.
Qed.

Lemma STh_plus_zero_right : forall n:A, n + 0 == n.
intro; rewrite (plus_comm n 0); auto.
Qed.

Lemma STh_plus_zero_right2 : forall n:A, n == n + 0.
intro; rewrite (plus_comm n 0); auto.
Qed.

Lemma STh_mult_one_right : forall n:A, n * 1 == n.
intro; rewrite (mult_comm n 1); auto.
Qed.

Lemma STh_mult_one_right2 : forall n:A, n == n * 1.
intro; rewrite (mult_comm n 1); auto.
Qed.

Lemma STh_opp_mult_right : forall x y:A, - (x * y) == x * - y.
intros.
rewrite (mult_comm x y).
rewrite (mult_comm x (- y)).
auto.
Qed.

Lemma STh_opp_mult_right2 : forall x y:A, x * - y == - (x * y).
intros.
rewrite (mult_comm x y).
rewrite (mult_comm x (- y)).
auto.
Qed.

Lemma STh_plus_opp_opp : forall x y:A, - x + - y == - (x + y).
intros.
apply Saux2 with (x + y); auto.
rewrite (STh_plus_permute (x + y) (- x) (- y)).
rewrite <- (plus_assoc x y (- y)).
rewrite (opp_def y); rewrite (STh_plus_zero_right x).
rewrite (STh_opp_def2 x); trivial.
Qed.

Lemma STh_plus_permute_opp : forall n m p:A, - m + (n + p) == n + (- m + p).
auto.
Qed.

Lemma STh_opp_opp : forall n:A, - - n == n.
intro.
apply Saux2 with (- n); auto.
rewrite (plus_comm (- n) n); auto.
Qed.
Hint Resolve STh_opp_opp.

Lemma STh_opp_opp2 : forall n:A, n == - - n.
auto.
Qed.

Lemma STh_mult_opp_opp : forall x y:A, - x * - y == x * y.
intros.
rewrite (STh_opp_mult_left2 x (- y)).
rewrite (STh_opp_mult_right2 x y).
trivial.
Qed.

Lemma STh_mult_opp_opp2 : forall x y:A, x * y == - x * - y.
intros.
apply equiv_sym.
apply STh_mult_opp_opp.
Qed.

Lemma STh_opp_zero : - 0 == 0.
rewrite <- (plus_zero_left (- 0)).
trivial.
Qed.

Lemma STh_plus_reg_left : forall n m p:A, n + m == n + p -> m == p.
intros.
rewrite <- (plus_zero_left m).
rewrite <- (plus_zero_left p).
rewrite <- (opp_def n).
rewrite (plus_comm n (- n)).
rewrite <- (plus_assoc (- n) n m).
rewrite <- (plus_assoc (- n) n p).
auto.
Qed.

Lemma STh_plus_reg_right : forall n m p:A, m + n == p + n -> m == p.
intros.
apply STh_plus_reg_left with n.
rewrite (plus_comm n m); rewrite (plus_comm n p); assumption.
Qed.

Lemma STh_distr_right : forall n m p:A, n * (m + p) == n * m + n * p.
intros.
rewrite (mult_comm n (m + p)).
rewrite (mult_comm n m).
rewrite (mult_comm n p).
trivial.
Qed.

Lemma STh_distr_right2 : forall n m p:A, n * m + n * p == n * (m + p).
intros.
apply equiv_sym.
apply STh_distr_right.
Qed.

End Theory_of_setoid_rings.

Hint Resolve STh_mult_zero_left STh_plus_reg_left: core.

Unset Implicit Arguments.

Definition Semi_Setoid_Ring_Theory_of :
  Setoid_Ring_Theory -> Semi_Setoid_Ring_Theory.
intros until 1; case H.
split; intros; simpl in |- *; eauto.
Defined.

Coercion Semi_Setoid_Ring_Theory_of : Setoid_Ring_Theory >->
 Semi_Setoid_Ring_Theory.



Section product_ring.

End product_ring.

Section power_ring.

End power_ring.

End Setoid_rings.
