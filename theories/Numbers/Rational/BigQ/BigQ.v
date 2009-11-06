(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*            Benjamin Gregoire, Laurent Thery, INRIA, 2007             *)
(************************************************************************)

(*i $Id$ i*)

Require Import Field Qfield BigN BigZ QSig QMake.

(** We choose for BigQ an implemention with
    multiple representation of 0: 0, 1/0, 2/0 etc.
    See [QMake.v] *)

(** First, we provide translations functions between [BigN] and [BigZ] *)

Module BigN_BigZ <: NType_ZType BigN.BigN BigZ.
 Definition Z_of_N := BigZ.Pos.
 Lemma spec_Z_of_N : forall n, BigZ.to_Z (Z_of_N n) = BigN.to_Z n.
 Proof.
 reflexivity.
 Qed.
 Definition Zabs_N := BigZ.to_N.
 Lemma spec_Zabs_N : forall z, BigN.to_Z (Zabs_N z) = Zabs (BigZ.to_Z z).
 Proof.
 unfold Zabs_N; intros.
 rewrite BigZ.spec_to_Z, Zmult_comm; apply Zsgn_Zabs.
 Qed.
End BigN_BigZ.

(** This allows to build [BigQ] out of [BigN] and [BigQ] via [QMake] *)

Module BigQ <: QSig.QType := QMake.Make BigN BigZ BigN_BigZ.

(** Notations about [BigQ] *)

Notation bigQ := BigQ.t.

Delimit Scope bigQ_scope with bigQ.
Bind Scope bigQ_scope with bigQ.
Bind Scope bigQ_scope with BigQ.t.

Infix "+" := BigQ.add : bigQ_scope.
Infix "-" := BigQ.sub : bigQ_scope.
Notation "- x" := (BigQ.opp x) : bigQ_scope.
Infix "*" := BigQ.mul : bigQ_scope.
Infix "/" := BigQ.div : bigQ_scope.
Infix "^" := BigQ.power : bigQ_scope.
Infix "?=" := BigQ.compare : bigQ_scope.
Infix "==" := BigQ.eq : bigQ_scope.
Infix "<" := BigQ.lt : bigQ_scope.
Infix "<=" := BigQ.le : bigQ_scope.
Notation "x > y" := (BigQ.lt y x)(only parsing) : bigQ_scope.
Notation "x >= y" := (BigQ.le y x)(only parsing) : bigQ_scope.
Notation "[ q ]" := (BigQ.to_Q q) : bigQ_scope.

Open Scope bigQ_scope.

(** [BigQ] is a setoid *)

Instance BigQeq_rel : Equivalence BigQ.eq.

Instance BigQadd_wd : Proper (BigQ.eq==>BigQ.eq==>BigQ.eq) BigQ.add.
Proof.
 do 3 red. unfold BigQ.eq; intros.
 rewrite !BigQ.spec_add, H, H0. reflexivity.
Qed.

Instance BigQopp_wd : Proper (BigQ.eq==>BigQ.eq) BigQ.opp.
Proof.
 do 2 red. unfold BigQ.eq; intros.
 rewrite !BigQ.spec_opp, H; reflexivity.
Qed.

Instance BigQsub_wd : Proper (BigQ.eq==>BigQ.eq==>BigQ.eq) BigQ.sub.
Proof.
 do 3 red. unfold BigQ.eq; intros.
 rewrite !BigQ.spec_sub, H, H0; reflexivity.
Qed.

Instance BigQmul_wd : Proper (BigQ.eq==>BigQ.eq==>BigQ.eq) BigQ.mul.
Proof.
 do 3 red. unfold BigQ.eq; intros.
 rewrite !BigQ.spec_mul, H, H0; reflexivity.
Qed.

Instance BigQinv_wd : Proper (BigQ.eq==>BigQ.eq) BigQ.inv.
Proof.
 do 2 red; unfold BigQ.eq; intros.
 rewrite !BigQ.spec_inv, H; reflexivity.
Qed.

Instance BigQdiv_wd : Proper (BigQ.eq==>BigQ.eq==>BigQ.eq) BigQ.div.
Proof.
 do 3 red; unfold BigQ.eq; intros.
 rewrite !BigQ.spec_div, H, H0; reflexivity.
Qed.

(* TODO : fix this. For the moment it's useless (horribly slow)
Hint Rewrite
 BigQ.spec_0 BigQ.spec_1 BigQ.spec_m1 BigQ.spec_compare
 BigQ.spec_red BigQ.spec_add BigQ.spec_sub BigQ.spec_opp
 BigQ.spec_mul BigQ.spec_inv BigQ.spec_div BigQ.spec_power_pos
 BigQ.spec_square : bigq. *)


(** [BigQ] is a field *)

Lemma BigQfieldth :
 field_theory BigQ.zero BigQ.one BigQ.add BigQ.mul BigQ.sub BigQ.opp BigQ.div BigQ.inv BigQ.eq.
Proof.
constructor.
constructor; intros; red.
rewrite BigQ.spec_add, BigQ.spec_0; ring.
rewrite ! BigQ.spec_add; ring.
rewrite ! BigQ.spec_add; ring.
rewrite BigQ.spec_mul, BigQ.spec_1; ring.
rewrite ! BigQ.spec_mul; ring.
rewrite ! BigQ.spec_mul; ring.
rewrite BigQ.spec_add, ! BigQ.spec_mul, BigQ.spec_add; ring.
unfold BigQ.sub; apply Qeq_refl.
rewrite BigQ.spec_add, BigQ.spec_0, BigQ.spec_opp; ring.
compute; discriminate.
intros; red.
unfold BigQ.div; apply Qeq_refl.
intros; red.
rewrite BigQ.spec_mul, BigQ.spec_inv, BigQ.spec_1; field.
rewrite <- BigQ.spec_0; auto.
Qed.

Lemma BigQpowerth :
 power_theory BigQ.one BigQ.mul BigQ.eq Z_of_N BigQ.power.
Proof.
constructor.
intros; red.
rewrite BigQ.spec_power.
replace ([r] ^ Z_of_N n)%Q with (pow_N 1 Qmult [r] n)%Q.
destruct n.
simpl; compute; auto.
induction p; simpl; auto; try rewrite !BigQ.spec_mul, !IHp; apply Qeq_refl.
destruct n; reflexivity.
Qed.

Lemma BigQ_eq_bool_correct :
 forall x y, BigQ.eq_bool x y = true -> x==y.
Proof.
intros; generalize (BigQ.spec_eq_bool x y); rewrite H; auto.
Qed.

Lemma BigQ_eq_bool_complete :
 forall x y, x==y -> BigQ.eq_bool x y = true.
Proof.
intros; generalize (BigQ.spec_eq_bool x y).
destruct BigQ.eq_bool; auto.
Qed.

(* TODO : improve later the detection of constants ... *)

Ltac BigQcst t :=
 match t with
   | BigQ.zero => BigQ.zero
   | BigQ.one => BigQ.one
   | BigQ.minus_one => BigQ.minus_one
   | _ => NotConstant
 end.

Add Field BigQfield : BigQfieldth
 (decidable BigQ_eq_bool_correct,
  completeness BigQ_eq_bool_complete,
  constants [BigQcst],
  power_tac BigQpowerth [Qpow_tac]).

Section Examples.

Let ex1 : forall x y z, (x+y)*z ==  (x*z)+(y*z).
  intros.
  ring.
Qed.

Let ex8 : forall x, x ^ 1 == x.
  intro.
  ring.
Qed.

Let ex10 : forall x y, ~(y==BigQ.zero) -> (x/y)*y == x.
intros.
field.
auto.
Qed.

End Examples.