(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Unset Boxed Definitions.

Declare ML Module "z_syntax_plugin".

(** * Binary positive numbers *)

(** Original development by Pierre Crégut, CNET, Lannion, France *)

Inductive positive : Set :=
| xI : positive -> positive
| xO : positive -> positive
| xH : positive.

(** Declare binding key for scope positive_scope *)

Delimit Scope positive_scope with positive.

(** Automatically open scope positive_scope for type positive, xO and xI *)

Bind Scope positive_scope with positive.
Arguments Scope xO [positive_scope].
Arguments Scope xI [positive_scope].

(** Postfix notation for positive numbers, allowing to mimic
    the position of bits in a big-endian representation.
    For instance, we can write 1~1~0 instead of (xO (xI xH))
    for the number 6 (which is 110 in binary notation).
*)

Notation "p ~ 1" := (xI p)
 (at level 7, left associativity, format "p '~' '1'") : positive_scope.
Notation "p ~ 0" := (xO p)
 (at level 7, left associativity, format "p '~' '0'") : positive_scope.

Local Open Scope positive_scope.

(* In the current file, [xH] cannot yet be written as [1], since the
   interpretation of positive numerical constants is not available
   yet. We fix this here with an ad-hoc temporary notation. *)

Local Notation "1" := xH (at level 7).


(** * Operations over positive numbers *)

(** Successor *)

Fixpoint Psucc (x:positive) : positive :=
  match x with
    | p~1 => (Psucc p)~0
    | p~0 => p~1
    | 1 => 1~0
  end.

(** Addition *)

Set Boxed Definitions.

Fixpoint Pplus (x y:positive) : positive :=
  match x, y with
    | p~1, q~1 => (Pplus_carry p q)~0
    | p~1, q~0 => (Pplus p q)~1
    | p~1, 1 => (Psucc p)~0
    | p~0, q~1 => (Pplus p q)~1
    | p~0, q~0 => (Pplus p q)~0
    | p~0, 1 => p~1
    | 1, q~1 => (Psucc q)~0
    | 1, q~0 => q~1
    | 1, 1 => 1~0
  end

with Pplus_carry (x y:positive) : positive :=
  match x, y with
    | p~1, q~1 => (Pplus_carry p q)~1
    | p~1, q~0 => (Pplus_carry p q)~0
    | p~1, 1 => (Psucc p)~1
    | p~0, q~1 => (Pplus_carry p q)~0
    | p~0, q~0 => (Pplus p q)~1
    | p~0, 1 => (Psucc p)~0
    | 1, q~1 => (Psucc q)~1
    | 1, q~0 => (Psucc q)~0
    | 1, 1 => 1~1
  end.

Unset Boxed Definitions.

Infix "+" := Pplus : positive_scope.

Definition Piter_op {A}(op:A->A->A) :=
  fix iter (p:positive)(a:A) : A :=
  match p with
    | 1 => a
    | p~0 => iter p (op a a)
    | p~1 => op a (iter p (op a a))
  end.

Lemma Piter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 Piter_op op (Psucc p) a = op a (Piter_op op p a).
Proof.
 induction p; simpl; intros; trivial.
 rewrite H. apply IHp.
Qed.

(** From binary positive numbers to Peano natural numbers *)

Definition Pmult_nat : positive -> nat -> nat :=
 Eval unfold Piter_op in (* for compatibility *)
 Piter_op plus.

Definition nat_of_P (x:positive) := Pmult_nat x (S O).

(** From Peano natural numbers to binary positive numbers *)

Fixpoint P_of_succ_nat (n:nat) : positive :=
  match n with
    | O => 1
    | S x => Psucc (P_of_succ_nat x)
  end.

(** Operation x -> 2*x-1 *)

Fixpoint Pdouble_minus_one (x:positive) : positive :=
  match x with
    | p~1 => p~0~1
    | p~0 => (Pdouble_minus_one p)~1
    | 1 => 1
  end.

(** Predecessor *)

Definition Ppred (x:positive) :=
  match x with
    | p~1 => p~0
    | p~0 => Pdouble_minus_one p
    | 1 => 1
  end.

(** An auxiliary type for subtraction *)

Inductive positive_mask : Set :=
| IsNul : positive_mask
| IsPos : positive -> positive_mask
| IsNeg : positive_mask.

(** Operation x -> 2*x+1 *)

Definition Pdouble_plus_one_mask (x:positive_mask) :=
  match x with
    | IsNul => IsPos 1
    | IsNeg => IsNeg
    | IsPos p => IsPos p~1
  end.

(** Operation x -> 2*x *)

Definition Pdouble_mask (x:positive_mask) :=
  match x with
    | IsNul => IsNul
    | IsNeg => IsNeg
    | IsPos p => IsPos p~0
  end.

(** Operation x -> 2*x-2 *)

Definition Pdouble_minus_two (x:positive) :=
  match x with
    | p~1 => IsPos p~0~0
    | p~0 => IsPos (Pdouble_minus_one p)~0
    | 1 => IsNul
  end.

(** Subtraction of binary positive numbers into a positive numbers mask *)

Fixpoint Pminus_mask (x y:positive) {struct y} : positive_mask :=
  match x, y with
    | p~1, q~1 => Pdouble_mask (Pminus_mask p q)
    | p~1, q~0 => Pdouble_plus_one_mask (Pminus_mask p q)
    | p~1, 1 => IsPos p~0
    | p~0, q~1 => Pdouble_plus_one_mask (Pminus_mask_carry p q)
    | p~0, q~0 => Pdouble_mask (Pminus_mask p q)
    | p~0, 1 => IsPos (Pdouble_minus_one p)
    | 1, 1 => IsNul
    | 1, _ => IsNeg
  end

with Pminus_mask_carry (x y:positive) {struct y} : positive_mask :=
  match x, y with
    | p~1, q~1 => Pdouble_plus_one_mask (Pminus_mask_carry p q)
    | p~1, q~0 => Pdouble_mask (Pminus_mask p q)
    | p~1, 1 => IsPos (Pdouble_minus_one p)
    | p~0, q~1 => Pdouble_mask (Pminus_mask_carry p q)
    | p~0, q~0 => Pdouble_plus_one_mask (Pminus_mask_carry p q)
    | p~0, 1 => Pdouble_minus_two p
    | 1, _ => IsNeg
  end.

(** Subtraction of binary positive numbers x and y, returns 1 if x<=y *)

Definition Pminus (x y:positive) :=
  match Pminus_mask x y with
    | IsPos z => z
    | _ => 1
  end.

Infix "-" := Pminus : positive_scope.

(** Multiplication on binary positive numbers *)

Fixpoint Pmult (x y:positive) : positive :=
  match x with
    | p~1 => y + (Pmult p y)~0
    | p~0 => (Pmult p y)~0
    | 1 => y
  end.

Infix "*" := Pmult : positive_scope.

(** Iteration over a positive number *)

Fixpoint iter_pos (n:positive) (A:Type) (f:A -> A) (x:A) : A :=
  match n with
    | xH => f x
    | xO n' => iter_pos n' A f (iter_pos n' A f x)
    | xI n' => f (iter_pos n' A f (iter_pos n' A f x))
  end.

(** Power *)

Definition Ppow (x y:positive) := iter_pos y _ (Pmult x) 1.

(** Another possible definition is : Piter_op Pmult y x
    but for some reason, this is quite slower on powers of two. *)

Infix "^" := Ppow : positive_scope.

(** Division by 2 rounded below but for 1 *)

Definition Pdiv2 (z:positive) :=
  match z with
    | 1 => 1
    | p~0 => p
    | p~1 => p
  end.

Infix "/" := Pdiv2 : positive_scope.

(** Number of digits in a positive number *)

Fixpoint Psize (p:positive) : nat :=
  match p with
    | 1 => S O
    | p~1 => S (Psize p)
    | p~0 => S (Psize p)
  end.

(** Same, with positive output *)

Fixpoint Psize_pos (p:positive) : positive :=
  match p with
    | 1 => 1
    | p~1 => Psucc (Psize_pos p)
    | p~0 => Psucc (Psize_pos p)
  end.

(** Comparison on binary positive numbers *)

Fixpoint Pcompare (x y:positive) (r:comparison) {struct y} : comparison :=
  match x, y with
    | p~1, q~1 => Pcompare p q r
    | p~1, q~0 => Pcompare p q Gt
    | p~1, 1 => Gt
    | p~0, q~1 => Pcompare p q Lt
    | p~0, q~0 => Pcompare p q r
    | p~0, 1 => Gt
    | 1, q~1 => Lt
    | 1, q~0 => Lt
    | 1, 1 => r
  end.

Infix "?=" := Pcompare (at level 70, no associativity) : positive_scope.

Definition Plt (x y:positive) := (Pcompare x y Eq) = Lt.
Definition Pgt (x y:positive) := (Pcompare x y Eq) = Gt.
Definition Ple (x y:positive) := (Pcompare x y Eq) <> Gt.
Definition Pge (x y:positive) := (Pcompare x y Eq) <> Lt.

Infix "<=" := Ple : positive_scope.
Infix "<" := Plt : positive_scope.
Infix ">=" := Pge : positive_scope.
Infix ">" := Pgt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.


Definition Pmin (p p' : positive) := match Pcompare p p' Eq with
 | Lt | Eq => p
 | Gt => p'
 end.

Definition Pmax (p p' : positive) := match Pcompare p p' Eq with
 | Lt | Eq => p'
 | Gt => p
 end.

(** Boolean equality *)

Fixpoint Peqb (x y : positive) {struct y} : bool :=
 match x, y with
 | 1, 1 => true
 | p~1, q~1 => Peqb p q
 | p~0, q~0 => Peqb p q
 | _, _ => false
 end.


(** * Properties of operations over positive numbers *)

(** Decidability of equality on binary positive numbers *)

Lemma positive_eq_dec : forall x y: positive, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

(* begin hide *)
Corollary ZL11 : forall p:positive, p = 1 \/ p <> 1.
Proof.
  intro; edestruct positive_eq_dec; eauto.
Qed.
(* end hide *)

(**********************************************************************)
(** Properties of successor on binary positive numbers *)

(** Specification of [xI] in term of [Psucc] and [xO] *)

Lemma xI_succ_xO : forall p:positive, p~1 = Psucc p~0.
Proof.
  reflexivity.
Qed.

Lemma Psucc_discr : forall p:positive, p <> Psucc p.
Proof.
  destruct p; discriminate.
Qed.

(** Successor and double *)

Lemma Psucc_o_double_minus_one_eq_xO :
  forall p:positive, Psucc (Pdouble_minus_one p) = p~0.
Proof.
  induction p; simpl; f_equal; auto.
Qed.

Lemma Pdouble_minus_one_o_succ_eq_xI :
  forall p:positive, Pdouble_minus_one (Psucc p) = p~1.
Proof.
  induction p; simpl; f_equal; auto.
Qed.

Lemma xO_succ_permute :
  forall p:positive, (Psucc p)~0 = Psucc (Psucc p~0).
Proof.
  induction p; simpl; auto.
Qed.

Lemma double_moins_un_xO_discr :
  forall p:positive, Pdouble_minus_one p <> p~0.
Proof.
  destruct p; discriminate.
Qed.

(** Successor and predecessor *)

Lemma Psucc_not_one : forall p:positive, Psucc p <> 1.
Proof.
  destruct p; discriminate.
Qed.

Lemma Ppred_succ : forall p:positive, Ppred (Psucc p) = p.
Proof.
  intros [[p|p| ]|[p|p| ]| ]; simpl; auto.
  f_equal; apply Pdouble_minus_one_o_succ_eq_xI.
Qed.

Lemma Psucc_pred : forall p:positive, p = 1 \/ Psucc (Ppred p) = p.
Proof.
  induction p; simpl; auto.
  right; apply Psucc_o_double_minus_one_eq_xO.
Qed.

Ltac destr_eq H := discriminate H || (try (injection H; clear H; intro H)).

(** Injectivity of successor *)

Lemma Psucc_inj : forall p q:positive, Psucc p = Psucc q -> p = q.
Proof.
  induction p; intros [q|q| ] H; simpl in *; destr_eq H; f_equal; auto.
  elim (Psucc_not_one p); auto.
  elim (Psucc_not_one q); auto.
Qed.

(**********************************************************************)
(** Properties of addition on binary positive numbers *)

(** Specification of [Psucc] in term of [Pplus] *)

Lemma Pplus_one_succ_r : forall p:positive, Psucc p = p + 1.
Proof.
  destruct p; reflexivity.
Qed.

Lemma Pplus_one_succ_l : forall p:positive, Psucc p = 1 + p.
Proof.
  destruct p; reflexivity.
Qed.

(** Specification of [Pplus_carry] *)

Theorem Pplus_carry_spec :
  forall p q:positive, Pplus_carry p q = Psucc (p + q).
Proof.
  induction p; destruct q; simpl; f_equal; auto.
Qed.

(** Commutativity *)

Theorem Pplus_comm : forall p q:positive, p + q = q + p.
Proof.
  induction p; destruct q; simpl; f_equal; auto.
  rewrite 2 Pplus_carry_spec; f_equal; auto.
Qed.

(** Permutation of [Pplus] and [Psucc] *)

Theorem Pplus_succ_permute_r :
  forall p q:positive, p + Psucc q = Psucc (p + q).
Proof.
  induction p; destruct q; simpl; f_equal;
   auto using Pplus_one_succ_r; rewrite Pplus_carry_spec; auto.
Qed.

Theorem Pplus_succ_permute_l :
  forall p q:positive, Psucc p + q = Psucc (p + q).
Proof.
  intros p q; rewrite Pplus_comm, (Pplus_comm p);
    apply Pplus_succ_permute_r.
Qed.

Theorem Pplus_carry_pred_eq_plus :
  forall p q:positive, q <> 1 -> Pplus_carry p (Ppred q) = p + q.
Proof.
  intros p q H; rewrite Pplus_carry_spec, <- Pplus_succ_permute_r; f_equal.
  destruct (Psucc_pred q); [ elim H; assumption | assumption ].
Qed.

(** No neutral for addition on strictly positive numbers *)

Lemma Pplus_no_neutral : forall p q:positive, q + p <> p.
Proof.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] H;
   destr_eq H; apply (IHp q H).
Qed.

Lemma Pplus_carry_no_neutral :
  forall p q:positive, Pplus_carry q p <> Psucc p.
Proof.
  intros p q H; elim (Pplus_no_neutral p q).
  apply Psucc_inj; rewrite <- Pplus_carry_spec; assumption.
Qed.

(** Simplification *)

Lemma Pplus_carry_plus :
  forall p q r s:positive, Pplus_carry p r = Pplus_carry q s -> p + r = q + s.
Proof.
  intros p q r s H; apply Psucc_inj; do 2 rewrite <- Pplus_carry_spec;
    assumption.
Qed.

Lemma Pplus_reg_r : forall p q r:positive, p + r = q + r -> p = q.
Proof.
  intros p q r; revert p q; induction r.
  intros [p|p| ] [q|q| ] H; simpl; destr_eq H;
    f_equal; auto using Pplus_carry_plus;
    contradict H; auto using Pplus_carry_no_neutral.
  intros [p|p| ] [q|q| ] H; simpl; destr_eq H; f_equal; auto;
    contradict H; auto using Pplus_no_neutral.
  intros p q H; apply Psucc_inj; do 2 rewrite Pplus_one_succ_r; assumption.
Qed.

Lemma Pplus_reg_l : forall p q r:positive, p + q = p + r -> q = r.
Proof.
  intros p q r H; apply Pplus_reg_r with (r:=p).
  rewrite (Pplus_comm r), (Pplus_comm q); assumption.
Qed.

Lemma Pplus_carry_reg_r :
  forall p q r:positive, Pplus_carry p r = Pplus_carry q r -> p = q.
Proof.
  intros p q r H; apply Pplus_reg_r with (r:=r); apply Pplus_carry_plus;
    assumption.
Qed.

Lemma Pplus_carry_reg_l :
  forall p q r:positive, Pplus_carry p q = Pplus_carry p r -> q = r.
Proof.
  intros p q r H; apply Pplus_reg_r with (r:=p);
  rewrite (Pplus_comm r), (Pplus_comm q); apply Pplus_carry_plus; assumption.
Qed.

(** Addition on positive is associative *)

Theorem Pplus_assoc : forall p q r:positive, p + (q + r) = p + q + r.
Proof.
  induction p.
  intros [q|q| ] [r|r| ]; simpl; f_equal; auto;
    rewrite ?Pplus_carry_spec, ?Pplus_succ_permute_r,
     ?Pplus_succ_permute_l, ?Pplus_one_succ_r; f_equal; auto.
  intros [q|q| ] [r|r| ]; simpl; f_equal; auto;
    rewrite ?Pplus_carry_spec, ?Pplus_succ_permute_r,
     ?Pplus_succ_permute_l, ?Pplus_one_succ_r; f_equal; auto.
  intros p r; rewrite <- 2 Pplus_one_succ_l, Pplus_succ_permute_l; auto.
Qed.

(** Commutation of addition with the double of a positive number *)

Lemma Pplus_xO : forall m n : positive, (m + n)~0 = m~0 + n~0.
Proof.
  destruct n; destruct m; simpl; auto.
Qed.

Lemma Pplus_xI_double_minus_one :
  forall p q:positive, (p + q)~0 = p~1 + Pdouble_minus_one q.
Proof.
  intros; change (p~1) with (p~0 + 1).
  rewrite <- Pplus_assoc, <- Pplus_one_succ_l, Psucc_o_double_minus_one_eq_xO.
  reflexivity.
Qed.

Lemma Pplus_xO_double_minus_one :
  forall p q:positive, Pdouble_minus_one (p + q) = p~0 + Pdouble_minus_one q.
Proof.
  induction p as [p IHp| p IHp| ]; destruct q; simpl;
  rewrite ?Pplus_carry_spec, ?Pdouble_minus_one_o_succ_eq_xI,
    ?Pplus_xI_double_minus_one; try reflexivity.
  rewrite IHp; auto.
  rewrite <- Psucc_o_double_minus_one_eq_xO, Pplus_one_succ_l; reflexivity.
Qed.

(** Misc *)

Lemma Pplus_diag : forall p:positive, p + p = p~0.
Proof.
  induction p as [p IHp| p IHp| ]; simpl;
   try rewrite ?Pplus_carry_spec, ?IHp; reflexivity.
Qed.

(**********************************************************************)
(** Peano induction and recursion on binary positive positive numbers *)
(** (a nice proof from Conor McBride, see "The view from the left")   *)

Inductive PeanoView : positive -> Type :=
| PeanoOne : PeanoView 1
| PeanoSucc : forall p, PeanoView p -> PeanoView (Psucc p).

Fixpoint peanoView_xO p (q:PeanoView p) : PeanoView (p~0) :=
  match q in PeanoView x return PeanoView (x~0) with
    | PeanoOne => PeanoSucc _ PeanoOne
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xO _ q))
  end.

Fixpoint peanoView_xI p (q:PeanoView p) : PeanoView (p~1) :=
  match q in PeanoView x return PeanoView (x~1) with
    | PeanoOne => PeanoSucc _ (PeanoSucc _ PeanoOne)
    | PeanoSucc _ q => PeanoSucc _ (PeanoSucc _ (peanoView_xI _ q))
  end.

Fixpoint peanoView p : PeanoView p :=
  match p return PeanoView p with
    | 1 => PeanoOne
    | p~0 => peanoView_xO p (peanoView p)
    | p~1 => peanoView_xI p (peanoView p)
  end.

Definition PeanoView_iter (P:positive->Type)
  (a:P 1) (f:forall p, P p -> P (Psucc p)) :=
  (fix iter p (q:PeanoView p) : P p :=
    match q in PeanoView p return P p with
      | PeanoOne => a
      | PeanoSucc _ q => f _ (iter _ q)
    end).

Require Import Eqdep_dec EqdepFacts.

Theorem eq_dep_eq_positive :
  forall (P:positive->Type) (p:positive) (x y:P p),
    eq_dep positive P p x p y -> x = y.
Proof.
  apply eq_dep_eq_dec.
  decide equality.
Qed.

Theorem PeanoViewUnique : forall p (q q':PeanoView p), q = q'.
Proof.
  intros.
  induction q as [ | p q IHq ].
  apply eq_dep_eq_positive.
  cut (1=1). pattern 1 at 1 2 5, q'. destruct q'. trivial.
  destruct p0; intros; discriminate.
  trivial.
  apply eq_dep_eq_positive.
  cut (Psucc p=Psucc p). pattern (Psucc p) at 1 2 5, q'. destruct q'.
  intro. destruct p; discriminate.
  intro. unfold p0 in H. apply Psucc_inj in H.
  generalize q'. rewrite H. intro.
  rewrite (IHq q'0).
  trivial.
  trivial.
Qed.

Definition Prect (P:positive->Type) (a:P 1) (f:forall p, P p -> P (Psucc p))
  (p:positive) :=
  PeanoView_iter P a f p (peanoView p).

Theorem Prect_succ : forall (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (Psucc p)) (p:positive),
  Prect P a f (Psucc p) = f _ (Prect P a f p).
Proof.
  intros.
  unfold Prect.
  rewrite (PeanoViewUnique _ (peanoView (Psucc p)) (PeanoSucc _ (peanoView p))).
  trivial.
Qed.

Theorem Prect_base : forall (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (Psucc p)), Prect P a f 1 = a.
Proof.
  trivial.
Qed.

Definition Prec (P:positive->Set) := Prect P.

(** Peano induction *)

Definition Pind (P:positive->Prop) := Prect P.

(** Peano case analysis *)

Theorem Pcase :
  forall P:positive -> Prop,
    P 1 -> (forall n:positive, P (Psucc n)) -> forall p:positive, P p.
Proof.
  intros; apply Pind; auto.
Qed.

(**********************************************************************)
(** Properties of multiplication on binary positive numbers *)

(** One is right neutral for multiplication *)

Lemma Pmult_1_r : forall p:positive, p * 1 = p.
Proof.
  induction p; simpl; f_equal; auto.
Qed.

(** Successor and multiplication *)

Lemma Pmult_Sn_m : forall n m : positive, (Psucc n) * m = m + n * m.
Proof.
  induction n as [n IHn | n IHn | ]; simpl; intro m.
  rewrite IHn, Pplus_assoc, Pplus_diag, <-Pplus_xO; reflexivity.
  reflexivity.
  symmetry; apply Pplus_diag.
Qed.

(** Right reduction properties for multiplication *)

Lemma Pmult_xO_permute_r : forall p q:positive, p * q~0 = (p * q)~0.
Proof.
  intros p q; induction p; simpl; do 2 (f_equal; auto).
Qed.

Lemma Pmult_xI_permute_r : forall p q:positive, p * q~1 = p + (p * q)~0.
Proof.
  intros p q; induction p as [p IHp|p IHp| ]; simpl; f_equal; auto.
  rewrite IHp, 2 Pplus_assoc, (Pplus_comm p); reflexivity.
Qed.

(** Commutativity of multiplication *)

Theorem Pmult_comm : forall p q:positive, p * q = q * p.
Proof.
  intros p q; induction q as [q IHq|q IHq| ]; simpl; try rewrite <- IHq;
   auto using Pmult_xI_permute_r, Pmult_xO_permute_r, Pmult_1_r.
Qed.

(** Distributivity of multiplication over addition *)

Theorem Pmult_plus_distr_l :
  forall p q r:positive, p * (q + r) = p * q + p * r.
Proof.
  intros p q r; induction p as [p IHp|p IHp| ]; simpl.
  rewrite IHp. set (m:=(p*q)~0). set (n:=(p*r)~0).
  change ((p*q+p*r)~0) with (m+n).
  rewrite 2 Pplus_assoc; f_equal.
  rewrite <- 2 Pplus_assoc; f_equal.
  apply Pplus_comm.
  f_equal; auto.
  reflexivity.
Qed.

Theorem Pmult_plus_distr_r :
  forall p q r:positive, (p + q) * r = p * r + q * r.
Proof.
  intros p q r; do 3 rewrite Pmult_comm with (q:=r); apply Pmult_plus_distr_l.
Qed.

(** Associativity of multiplication *)

Theorem Pmult_assoc : forall p q r:positive, p * (q * r) = p * q * r.
Proof.
  induction p as [p IHp| p IHp | ]; simpl; intros q r.
  rewrite IHp; rewrite Pmult_plus_distr_r; reflexivity.
  rewrite IHp; reflexivity.
  reflexivity.
Qed.

(** Parity properties of multiplication *)

Lemma Pmult_xI_mult_xO_discr : forall p q r:positive, p~1 * r <> q~0 * r.
Proof.
  intros p q r; induction r; try discriminate.
  rewrite 2 Pmult_xO_permute_r; intro H; destr_eq H; auto.
Qed.

Lemma Pmult_xO_discr : forall p q:positive, p~0 * q <> q.
Proof.
  intros p q; induction q; try discriminate.
  rewrite Pmult_xO_permute_r; injection; assumption.
Qed.

(** Simplification properties of multiplication *)

Theorem Pmult_reg_r : forall p q r:positive, p * r = q * r -> p = q.
Proof.
  induction p as [p IHp| p IHp| ]; intros [q|q| ] r H;
    reflexivity || apply (f_equal (A:=positive)) || apply False_ind.
  apply IHp with (r~0); simpl in *;
    rewrite 2 Pmult_xO_permute_r; apply Pplus_reg_l with (1:=H).
  apply Pmult_xI_mult_xO_discr with (1:=H).
  simpl in H; rewrite Pplus_comm in H; apply Pplus_no_neutral with (1:=H).
  symmetry in H; apply Pmult_xI_mult_xO_discr with (1:=H).
  apply IHp with (r~0); simpl; rewrite 2 Pmult_xO_permute_r; assumption.
  apply Pmult_xO_discr with (1:= H).
  simpl in H; symmetry in H; rewrite Pplus_comm in H;
    apply Pplus_no_neutral with (1:=H).
  symmetry in H; apply Pmult_xO_discr with (1:=H).
Qed.

Theorem Pmult_reg_l : forall p q r:positive, r * p = r * q -> p = q.
Proof.
  intros p q r H; apply Pmult_reg_r with (r:=r).
  rewrite (Pmult_comm p), (Pmult_comm q); assumption.
Qed.

(** Inversion of multiplication *)

Lemma Pmult_1_inversion_l : forall p q:positive, p * q = 1 -> p = 1.
Proof.
  intros [p|p| ] [q|q| ] H; destr_eq H; auto.
Qed.

(** Square *)

Lemma Psquare_xO : forall p, p~0 * p~0 = (p*p)~0~0.
Proof.
 intros. simpl. now rewrite Pmult_comm.
Qed.

Lemma Psquare_xI : forall p, p~1 * p~1 = (p*p+p)~0~1.
Proof.
 intros. simpl. rewrite Pmult_comm. simpl. f_equal.
 rewrite Pplus_assoc, Pplus_diag. simpl. now rewrite Pplus_comm.
Qed.

(** Properties of [iter_pos] *)

Lemma iter_pos_swap_gen : forall A B (f:A->B)(g:A->A)(h:B->B),
 (forall a, f (g a) = h (f a)) -> forall p a,
 f (iter_pos p A g a) = iter_pos p B h (f a).
Proof.
 induction p; simpl; intros; now rewrite ?H, ?IHp.
Qed.

Theorem iter_pos_swap :
  forall p (A:Type) (f:A -> A) (x:A),
    iter_pos p A f (f x) = f (iter_pos p A f x).
Proof.
 intros. symmetry. now apply iter_pos_swap_gen.
Qed.

Theorem iter_pos_succ :
  forall p (A:Type) (f:A -> A) (x:A),
    iter_pos (Psucc p) A f x = f (iter_pos p A f x).
Proof.
 induction p as [p IHp|p IHp|]; intros; simpl; trivial.
 now rewrite !IHp, iter_pos_swap.
Qed.

Theorem iter_pos_plus :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter_pos (p+q) A f x = iter_pos p A f (iter_pos q A f x).
Proof.
 induction p using Pind; intros.
 now rewrite <- Pplus_one_succ_l, iter_pos_succ.
 now rewrite Pplus_succ_permute_l, !iter_pos_succ, IHp.
Qed.

Theorem iter_pos_invariant :
  forall (p:positive) (A:Type) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter_pos p A f x).
Proof.
 induction p as [p IHp|p IHp|]; simpl; trivial.
 intros A f Inv H x H0. apply H, IHp, IHp; trivial.
 intros A f Inv H x H0. apply IHp, IHp; trivial.
Qed.

(** Properties of power *)

Lemma Ppow_1_r : forall p, p^1 = p.
Proof.
 intros p. unfold Ppow. simpl. now rewrite Pmult_comm.
Qed.

Lemma Ppow_succ_r : forall p q, p^(Psucc q) = p * p^q.
Proof.
 intros. unfold Ppow. now rewrite iter_pos_succ.
Qed.

(*********************************************************************)
(** Properties of boolean equality *)

Theorem Peqb_refl : forall x:positive, Peqb x x = true.
Proof.
 induction x; auto.
Qed.

Theorem Peqb_true_eq : forall x y:positive, Peqb x y = true -> x=y.
Proof.
 induction x; destruct y; simpl; intros; try discriminate.
 f_equal; auto.
 f_equal; auto.
 reflexivity.
Qed.

Theorem Peqb_eq : forall x y : positive, Peqb x y = true <-> x=y.
Proof.
 split. apply Peqb_true_eq.
 intros; subst; apply Peqb_refl.
Qed.


(**********************************************************************)
(** Properties of comparison on binary positive numbers *)

Theorem Pcompare_refl : forall p:positive, (p ?= p) Eq = Eq.
  induction p; auto.
Qed.

(* A generalization of Pcompare_refl *)

Theorem Pcompare_refl_id : forall (p : positive) (r : comparison), (p ?= p) r = r.
  induction p; auto.
Qed.

Theorem Pcompare_not_Eq :
  forall p q:positive, (p ?= q) Gt <> Eq /\ (p ?= q) Lt <> Eq.
Proof.
  induction p as [p IHp| p IHp| ]; intros [q| q| ]; split; simpl; auto;
    discriminate || (elim (IHp q); auto).
Qed.

Theorem Pcompare_Eq_eq : forall p q:positive, (p ?= q) Eq = Eq -> p = q.
Proof.
  induction p; intros [q| q| ] H; simpl in *; auto;
   try discriminate H; try (f_equal; auto; fail).
  destruct (Pcompare_not_Eq p q) as (H',_); elim H'; auto.
  destruct (Pcompare_not_Eq p q) as (_,H'); elim H'; auto.
Qed.

Lemma Pcompare_eq_iff : forall p q:positive, (p ?= q) Eq = Eq <-> p = q.
Proof.
  split.
  apply Pcompare_Eq_eq.
  intros; subst; apply Pcompare_refl.
Qed.

Lemma Pcompare_Gt_Lt :
  forall p q:positive, (p ?= q) Gt = Lt -> (p ?= q) Eq = Lt.
Proof.
  induction p; intros [q|q| ] H; simpl; auto; discriminate.
Qed.

Lemma Pcompare_eq_Lt :
  forall p q : positive, (p ?= q) Eq = Lt <-> (p ?= q) Gt = Lt.
Proof.
  intros p q; split; [| apply Pcompare_Gt_Lt].
  revert q; induction p; intros [q|q| ] H; simpl; auto; discriminate.
Qed.

Lemma Pcompare_Lt_Gt :
  forall p q:positive, (p ?= q) Lt = Gt -> (p ?= q) Eq = Gt.
Proof.
  induction p; intros [q|q| ] H; simpl; auto; discriminate.
Qed.

Lemma Pcompare_eq_Gt :
  forall p q : positive, (p ?= q) Eq = Gt <-> (p ?= q) Lt = Gt.
Proof.
  intros p q; split; [| apply Pcompare_Lt_Gt].
  revert q; induction p; intros [q|q| ] H; simpl; auto; discriminate.
Qed.

Lemma Pcompare_Lt_Lt :
  forall p q:positive, (p ?= q) Lt = Lt -> (p ?= q) Eq = Lt \/ p = q.
Proof.
  induction p as [p IHp| p IHp| ]; intros [q|q| ] H; simpl in *; auto;
   destruct (IHp q H); subst; auto.
Qed.

Lemma Pcompare_Lt_eq_Lt :
  forall p q:positive, (p ?= q) Lt = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
  intros p q; split; [apply Pcompare_Lt_Lt |].
  intros [H|H]; [|subst; apply Pcompare_refl_id].
  revert q H; induction p; intros [q|q| ] H; simpl in *;
  auto; discriminate.
Qed.

Lemma Pcompare_Gt_Gt :
  forall p q:positive, (p ?= q) Gt = Gt -> (p ?= q) Eq = Gt \/ p = q.
Proof.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] H; simpl in *; auto;
    destruct (IHp q H); subst; auto.
Qed.

Lemma Pcompare_Gt_eq_Gt :
  forall p q:positive, (p ?= q) Gt = Gt <-> (p ?= q) Eq = Gt \/ p = q.
Proof.
  intros p q; split; [apply Pcompare_Gt_Gt |].
  intros [H|H]; [|subst; apply Pcompare_refl_id].
  revert q H; induction p; intros [q|q| ] H; simpl in *;
  auto; discriminate.
Qed.

Lemma Dcompare : forall r:comparison, r = Eq \/ r = Lt \/ r = Gt.
Proof.
  destruct r; auto.
Qed.

Ltac ElimPcompare c1 c2 :=
  elim (Dcompare ((c1 ?= c2) Eq));
    [ idtac | let x := fresh "H" in (intro x; case x; clear x) ].

Lemma Pcompare_antisym :
  forall (p q:positive) (r:comparison),
    CompOpp ((p ?= q) r) = (q ?= p) (CompOpp r).
Proof.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] r; simpl; auto;
   rewrite IHp; auto.
Qed.

Lemma ZC1 : forall p q:positive, (p ?= q) Eq = Gt -> (q ?= p) Eq = Lt.
Proof.
  intros p q H; change Eq with (CompOpp Eq).
  rewrite <- Pcompare_antisym, H; reflexivity.
Qed.

Lemma ZC2 : forall p q:positive, (p ?= q) Eq = Lt -> (q ?= p) Eq = Gt.
Proof.
  intros p q H; change Eq with (CompOpp Eq).
  rewrite <- Pcompare_antisym, H; reflexivity.
Qed.

Lemma ZC3 : forall p q:positive, (p ?= q) Eq = Eq -> (q ?= p) Eq = Eq.
Proof.
  intros p q H; change Eq with (CompOpp Eq).
  rewrite <- Pcompare_antisym, H; reflexivity.
Qed.

Lemma ZC4 : forall p q:positive, (p ?= q) Eq = CompOpp ((q ?= p) Eq).
Proof.
  intros; change Eq at 1 with (CompOpp Eq).
  symmetry; apply Pcompare_antisym.
Qed.

Lemma Pcompare_spec : forall p q, CompSpec eq Plt p q ((p ?= q) Eq).
Proof.
  intros. destruct ((p ?= q) Eq) as [ ]_eqn; constructor.
  apply Pcompare_Eq_eq; auto.
  auto.
  apply ZC1; auto.
Qed.

(** Comparison and the successor *)

Lemma Pcompare_p_Sp : forall p : positive, (p ?= Psucc p) Eq = Lt.
Proof.
  induction p; simpl in *;
    [ elim (Pcompare_eq_Lt p (Psucc p)); auto |
      apply Pcompare_refl_id | reflexivity].
Qed.

Theorem Pcompare_p_Sq : forall p q : positive,
  (p ?= Psucc q) Eq = Lt <-> (p ?= q) Eq = Lt \/ p = q.
Proof.
  intros p q; split.
  (* -> *)
  revert p q; induction p as [p IHp|p IHp| ]; intros [q|q| ] H; simpl in *;
   try (left; reflexivity); try (right; reflexivity).
  destruct (IHp q (Pcompare_Gt_Lt _ _ H)); subst; auto.
  destruct (Pcompare_eq_Lt p q); auto.
  destruct p; discriminate.
  left; destruct (IHp q H);
   [ elim (Pcompare_Lt_eq_Lt p q); auto | subst; apply Pcompare_refl_id].
  destruct (Pcompare_Lt_Lt p q H); subst; auto.
  destruct p; discriminate.
  (* <- *)
  intros [H|H]; [|subst; apply Pcompare_p_Sp].
  revert q H; induction p; intros [q|q| ] H; simpl in *;
   auto; try discriminate.
  destruct (Pcompare_eq_Lt p (Psucc q)); auto.
  apply Pcompare_Gt_Lt; auto.
  destruct (Pcompare_Lt_Lt p q H); subst; auto using Pcompare_p_Sp.
  destruct (Pcompare_Lt_eq_Lt p q); auto.
Qed.

Lemma Pcompare_succ_succ :
 forall n m, (Psucc n ?= Psucc m) Eq = (n ?= m) Eq.
Proof.
 assert (AUX : forall n m, (Psucc n ?= Psucc m) Eq = (n ?= m) Eq ->
          (Psucc n ?= m) Lt = (n ?= m) Gt).
  intros n m IH.
  case_eq ((n ?= m) Gt); intros H.
  elim (proj1 (Pcompare_not_Eq n m) H).
  apply Pcompare_Lt_eq_Lt, Pcompare_p_Sq. rewrite IH.
   now apply Pcompare_Gt_Lt.
  apply Pcompare_eq_Gt, ZC2, Pcompare_p_Sq. apply Pcompare_Gt_Gt in H.
   destruct H; [left; now apply ZC1|now right].
 (* main *)
 induction n; destruct m; simpl; trivial.
 now apply AUX.
 generalize (Psucc_not_one n); destruct (Psucc n); intuition.
 change Gt with (CompOpp Lt); rewrite <- Pcompare_antisym.
 rewrite AUX, Pcompare_antisym; trivial. now rewrite ZC4, IHn, <- ZC4.
 now destruct n.
 apply Pcompare_p_Sq; destruct m; auto.
 now destruct m.
Qed.

(** 1 is the least positive number *)

Lemma Pcompare_1 : forall p, ~ (p ?= 1) Eq = Lt.
Proof.
  destruct p; discriminate.
Qed.

(** Properties of the order on positive numbers *)

Lemma Plt_1 : forall p, ~ p < 1.
Proof.
 exact Pcompare_1.
Qed.

Lemma Plt_1_succ : forall n, 1 < Psucc n.
Proof.
 intros. apply Pcompare_p_Sq. destruct n; auto.
Qed.

Lemma Plt_lt_succ : forall n m : positive, n < m -> n < Psucc m.
Proof.
  unfold Plt; intros n m H; apply <- Pcompare_p_Sq; auto.
Qed.

Lemma Psucc_lt_compat : forall n m, n < m <-> Psucc n < Psucc m.
Proof.
 unfold Plt. intros. rewrite Pcompare_succ_succ. apply iff_refl.
Qed.

Lemma Psucc_le_compat : forall n m, n <= m <-> Psucc n <= Psucc m.
Proof.
 unfold Ple. intros. rewrite Pcompare_succ_succ. apply iff_refl.
Qed.

Lemma Plt_irrefl : forall p : positive, ~ p < p.
Proof.
  unfold Plt; intro p; rewrite Pcompare_refl; discriminate.
Qed.

Lemma Plt_trans : forall n m p : positive, n < m -> m < p -> n < p.
Proof.
  intros n m p; induction p using Pind; intros H H0.
  elim (Plt_1 _ H0).
  apply Plt_lt_succ.
  destruct (Pcompare_p_Sq m p) as (H',_); destruct (H' H0); subst; auto.
Qed.

Theorem Plt_ind : forall (A : positive -> Prop) (n : positive),
  A (Psucc n) ->
    (forall m : positive, n < m -> A m -> A (Psucc m)) ->
      forall m : positive, n < m -> A m.
Proof.
  intros A n AB AS m. induction m using Pind; intros H.
  elim (Plt_1 _ H).
  destruct (Pcompare_p_Sq n m) as (H',_); destruct (H' H); subst; auto.
Qed.

Lemma Ple_lteq : forall p q, p <= q <-> p < q \/ p = q.
Proof.
  unfold Ple, Plt. intros.
  generalize (Pcompare_eq_iff p q).
  destruct ((p ?= q) Eq); intuition; discriminate.
Qed.

Lemma Ple_refl : forall p, p <= p.
Proof.
 intros. unfold Ple. rewrite Pcompare_refl_id. discriminate.
Qed.

Lemma Ple_lt_trans : forall n m p, n <= m -> m < p -> n < p.
Proof.
 intros n m p H H'.
 apply Ple_lteq in H. destruct H.
 now apply Plt_trans with m. now subst.
Qed.

Lemma Plt_le_trans : forall n m p, n < m -> m <= p -> n < p.
Proof.
 intros n m p H H'.
 apply Ple_lteq in H'. destruct H'.
 now apply Plt_trans with m. now subst.
Qed.

Lemma Ple_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
 intros n m p H H'.
 apply Ple_lteq in H. destruct H.
 apply Ple_lteq; left. now apply Plt_le_trans with m.
 now subst.
Qed.

Lemma Plt_succ_r : forall p q, p < Psucc q <-> p <= q.
Proof.
 intros. eapply iff_trans; [eapply Pcompare_p_Sq|eapply iff_sym, Ple_lteq].
Qed.

Lemma Ple_succ_l : forall n m, Psucc n <= m <-> n < m.
Proof.
 intros. apply iff_sym.
 eapply iff_trans; [eapply Psucc_lt_compat|eapply Plt_succ_r].
Qed.

(** Comparison and addition *)

Lemma Pplus_compare_mono_l : forall p q r, (p+q ?= p+r) Eq = (q ?= r) Eq.
Proof.
 induction p using Pind; intros q r.
 rewrite <- 2 Pplus_one_succ_l. apply Pcompare_succ_succ.
 now rewrite 2 Pplus_succ_permute_l, Pcompare_succ_succ.
Qed.

Lemma Pplus_compare_mono_r : forall p q r, (q+p ?= r+p) Eq = (q ?= r) Eq.
Proof.
 intros. rewrite 2 (Pplus_comm _ p). apply Pplus_compare_mono_l.
Qed.

(** Order and addition *)

Lemma Pplus_lt_mono_l : forall p q r, q<r <-> p+q < p+r.
Proof.
 intros. unfold Plt. rewrite Pplus_compare_mono_l. apply iff_refl.
Qed.

Lemma Pplus_lt_mono_r : forall p q r, q<r <-> q+p < r+p.
Proof.
 intros. unfold Plt. rewrite Pplus_compare_mono_r. apply iff_refl.
Qed.

Lemma Pplus_lt_mono : forall p q r s, p<q -> r<s -> p+r<q+s.
Proof.
 intros. apply Plt_trans with (p+s).
 now apply Pplus_lt_mono_l.
 now apply Pplus_lt_mono_r.
Qed.

Lemma Pplus_le_mono_l : forall p q r, q<=r <-> p+q<=p+r.
Proof.
 intros. unfold Ple. rewrite Pplus_compare_mono_l. apply iff_refl.
Qed.

Lemma Pplus_le_mono_r : forall p q r, q<=r <-> q+p<=r+p.
Proof.
 intros. unfold Ple. rewrite Pplus_compare_mono_r. apply iff_refl.
Qed.

Lemma Pplus_le_mono : forall p q r s, p<=q -> r<=s -> p+r <= q+s.
Proof.
 intros. apply Ple_trans with (p+s).
 now apply Pplus_le_mono_l.
 now apply Pplus_le_mono_r.
Qed.

(** Comparison and multiplication *)

Lemma Pmult_compare_mono_l : forall p q r, (p*q ?= p*r) Eq = (q ?= r) Eq.
Proof.
 induction p; simpl; trivial. intros q r. specialize (IHp q r).
 case_eq ((q ?= r) Eq); intros H; rewrite H in IHp.
 apply Pcompare_Eq_eq in H. subst. apply Pcompare_refl.
 now apply Pplus_lt_mono.
 apply ZC2, Pplus_lt_mono; now apply ZC1.
Qed.

Lemma Pmult_compare_mono_r : forall p q r, (q*p ?= r*p) Eq = (q ?= r) Eq.
Proof.
 intros. rewrite 2 (Pmult_comm _ p). apply Pmult_compare_mono_l.
Qed.

(** Order and multiplication *)

Lemma Pmult_lt_mono_l : forall p q r, q<r <-> p*q < p*r.
Proof.
 intros. unfold Plt. rewrite Pmult_compare_mono_l. apply iff_refl.
Qed.

Lemma Pmult_lt_mono_r : forall p q r, q<r <-> q*p < r*p.
Proof.
 intros. unfold Plt. rewrite Pmult_compare_mono_r. apply iff_refl.
Qed.

Lemma Pmult_lt_mono : forall p q r s, p<q -> r<s -> p*r < q*s.
Proof.
 intros. apply Plt_trans with (p*s).
 now apply Pmult_lt_mono_l.
 now apply Pmult_lt_mono_r.
Qed.

Lemma Pmult_le_mono_l : forall p q r, q<=r <-> p*q<=p*r.
Proof.
 intros. unfold Ple. rewrite Pmult_compare_mono_l. apply iff_refl.
Qed.

Lemma Pmult_le_mono_r : forall p q r, q<=r <-> q*p<=r*p.
Proof.
 intros. unfold Ple. rewrite Pmult_compare_mono_r. apply iff_refl.
Qed.

Lemma Pmult_le_mono : forall p q r s, p<=q -> r<=s -> p*r <= q*s.
Proof.
 intros. apply Ple_trans with (p*s).
 now apply Pmult_le_mono_l.
 now apply Pmult_le_mono_r.
Qed.

Lemma Plt_plus_r : forall p q, p < p+q.
Proof.
 induction q using Pind.
 rewrite <- Pplus_one_succ_r. apply Pcompare_p_Sp.
 apply Plt_trans with (p+q); auto.
 apply Pplus_lt_mono_l, Pcompare_p_Sp.
Qed.

Lemma Plt_not_plus_l : forall p q, ~ p+q < p.
Proof.
 intros p q H. elim (Plt_irrefl p).
 apply Plt_trans with (p+q); auto using Plt_plus_r.
Qed.

(**********************************************************************)
(** Properties of subtraction on binary positive numbers *)

Lemma Ppred_minus : forall p, Ppred p = Pminus p 1.
Proof.
  destruct p; auto.
Qed.

Definition Ppred_mask (p : positive_mask) :=
match p with
| IsPos 1 => IsNul
| IsPos q => IsPos (Ppred q)
| IsNul => IsNeg
| IsNeg => IsNeg
end.

Lemma Pminus_mask_succ_r :
  forall p q : positive, Pminus_mask p (Psucc q) = Pminus_mask_carry p q.
Proof.
  induction p ; destruct q; simpl; f_equal; auto; destruct p; auto.
Qed.

Theorem Pminus_mask_carry_spec :
  forall p q : positive, Pminus_mask_carry p q = Ppred_mask (Pminus_mask p q).
Proof.
  induction p as [p IHp|p IHp| ]; destruct q; simpl;
   try reflexivity; try rewrite IHp;
   destruct (Pminus_mask p q) as [|[r|r| ]|] || destruct p; auto.
Qed.

Theorem Pminus_succ_r : forall p q : positive, p - (Psucc q) = Ppred (p - q).
Proof.
  intros p q; unfold Pminus;
  rewrite Pminus_mask_succ_r, Pminus_mask_carry_spec.
  destruct (Pminus_mask p q) as [|[r|r| ]|]; auto.
Qed.

Lemma double_eq_zero_inversion :
  forall p:positive_mask, Pdouble_mask p = IsNul -> p = IsNul.
Proof.
  destruct p; simpl; intros; trivial; discriminate.
Qed.

Lemma double_plus_one_zero_discr :
  forall p:positive_mask, Pdouble_plus_one_mask p <> IsNul.
Proof.
  destruct p; discriminate.
Qed.

Lemma double_plus_one_eq_one_inversion :
  forall p:positive_mask, Pdouble_plus_one_mask p = IsPos 1 -> p = IsNul.
Proof.
  destruct p; simpl; intros; trivial; discriminate.
Qed.

Lemma double_eq_one_discr :
  forall p:positive_mask, Pdouble_mask p <> IsPos 1.
Proof.
  destruct p; discriminate.
Qed.

Theorem Pminus_mask_diag : forall p:positive, Pminus_mask p p = IsNul.
Proof.
  induction p as [p IHp| p IHp| ]; simpl; try rewrite IHp; auto.
Qed.

Lemma Pminus_mask_carry_diag : forall p, Pminus_mask_carry p p = IsNeg.
Proof.
  induction p as [p IHp| p IHp| ]; simpl; try rewrite IHp; auto.
Qed.

Lemma Pminus_mask_IsNeg : forall p q:positive,
 Pminus_mask p q = IsNeg -> Pminus_mask_carry p q = IsNeg.
Proof.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] H; simpl in *; auto;
   try discriminate; unfold Pdouble_mask, Pdouble_plus_one_mask in H;
   specialize IHp with q.
  destruct (Pminus_mask p q); try discriminate; rewrite IHp; auto.
  destruct (Pminus_mask p q); simpl; auto; try discriminate.
  destruct (Pminus_mask_carry p q); simpl; auto; try discriminate.
  destruct (Pminus_mask p q); try discriminate; rewrite IHp; auto.
Qed.

Lemma ZL10 :
  forall p q:positive,
    Pminus_mask p q = IsPos 1 -> Pminus_mask_carry p q = IsNul.
Proof.
  induction p; intros [q|q| ] H; simpl in *; try discriminate.
  elim (double_eq_one_discr _ H).
  rewrite (double_plus_one_eq_one_inversion _ H); auto.
  rewrite (double_plus_one_eq_one_inversion _ H); auto.
  elim (double_eq_one_discr _ H).
  destruct p; simpl; auto; discriminate.
Qed.

(** Properties of subtraction valid only for x>y *)

Lemma Pminus_mask_Gt :
  forall p q:positive,
    (p ?= q) Eq = Gt ->
    exists h : positive,
      Pminus_mask p q = IsPos h /\
      q + h = p /\ (h = 1 \/ Pminus_mask_carry p q = IsPos (Ppred h)).
Proof.
  induction p as [p IHp| p IHp| ]; intros [q| q| ] H; simpl in *;
   try discriminate H.
  (* p~1, q~1 *)
  destruct (IHp q H) as (r & U & V & W); exists (r~0); rewrite ?U, ?V; auto.
  repeat split; auto; right.
  destruct (ZL11 r) as [EQ|NE]; [|destruct W as [|W]; [elim NE; auto|]].
  rewrite ZL10; subst; auto.
  rewrite W; simpl; destruct r; auto; elim NE; auto.
  (* p~1, q~0 *)
  destruct (Pcompare_Gt_Gt _ _ H) as [H'|H']; clear H; rename H' into H.
  destruct (IHp q H) as (r & U & V & W); exists (r~1); rewrite ?U, ?V; auto.
  exists 1; subst; rewrite Pminus_mask_diag; auto.
  (* p~1, 1 *)
  exists (p~0); auto.
  (* p~0, q~1 *)
  destruct (IHp q (Pcompare_Lt_Gt _ _ H)) as (r & U & V & W).
  destruct (ZL11 r) as [EQ|NE]; [|destruct W as [|W]; [elim NE; auto|]].
  exists 1; subst; rewrite ZL10, Pplus_one_succ_r; auto.
  exists ((Ppred r)~1); rewrite W, Pplus_carry_pred_eq_plus, V; auto.
  (* p~0, q~0 *)
  destruct (IHp q H) as (r & U & V & W); exists (r~0); rewrite ?U, ?V; auto.
  repeat split; auto; right.
  destruct (ZL11 r) as [EQ|NE]; [|destruct W as [|W]; [elim NE; auto|]].
  rewrite ZL10; subst; auto.
  rewrite W; simpl; destruct r; auto; elim NE; auto.
  (* p~0, 1 *)
  exists (Pdouble_minus_one p); repeat split; destruct p; simpl; auto.
  rewrite Psucc_o_double_minus_one_eq_xO; auto.
Qed.

Theorem Pplus_minus :
  forall p q:positive, (p ?= q) Eq = Gt -> q+(p-q) = p.
Proof.
  intros p q H; destruct (Pminus_mask_Gt p q H) as (r & U & V & _).
  unfold Pminus; rewrite U; simpl; auto.
Qed.

Theorem Pplus_minus_lt : forall p q, q<p -> q+(p-q) = p.
Proof.
 intros p q H. apply Pplus_minus. apply ZC2, H.
Qed.

Lemma Pplus_minus_eq : forall p q, p+q-q = p.
Proof.
 intros. apply Pplus_reg_l with q.
 rewrite Pplus_minus_lt.
 apply Pplus_comm.
 rewrite Pplus_comm. apply Plt_plus_r.
Qed.

Lemma Pmult_minus_distr_l : forall p q r, r<q -> p*(q-r) = p*q-p*r.
Proof.
 intros p q r H.
 apply Pplus_reg_l with (p*r).
 rewrite <- Pmult_plus_distr_l.
 rewrite Pplus_minus_lt; trivial.
 symmetry. apply Pplus_minus_lt; trivial.
 now apply Pmult_lt_mono_l.
Qed.

Lemma Pminus_lt_mono_l :
 forall p q r, q<p -> p<r -> r-p < r-q.
Proof.
 intros p q r Hqp Hpr.
 apply (Pplus_lt_mono_l p).
 rewrite Pplus_minus_lt by trivial.
 apply Ple_lt_trans with (q+(r-q)).
 rewrite Pplus_minus_lt by (now apply Plt_trans with p).
 apply Ple_refl.
 now apply Pplus_lt_mono_r.
Qed.

Lemma Pminus_compare_mono_l :
 forall p q r, q<p -> r<p -> (p-q ?= p-r) Eq = (r ?= q) Eq.
Proof.
 intros p q r Hqp Hrp.
 case (Pcompare_spec r q); intros H. subst. apply Pcompare_refl.
 apply Pminus_lt_mono_l; trivial.
 apply ZC2, Pminus_lt_mono_l; trivial.
Qed.

Lemma Pminus_compare_mono_r :
 forall p q r, p<q -> p<r -> (q-p ?= r-p) Eq = (q ?= r) Eq.
Proof.
 intros.
 rewrite <- (Pplus_compare_mono_l p), 2 Pplus_minus_lt; trivial.
Qed.

Lemma Pminus_lt_mono_r :
 forall p q r, q<p -> r<q -> q-r < p-r.
Proof.
 intros. unfold Plt. rewrite Pminus_compare_mono_r; trivial.
 now apply Plt_trans with q.
Qed.

Lemma Pminus_decr : forall n m, m<n -> n-m < n.
Proof.
 intros n m LT.
 apply Pplus_lt_mono_l with m.
 rewrite Pplus_minus_lt; trivial.
 rewrite Pplus_comm. apply Plt_plus_r.
Qed.

Lemma Pminus_xI_xI : forall n m, m<n -> n~1 - m~1 = (n-m)~0.
Proof.
 intros. unfold Pminus. simpl.
 destruct (Pminus_mask_Gt n m) as (p & -> & _); trivial.
 now rewrite ZC4, H.
Qed.

Lemma Pplus_minus_assoc : forall p q r, r<q -> p+(q-r) = p+q-r.
Proof.
 intros p q r H.
 apply Pplus_reg_l with r.
 rewrite Pplus_assoc, (Pplus_comm r), <- Pplus_assoc.
 rewrite !Pplus_minus_lt; trivial.
 rewrite Pplus_comm. apply Plt_trans with q; trivial using Plt_plus_r.
Qed.

Lemma Pminus_plus_distr : forall p q r, q+r < p -> p-(q+r) = p-q-r.
Proof.
 intros p q r H.
 assert (q < p)
  by (apply Plt_trans with (q+r); trivial using Plt_plus_r).
 apply Pplus_reg_l with (q+r).
 rewrite Pplus_minus_lt, <- Pplus_assoc, !Pplus_minus_lt; trivial.
 apply (Pplus_lt_mono_l q). rewrite Pplus_minus_lt; trivial.
Qed.

Lemma Pminus_minus_distr : forall p q r, r<q -> q-r < p -> p-(q-r) = p+r-q.
Proof.
 intros p q r H H'.
 apply Pplus_reg_l with (r+(q-r)).
 rewrite <- Pplus_assoc, !Pplus_minus_lt; trivial using Pplus_comm.
 rewrite Pplus_comm, <- (Pplus_minus_lt q r); trivial.
 now apply Pplus_lt_mono_l.
Qed.

(** When x<y, the substraction of x by y returns 1 *)

Lemma Pminus_mask_Lt : forall p q:positive, p<q -> Pminus_mask p q = IsNeg.
Proof.
  unfold Plt; induction p as [p IHp|p IHp| ]; destruct q; simpl; intros;
   try discriminate; try rewrite IHp; auto.
  apply Pcompare_Gt_Lt; auto.
  destruct (Pcompare_Lt_Lt _ _ H).
  rewrite Pminus_mask_IsNeg; simpl; auto.
  subst; rewrite Pminus_mask_carry_diag; auto.
Qed.

Lemma Pminus_Lt : forall p q:positive, p<q -> p-q = 1.
Proof.
  intros; unfold Plt, Pminus; rewrite Pminus_mask_Lt; auto.
Qed.

(** The substraction of x by x returns 1 *)

Lemma Pminus_Eq : forall p:positive, p-p = 1.
Proof.
 intros; unfold Pminus; rewrite Pminus_mask_diag; auto.
Qed.

(** Results concerning [Psize] and [Psize_pos] *)

Lemma Psize_monotone : forall p q, p<q -> (Psize p <= Psize q)%nat.
Proof.
  assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
  assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
  induction p; destruct q; simpl; auto; intros; try discriminate.
  intros; generalize (Pcompare_Gt_Lt _ _ H); auto.
  intros; destruct (Pcompare_Lt_Lt _ _ H); auto; subst; auto.
Qed.

Local Notation "2" := (1~0) : positive_scope.

Lemma Psize_pos_gt : forall p, p < 2^(Psize_pos p).
Proof.
 induction p; simpl; try rewrite Ppow_succ_r; try easy.
 apply Ple_succ_l in IHp. now apply Ple_succ_l.
Qed.

Lemma Psize_pos_le : forall p, 2^(Psize_pos p) <= p~0.
Proof.
 induction p; simpl; try rewrite Ppow_succ_r; try easy.
 apply Pmult_le_mono_l.
 apply Ple_lteq; left. rewrite xI_succ_xO. apply Plt_succ_r, IHp.
Qed.
