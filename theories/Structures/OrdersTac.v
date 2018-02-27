(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Setoid Morphisms Basics Equalities Orders.
Set Implicit Arguments.

(** * The order tactic *)

(** This tactic is designed to solve systems of (in)equations
    involving [eq], [lt], [le] and [~eq] on some type. This tactic is
    domain-agnostic; it will only use equivalence+order axioms, and
    not analyze elements of the domain. Hypothesis or goal of the form
    [~lt] or [~le] are initially turned into [le] and [lt], other
    parts of the goal are ignored. This initial preparation of the
    goal is the only moment where totality is used. In particular,
    the core of the tactic only proceeds by saturation of transitivity
    and similar properties, and does not perform case splitting.
    The tactic will fail if it doesn't solve the goal. *)


(** An abstract vision of the predicates. This allows a one-line
    statement for interesting transitivity properties: for instance
    [trans_ord OLE OLE = OLE] will imply later
    [le x y -> le y z -> le x z].
*)

Inductive ord : Set := OEQ | OLT | OLE.
Definition trans_ord o o' :=
 match o, o' with
 | OEQ, _ => o'
 | _, OEQ => o
 | OLE, OLE => OLE
 | _, _ => OLT
 end.
Local Infix "+" := trans_ord.


(** ** The tactic requirements : a total order

   We need :
   - an equivalence [eq],
   - a strict order [lt] total and compatible with [eq],
   - a larger order [le] synonym for [lt\/eq].

   This used to be provided here via a [TotalOrder], but
   for technical reasons related to extraction, we now ask
   for two sperate parts: relations in a [EqLtLe] + properties in
   [IsTotalOrder]. Note that [TotalOrder = EqLtLe <+ IsTotalOrder]
*)

Module Type IsTotalOrder (O:EqLtLe) :=
 IsEq O <+ IsStrOrder O <+ LeIsLtEq O <+ LtIsTotal O.

(** ** Properties that will be used by the [order] tactic *)

Module OrderFacts (Import O:EqLtLe)(P:IsTotalOrder O).
Include EqLtLeNotation O.

(** Reflexivity rules *)

Lemma eq_refl : forall x, x==x.
Proof. reflexivity. Qed.

Lemma le_refl : forall x, x<=x.
Proof. intros; rewrite P.le_lteq; right; reflexivity. Qed.

Lemma lt_irrefl : forall x, ~ x<x.
Proof. intros. apply StrictOrder_Irreflexive. Qed.

(** Symmetry rules *)

Lemma eq_sym : forall x y, x==y -> y==x.
Proof. auto with *. Qed.

Lemma le_antisym : forall x y, x<=y -> y<=x -> x==y.
Proof.
 intros x y; rewrite 2 P.le_lteq. intuition.
 elim (StrictOrder_Irreflexive x); transitivity y; auto.
Qed.

Lemma neq_sym : forall x y, ~x==y -> ~y==x.
Proof. auto using eq_sym. Qed.

(** Transitivity rules : first, a generic formulation, then instances*)

Ltac subst_eqns :=
 match goal with
   | H : _==_ |- _ => (rewrite H || rewrite <- H); clear H; subst_eqns
   | _ => idtac
 end.

Definition interp_ord o :=
 match o with OEQ => O.eq | OLT => O.lt | OLE => O.le end.
Local Notation "#" := interp_ord.

Lemma trans : forall o o' x y z, #o x y -> #o' y z -> #(o+o') x z.
Proof.
destruct o, o'; simpl; intros x y z;
rewrite ?P.le_lteq; intuition auto;
subst_eqns; eauto using (StrictOrder_Transitive x y z) with *.
Qed.

Definition eq_trans x y z : x==y -> y==z -> x==z := @trans OEQ OEQ x y z.
Definition le_trans x y z : x<=y -> y<=z -> x<=z := @trans OLE OLE x y z.
Definition lt_trans x y z : x<y -> y<z -> x<z := @trans OLT OLT x y z.
Definition le_lt_trans x y z : x<=y -> y<z -> x<z := @trans OLE OLT x y z.
Definition lt_le_trans x y z : x<y -> y<=z -> x<z := @trans OLT OLE x y z.
Definition eq_lt x y z : x==y -> y<z -> x<z := @trans OEQ OLT x y z.
Definition lt_eq x y z : x<y -> y==z -> x<z := @trans OLT OEQ x y z.
Definition eq_le x y z : x==y -> y<=z -> x<=z := @trans OEQ OLE x y z.
Definition le_eq x y z : x<=y -> y==z -> x<=z := @trans OLE OEQ x y z.

Lemma eq_neq : forall x y z, x==y -> ~y==z -> ~x==z.
Proof. eauto using eq_trans, eq_sym. Qed.

Lemma neq_eq : forall x y z, ~x==y -> y==z -> ~x==z.
Proof. eauto using eq_trans, eq_sym. Qed.

(** (double) negation rules *)

Lemma not_neq_eq : forall x y, ~~x==y -> x==y.
Proof.
intros x y H. destruct (P.lt_total x y) as [H'|[H'|H']]; auto;
 destruct H; intro H; rewrite H in H'; eapply lt_irrefl; eauto.
Qed.

Lemma not_ge_lt : forall x y, ~y<=x -> x<y.
Proof.
intros x y H. destruct (P.lt_total x y); auto.
destruct H. rewrite P.le_lteq. intuition.
Qed.

Lemma not_gt_le : forall x y, ~y<x -> x<=y.
Proof.
intros x y H. rewrite P.le_lteq. generalize (P.lt_total x y); intuition.
Qed.

Lemma le_neq_lt : forall x y, x<=y -> ~x==y -> x<y.
Proof. auto using not_ge_lt, le_antisym. Qed.

End OrderFacts.



(** ** [MakeOrderTac] : The functor providing the order tactic. *)

Module MakeOrderTac (Import O:EqLtLe)(P:IsTotalOrder O).
Include OrderFacts O P.
Include EqLtLeNotation O.

(** order_eq : replace x by y in all (in)equations hyps thanks
   to equality EQ (where eq has been hidden in order to avoid
   self-rewriting), then discard EQ. *)

Ltac order_rewr x eqn :=
 (* NB: we could use the real rewrite here, but proofs would be uglier. *)
 let rewr H t := generalize t; clear H; intro H
 in
 match goal with
 | H : x == _ |- _ => rewr H (eq_trans (eq_sym eqn) H); order_rewr x eqn
 | H : _ == x |- _ => rewr H (eq_trans H eqn); order_rewr x eqn
 | H : ~x == _ |- _ => rewr H (eq_neq (eq_sym eqn) H); order_rewr x eqn
 | H : ~_ == x |- _ => rewr H (neq_eq H eqn); order_rewr x eqn
 | H : x < _ |- _ => rewr H (eq_lt (eq_sym eqn) H); order_rewr x eqn
 | H : _ < x |- _ => rewr H (lt_eq H eqn); order_rewr x eqn
 | H : x <= _ |- _ => rewr H (eq_le (eq_sym eqn) H); order_rewr x eqn
 | H : _ <= x |- _ => rewr H (le_eq H eqn); order_rewr x eqn
 | _ => clear eqn
end.

Ltac order_eq x y eqn :=
 match x with
 | y => clear eqn
 | _ => change (interp_ord OEQ x y) in eqn; order_rewr x eqn
 end.

(** Goal preparation : We turn all negative hyps into positive ones
  and try to prove False from the inverse of the current goal.
  These steps require totality of our order. After this preparation,
  order only deals with the context, and tries to prove False.
  Hypotheses of the form [A -> False] are also folded in [~A]
  for convenience (i.e. cope with the mess left by intuition). *)

Ltac order_prepare :=
 match goal with
 | H : ?A -> False |- _ => change (~A) in H; order_prepare
 | H : ~(?R ?x ?y) |- _ =>
   match R with
   | eq => fail 1 (* if already using [eq], we leave it this ways *)
   | _ => (change (~x==y) in H ||
           apply not_gt_le in H ||
           apply not_ge_lt in H ||
           clear H || fail 1); order_prepare
   end
 | H : ?R ?x ?y |- _ =>
   match R with
   | eq => fail 1
   | lt => fail 1
   | le => fail 1
   | _ => (change (x==y) in H ||
           change (x<y) in H ||
           change (x<=y) in H ||
           clear H || fail 1); order_prepare
   end
 | |- ~ _ => intro; order_prepare
 | |- _ ?x ?x =>
   exact (eq_refl x) || exact (le_refl x) || exfalso
 | _ =>
   (apply not_neq_eq; intro) ||
   (apply not_ge_lt; intro) ||
   (apply not_gt_le; intro) || exfalso
 end.

(** We now try to prove False from the various [< <= == !=] hypothesis *)

Ltac order_loop :=
 match goal with
 (* First, successful situations *)
 | H : ?x < ?x |- _ => exact (lt_irrefl H)
 | H : ~ ?x == ?x |- _ => exact (H (eq_refl x))
 (* Second, useless hyps *)
 | H : ?x <= ?x |- _ => clear H; order_loop
 (* Third, we eliminate equalities *)
 | H : ?x == ?y |- _ => order_eq x y H; order_loop
 (* Simultaneous le and ge is eq *)
 | H1 : ?x <= ?y, H2 : ?y <= ?x |- _ =>
     generalize (le_antisym H1 H2); clear H1 H2; intro; order_loop
 (* Simultaneous le and ~eq is lt *)
 | H1: ?x <= ?y, H2: ~ ?x == ?y |- _ =>
     generalize (le_neq_lt H1 H2); clear H1 H2; intro; order_loop
 | H1: ?x <= ?y, H2: ~ ?y == ?x |- _ =>
     generalize (le_neq_lt H1 (neq_sym H2)); clear H1 H2; intro; order_loop
 (* Transitivity of lt and le *)
 | H1 : ?x < ?y, H2 : ?y < ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (lt_trans H1 H2); intro; order_loop
    end
 | H1 : ?x <= ?y, H2 : ?y < ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (le_lt_trans H1 H2); intro; order_loop
    end
 | H1 : ?x < ?y, H2 : ?y <= ?z |- _ =>
    match goal with
      | H : x < z |- _ => fail 1
      | _ => generalize (lt_le_trans H1 H2); intro; order_loop
    end
 | H1 : ?x <= ?y, H2 : ?y <= ?z |- _ =>
    match goal with
      | H : x <= z |- _ => fail 1
      | _ => generalize (le_trans H1 H2); intro; order_loop
    end
 | _ => idtac
end.

(** The complete tactic. *)

Ltac order :=
 intros; order_prepare; order_loop; fail "Order tactic unsuccessful".

End MakeOrderTac.

Module OTF_to_OrderTac (OTF:OrderedTypeFull).
 Module TO := OTF_to_TotalOrder OTF.
 Include !MakeOrderTac OTF TO.
End OTF_to_OrderTac.

Module OT_to_OrderTac (OT:OrderedType).
 Module OTF := OT_to_Full OT.
 Include !OTF_to_OrderTac OTF.
End OT_to_OrderTac.
