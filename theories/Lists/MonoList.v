(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** THIS IS A OLD CONTRIB. IT IS NO LONGER MAINTAINED ***)

Require Import Le.

Parameter List_Dom : Set.
Definition A := List_Dom.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Fixpoint app (l m:list) {struct l} : list :=
  match l return list with
  | nil => m
  | cons a l1 => cons a (app l1 m)
  end.


Lemma app_nil_end : forall l:list, l = app l nil.
Proof. 
	intro l; elim l; simpl in |- *; auto.
        simple induction 1; auto.
Qed.
Hint Resolve app_nil_end: list v62.

Lemma app_ass : forall l m n:list, app (app l m) n = app l (app m n).
Proof. 
	intros l m n; elim l; simpl in |- *; auto with list.
	simple induction 1; auto with list.
Qed.
Hint Resolve app_ass: list v62.

Lemma ass_app : forall l m n:list, app l (app m n) = app (app l m) n.
Proof. 
	auto with list.
Qed.
Hint Resolve ass_app: list v62.

Definition tail (l:list) : list :=
  match l return list with
  | cons _ m => m
  | _ => nil
  end.
                   

Lemma nil_cons : forall (a:A) (m:list), nil <> cons a m.
  intros; discriminate.
Qed.

(****************************************)
(* Length of lists                      *)
(****************************************)

Fixpoint length (l:list) : nat :=
  match l return nat with
  | cons _ m => S (length m)
  | _ => 0
  end.

(******************************)
(* Length order of lists      *)
(******************************)

Section length_order.
Definition lel (l m:list) := length l <= length m.

Hint Unfold lel: list.

Variables a b : A.
Variables l m n : list.

Lemma lel_refl : lel l l.
Proof. 
	unfold lel in |- *; auto with list.
Qed.

Lemma lel_trans : lel l m -> lel m n -> lel l n.
Proof. 
	unfold lel in |- *; intros.
        apply le_trans with (length m); auto with list.
Qed.

Lemma lel_cons_cons : lel l m -> lel (cons a l) (cons b m).
Proof. 
	unfold lel in |- *; simpl in |- *; auto with list arith.
Qed.

Lemma lel_cons : lel l m -> lel l (cons b m).
Proof. 
	unfold lel in |- *; simpl in |- *; auto with list arith.
Qed.

Lemma lel_tail : lel (cons a l) (cons b m) -> lel l m.
Proof. 
	unfold lel in |- *; simpl in |- *; auto with list arith.
Qed.

Lemma lel_nil : forall l':list, lel l' nil -> nil = l'.
Proof. 
	intro l'; elim l'; auto with list arith.
	intros a' y H H0.
	(*  <list>nil=(cons a' y)
	    ============================
	      H0 : (lel (cons a' y) nil)
	      H : (lel y nil)->(<list>nil=y)
	      y : list
	      a' : A
	      l' : list *)
	absurd (S (length y) <= 0); auto with list arith.
Qed.
End length_order.

Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons: list
  v62.

Fixpoint In (a:A) (l:list) {struct l} : Prop :=
  match l with
  | nil => False
  | cons b m => b = a \/ In a m
  end.

Lemma in_eq : forall (a:A) (l:list), In a (cons a l).
Proof. 
	simpl in |- *; auto with list.
Qed.
Hint Resolve in_eq: list v62.

Lemma in_cons : forall (a b:A) (l:list), In b l -> In b (cons a l).
Proof. 
	simpl in |- *; auto with list.
Qed.
Hint Resolve in_cons: list v62.

Lemma in_app_or : forall (l m:list) (a:A), In a (app l m) -> In a l \/ In a m.
Proof. 
	intros l m a.
	elim l; simpl in |- *; auto with list.
	intros a0 y H H0.
	(*  ((<A>a0=a)\/(In a y))\/(In a m)
	    ============================
	      H0 : (<A>a0=a)\/(In a (app y m))
	      H : (In a (app y m))->((In a y)\/(In a m))
	      y : list
	      a0 : A
	      a : A
	      m : list
	      l : list *)
	elim H0; auto with list.
	intro H1.
	(*  ((<A>a0=a)\/(In a y))\/(In a m)
	    ============================
	      H1 : (In a (app y m)) *)
	elim (H H1); auto with list.
Qed.
Hint Immediate in_app_or: list v62.

Lemma in_or_app : forall (l m:list) (a:A), In a l \/ In a m -> In a (app l m).
Proof. 
	intros l m a.
	elim l; simpl in |- *; intro H.
	(* 1 (In a m)
	    ============================
	      H : False\/(In a m)
	      a : A
	      m : list
	      l : list *)
	elim H; auto with list; intro H0.
	(*  (In a m)
	    ============================
	      H0 : False *)
	elim H0. (* subProof completed *)
	intros y H0 H1.
	(*  2 (<A>H=a)\/(In a (app y m))
	    ============================
	      H1 : ((<A>H=a)\/(In a y))\/(In a m)
	      H0 : ((In a y)\/(In a m))->(In a (app y m))
	      y : list *)
	elim H1; auto 4 with list.
	intro H2.
	(*  (<A>H=a)\/(In a (app y m))
	    ============================
	      H2 : (<A>H=a)\/(In a y) *)
	elim H2; auto with list.
Qed.
Hint Resolve in_or_app: list v62.

Definition incl (l m:list) := forall a:A, In a l -> In a m.

Hint Unfold incl: list v62.

Lemma incl_refl : forall l:list, incl l l.
Proof. 
	auto with list.
Qed.
Hint Resolve incl_refl: list v62.

Lemma incl_tl : forall (a:A) (l m:list), incl l m -> incl l (cons a m).
Proof. 
	auto with list.
Qed.
Hint Immediate incl_tl: list v62.

Lemma incl_tran : forall l m n:list, incl l m -> incl m n -> incl l n.
Proof. 
	auto with list.
Qed.

Lemma incl_appl : forall l m n:list, incl l n -> incl l (app n m).
Proof. 
	auto with list.
Qed.
Hint Immediate incl_appl: list v62.

Lemma incl_appr : forall l m n:list, incl l n -> incl l (app m n).
Proof. 
	auto with list.
Qed.
Hint Immediate incl_appr: list v62.

Lemma incl_cons :
 forall (a:A) (l m:list), In a m -> incl l m -> incl (cons a l) m.
Proof. 
	unfold incl in |- *; simpl in |- *; intros a l m H H0 a0 H1.
	(*  (In a0 m)
	    ============================
	      H1 : (<A>a=a0)\/(In a0 l)
	      a0 : A
	      H0 : (a:A)(In a l)->(In a m)
	      H : (In a m)
	      m : list
	      l : list
	      a : A *)
	elim H1.
	(*  1 (<A>a=a0)->(In a0 m) *)
	elim H1; auto with list; intro H2.
	(*  (<A>a=a0)->(In a0 m)
	    ============================
	      H2 : <A>a=a0 *)
	elim H2; auto with list. (* solves subgoal *)
	(*  2 (In a0 l)->(In a0 m) *)
	auto with list.
Qed.
Hint Resolve incl_cons: list v62.

Lemma incl_app : forall l m n:list, incl l n -> incl m n -> incl (app l m) n.
Proof. 
	unfold incl in |- *; simpl in |- *; intros l m n H H0 a H1.
	(*  (In a n)
	    ============================
	      H1 : (In a (app l m))
	      a : A
	      H0 : (a:A)(In a m)->(In a n)
	      H : (a:A)(In a l)->(In a n)
	      n : list
	      m : list
	      l : list *)
	elim (in_app_or l m a); auto with list.
Qed.
Hint Resolve incl_app: list v62.