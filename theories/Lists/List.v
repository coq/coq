(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

Require Import Le.


Section Lists.

Variable A : Set.

Set Implicit Arguments.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Infix "::" := cons (at level 60, right associativity) : list_scope.

Open Scope list_scope.

(*************************)
(** Discrimination       *)
(*************************)

Lemma nil_cons : forall (a:A) (m:list), nil <> a :: m.
Proof. 
  intros; discriminate.
Qed.

(*************************)
(** Concatenation        *)
(*************************)

Fixpoint app (l m:list) {struct l} : list :=
  match l with
  | nil => m
  | a :: l1 => a :: app l1 m
  end.

Infix "++" := app (right associativity, at level 60) : list_scope.

Lemma app_nil_end : forall l:list, l = l ++ nil.
Proof. 
	induction l; simpl in |- *; auto.
        rewrite <- IHl; auto.
Qed.
Hint Resolve app_nil_end.

Ltac now_show c := change c in |- *.

Lemma app_ass : forall l m n:list, (l ++ m) ++ n = l ++ m ++ n.
Proof. 
	intros. induction l; simpl in |- *; auto.
        now_show (a :: (l ++ m) ++ n = a :: l ++ m ++ n).
	rewrite <- IHl; auto.
Qed.
Hint Resolve app_ass.

Lemma ass_app : forall l m n:list, l ++ m ++ n = (l ++ m) ++ n.
Proof. 
	auto.
Qed.
Hint Resolve ass_app.

Lemma app_comm_cons : forall (x y:list) (a:A), a :: x ++ y = (a :: x) ++ y.
Proof.
 auto.
Qed.

Lemma app_eq_nil : forall x y:list, x ++ y = nil -> x = nil /\ y = nil.
Proof.
  destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
   simpl in |- *; auto.
  intros H; discriminate H.
  intros; discriminate H.
Qed.

Lemma app_cons_not_nil : forall (x y:list) (a:A), nil <> x ++ a :: y.
Proof.
unfold not in |- *.
  destruct x as [| a l]; simpl in |- *; intros.
  discriminate H.
  discriminate H.
Qed.

Lemma app_eq_unit :
 forall (x y:list) (a:A),
   x ++ y = a :: nil -> x = nil /\ y = a :: nil \/ x = a :: nil /\ y = nil.

Proof.
  destruct x as [| a l]; [ destruct y as [| a l] | destruct y as [| a0 l0] ];
   simpl in |- *.
  intros a H; discriminate H.
  left; split; auto.
  right; split; auto.
  generalize H.
  generalize (app_nil_end l); intros E.
  rewrite <- E; auto.
  intros.
  injection H.
  intro.
  cut (nil = l ++ a0 :: l0); auto.
  intro.
  generalize (app_cons_not_nil _ _ _ H1); intro.
  elim H2.
Qed.

Lemma app_inj_tail :
 forall (x y:list) (a b:A), x ++ a :: nil = y ++ b :: nil -> x = y /\ a = b.
Proof.
  induction x as [| x l IHl];
   [ destruct y as [| a l] | destruct y as [| a l0] ]; 
   simpl in |- *; auto.
  intros a b H.
  injection H.
  auto.
  intros a0 b H.
  injection H; intros.
  generalize (app_cons_not_nil _ _ _ H0); destruct 1.
  intros a b H.
  injection H; intros.
  cut (nil = l ++ a :: nil); auto.
  intro.
  generalize (app_cons_not_nil _ _ _ H2); destruct 1.
  intros a0 b H.
  injection H; intros.
  destruct (IHl l0 a0 b H0). 
  split; auto.
  rewrite <- H1; rewrite <- H2; reflexivity.
Qed.

(*************************)
(** Head and tail        *)
(*************************)

Definition head (l:list) :=
  match l with
  | nil => error
  | x :: _ => value x
  end.

Definition tail (l:list) : list :=
  match l with
  | nil => nil
  | a :: m => m
  end.

(****************************************)
(** Length of lists                     *)
(****************************************)

Fixpoint length (l:list) : nat :=
  match l with
  | nil => 0
  | _ :: m => S (length m)
  end.

(******************************)
(** Length order of lists     *)
(******************************)

Section length_order.
Definition lel (l m:list) := length l <= length m.

Variables a b : A.
Variables l m n : list.

Lemma lel_refl : lel l l.
Proof. 
	unfold lel in |- *; auto with arith.
Qed.

Lemma lel_trans : lel l m -> lel m n -> lel l n.
Proof. 
	unfold lel in |- *; intros.
        now_show (length l <= length n).
        apply le_trans with (length m); auto with arith.
Qed.

Lemma lel_cons_cons : lel l m -> lel (a :: l) (b :: m).
Proof. 
	unfold lel in |- *; simpl in |- *; auto with arith.
Qed.

Lemma lel_cons : lel l m -> lel l (b :: m).
Proof. 
	unfold lel in |- *; simpl in |- *; auto with arith.
Qed.

Lemma lel_tail : lel (a :: l) (b :: m) -> lel l m.
Proof. 
	unfold lel in |- *; simpl in |- *; auto with arith.
Qed.

Lemma lel_nil : forall l':list, lel l' nil -> nil = l'.
Proof. 
	intro l'; elim l'; auto with arith.
	intros a' y H H0.
        now_show (nil = a' :: y).
	absurd (S (length y) <= 0); auto with arith.
Qed.
End length_order.

Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons.

(*********************************)
(** The [In] predicate           *)
(*********************************)

Fixpoint In (a:A) (l:list) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => b = a \/ In a m
  end.

Lemma in_eq : forall (a:A) (l:list), In a (a :: l).
Proof. 
	simpl in |- *; auto.
Qed.
Hint Resolve in_eq.

Lemma in_cons : forall (a b:A) (l:list), In b l -> In b (a :: l).
Proof. 
	simpl in |- *; auto.
Qed.
Hint Resolve in_cons.

Lemma in_nil : forall a:A, ~ In a nil.
Proof.
  unfold not in |- *; intros a H; inversion_clear H.
Qed.


Lemma in_inv : forall (a b:A) (l:list), In b (a :: l) -> a = b \/ In b l.
Proof.
 intros a b l H; inversion_clear H; auto.
Qed.

Lemma In_dec :
 (forall x y:A, {x = y} + {x <> y}) ->
 forall (a:A) (l:list), {In a l} + {~ In a l}.

Proof.
  induction l as [| a0 l IHl].
  right; apply in_nil.
  destruct (H a0 a); simpl in |- *; auto.
  destruct IHl; simpl in |- *; auto. 
  right; unfold not in |- *; intros [Hc1| Hc2]; auto.
Qed.

Lemma in_app_or : forall (l m:list) (a:A), In a (l ++ m) -> In a l \/ In a m.
Proof. 
	intros l m a.
	elim l; simpl in |- *; auto.
	intros a0 y H H0.
	now_show ((a0 = a \/ In a y) \/ In a m).
	elim H0; auto.
	intro H1.
        now_show ((a0 = a \/ In a y) \/ In a m).
	elim (H H1); auto.
Qed.
Hint Immediate in_app_or.

Lemma in_or_app : forall (l m:list) (a:A), In a l \/ In a m -> In a (l ++ m).
Proof. 
	intros l m a.
	elim l; simpl in |- *; intro H.
        now_show (In a m).
	elim H; auto; intro H0.
	now_show (In a m).
	elim H0. (* subProof completed *)
	intros y H0 H1.
	now_show (H = a \/ In a (y ++ m)).
	elim H1; auto 4.
	intro H2.
	now_show (H = a \/ In a (y ++ m)).
	elim H2; auto.
Qed.
Hint Resolve in_or_app.

(***************************)
(** Set inclusion on list  *)
(***************************)

Definition incl (l m:list) := forall a:A, In a l -> In a m.
Hint Unfold incl.

Lemma incl_refl : forall l:list, incl l l.
Proof. 
	auto.
Qed.
Hint Resolve incl_refl.

Lemma incl_tl : forall (a:A) (l m:list), incl l m -> incl l (a :: m).
Proof. 
	auto.
Qed.
Hint Immediate incl_tl.

Lemma incl_tran : forall l m n:list, incl l m -> incl m n -> incl l n.
Proof. 
	auto.
Qed.

Lemma incl_appl : forall l m n:list, incl l n -> incl l (n ++ m).
Proof. 
	auto.
Qed.
Hint Immediate incl_appl.

Lemma incl_appr : forall l m n:list, incl l n -> incl l (m ++ n).
Proof. 
	auto.
Qed.
Hint Immediate incl_appr.

Lemma incl_cons :
 forall (a:A) (l m:list), In a m -> incl l m -> incl (a :: l) m.
Proof. 
	unfold incl in |- *; simpl in |- *; intros a l m H H0 a0 H1.
        now_show (In a0 m).
	elim H1.
	now_show (a = a0 -> In a0 m).
	elim H1; auto; intro H2.
	now_show (a = a0 -> In a0 m).
	elim H2; auto. (* solves subgoal *)
	now_show (In a0 l -> In a0 m).
	auto.
Qed.
Hint Resolve incl_cons.

Lemma incl_app : forall l m n:list, incl l n -> incl m n -> incl (l ++ m) n.
Proof. 
	unfold incl in |- *; simpl in |- *; intros l m n H H0 a H1.
        now_show (In a n).
	elim (in_app_or _ _ _ H1); auto.
Qed.
Hint Resolve incl_app.

(**************************)
(** Nth element of a list *)
(**************************)

Fixpoint nth (n:nat) (l:list) (default:A) {struct l} : A :=
  match n, l with
  | O, x :: l' => x
  | O, other => default
  | S m, nil => default
  | S m, x :: t => nth m t default
  end.

Fixpoint nth_ok (n:nat) (l:list) (default:A) {struct l} : bool :=
  match n, l with
  | O, x :: l' => true
  | O, other => false
  | S m, nil => false
  | S m, x :: t => nth_ok m t default
  end.

Lemma nth_in_or_default :
 forall (n:nat) (l:list) (d:A), {In (nth n l d) l} + {nth n l d = d}.
(* Realizer nth_ok. Program_all. *)
Proof. 
  intros n l d; generalize n; induction l; intro n0.
  right; case n0; trivial.
  case n0; simpl in |- *.
  auto.
  intro n1; elim (IHl n1); auto.     
Qed.

Lemma nth_S_cons :
 forall (n:nat) (l:list) (d a:A),
   In (nth n l d) l -> In (nth (S n) (a :: l) d) (a :: l).
Proof. 
  simpl in |- *; auto.
Qed.

Fixpoint nth_error (l:list) (n:nat) {struct n} : Exc A :=
  match n, l with
  | O, x :: _ => value x
  | S n, _ :: l => nth_error l n
  | _, _ => error
  end.

Definition nth_default (default:A) (l:list) (n:nat) : A :=
  match nth_error l n with
  | Some x => x
  | None => default
  end.

Lemma nth_In :
 forall (n:nat) (l:list) (d:A), n < length l -> In (nth n l d) l.

Proof.
unfold lt in |- *; induction n as [| n hn]; simpl in |- *.
destruct l; simpl in |- *; [ inversion 2 | auto ].
destruct l as [| a l hl]; simpl in |- *.
inversion 2.
intros d ie; right; apply hn; auto with arith.
Qed.

(********************************)
(** Decidable equality on lists *)
(********************************)


Lemma list_eq_dec :
 (forall x y:A, {x = y} + {x <> y}) -> forall x y:list, {x = y} + {x <> y}.
Proof.
  induction x as [| a l IHl]; destruct y as [| a0 l0]; auto.
  destruct (H a a0) as [e| e].
  destruct (IHl l0) as [e'| e'].
  left; rewrite e; rewrite e'; trivial.
  right; red in |- *; intro.
  apply e'; injection H0; trivial.
  right; red in |- *; intro.
  apply e; injection H0; trivial.
Qed.

(*************************)
(**  Reverse             *)
(*************************)

Fixpoint rev (l:list) : list :=
  match l with
  | nil => nil
  | x :: l' => rev l' ++ x :: nil
  end.

Lemma distr_rev : forall x y:list, rev (x ++ y) = rev y ++ rev x.
Proof.
 induction x as [| a l IHl].
 destruct y as [| a l].
 simpl in |- *.
 auto.

 simpl in |- *.
 apply app_nil_end; auto.

 intro y.
 simpl in |- *.
 rewrite (IHl y).
 apply (app_ass (rev y) (rev l) (a :: nil)).
Qed.

Remark rev_unit : forall (l:list) (a:A), rev (l ++ a :: nil) = a :: rev l.
Proof.
 intros.
 apply (distr_rev l (a :: nil)); simpl in |- *; auto.
Qed.

Lemma rev_involutive : forall l:list, rev (rev l) = l.
Proof.
 induction l as [| a l IHl].
 simpl in |- *; auto.

 simpl in |- *.
 rewrite (rev_unit (rev l) a).
 rewrite IHl; auto.
Qed.

(*********************************************)
(**  Reverse Induction Principle on Lists    *)
(*********************************************)

Section Reverse_Induction.

Unset Implicit Arguments.

Remark rev_list_ind :
 forall P:list -> Prop,
   P nil ->
   (forall (a:A) (l:list), P (rev l) -> P (rev (a :: l))) ->
   forall l:list, P (rev l).
Proof.
 induction l; auto.
Qed.
Set Implicit Arguments.

Lemma rev_ind :
 forall P:list -> Prop,
   P nil ->
   (forall (x:A) (l:list), P l -> P (l ++ x :: nil)) -> forall l:list, P l.
Proof.
 intros.
 generalize (rev_involutive l).
 intros E; rewrite <- E.
 apply (rev_list_ind P).
 auto.

 simpl in |- *.
 intros.
 apply (H0 a (rev l0)).
 auto.
Qed.

End Reverse_Induction.

End Lists.

Implicit Arguments nil [A].

Hint Resolve nil_cons app_nil_end ass_app app_ass: datatypes v62.
Hint Resolve app_comm_cons app_cons_not_nil: datatypes v62.
Hint Immediate app_eq_nil: datatypes v62.
Hint Resolve app_eq_unit app_inj_tail: datatypes v62. 
Hint Resolve lel_refl lel_cons_cons lel_cons lel_nil lel_nil nil_cons:
  datatypes v62.
Hint Resolve in_eq in_cons in_inv in_nil in_app_or in_or_app: datatypes v62.
Hint Resolve incl_refl incl_tl incl_tran incl_appl incl_appr incl_cons
  incl_app: datatypes v62.

Section Functions_on_lists.

(****************************************************************)
(** Some generic functions on lists and basic functions of them *)
(****************************************************************)

Section Map.
Variables A B : Set.
Variable f : A -> B.
Fixpoint map (l:list A) : list B :=
  match l with
  | nil => nil
  | cons a t => cons (f a) (map t)
  end.
End Map.

Lemma in_map :
 forall (A B:Set) (f:A -> B) (l:list A) (x:A), In x l -> In (f x) (map f l).
Proof. 
  induction l as [| a l IHl]; simpl in |- *;
   [ auto
   | destruct 1; [ left; apply f_equal with (f := f); assumption | auto ] ].
Qed.

Fixpoint flat_map (A B:Set) (f:A -> list B) (l:list A) {struct l} : 
 list B :=
  match l with
  | nil => nil
  | cons x t => app (f x) (flat_map f t)
  end.

Fixpoint list_prod (A B:Set) (l:list A) (l':list B) {struct l} :
 list (A * B) :=
  match l with
  | nil => nil
  | cons x t => app (map (fun y:B => (x, y)) l') (list_prod t l')
  end.

Lemma in_prod_aux :
 forall (A B:Set) (x:A) (y:B) (l:list B),
   In y l -> In (x, y) (map (fun y0:B => (x, y0)) l).
Proof. 
  induction l;
   [ simpl in |- *; auto
   | simpl in |- *; destruct 1 as [H1| ];
      [ left; rewrite H1; trivial | right; auto ] ].
Qed.

Lemma in_prod :
 forall (A B:Set) (l:list A) (l':list B) (x:A) (y:B),
   In x l -> In y l' -> In (x, y) (list_prod l l').
Proof. 
  induction l;
   [ simpl in |- *; tauto
   | simpl in |- *; intros; apply in_or_app; destruct H;
      [ left; rewrite H; apply in_prod_aux; assumption | right; auto ] ].
Qed.

(** [(list_power x y)] is [y^x], or the set of sequences of elts of [y]
    indexed by elts of [x], sorted in lexicographic order. *)

Fixpoint list_power (A B:Set) (l:list A) (l':list B) {struct l} :
 list (list (A * B)) :=
  match l with
  | nil => cons nil nil
  | cons x t =>
      flat_map (fun f:list (A * B) => map (fun y:B => cons (x, y) f) l')
        (list_power t l')
  end.

(************************************)
(** Left-to-right iterator on lists *)
(************************************)

Section Fold_Left_Recursor.
Variables A B : Set.
Variable f : A -> B -> A.
Fixpoint fold_left (l:list B) (a0:A) {struct l} : A :=
  match l with
  | nil => a0
  | cons b t => fold_left t (f a0 b)
  end.
End Fold_Left_Recursor.

(************************************)
(** Right-to-left iterator on lists *)
(************************************)

Section Fold_Right_Recursor.
Variables A B : Set.
Variable f : B -> A -> A.
Variable a0 : A.
Fixpoint fold_right (l:list B) : A :=
  match l with
  | nil => a0
  | cons b t => f b (fold_right t)
  end.
End Fold_Right_Recursor.

Theorem fold_symmetric :
 forall (A:Set) (f:A -> A -> A),
   (forall x y z:A, f x (f y z) = f (f x y) z) ->
   (forall x y:A, f x y = f y x) ->
   forall (a0:A) (l:list A), fold_left f l a0 = fold_right f a0 l.
Proof.
destruct l as [| a l].
reflexivity.
simpl in |- *.
rewrite <- H0.
generalize a0 a.
induction l as [| a3 l IHl]; simpl in |- *.
trivial.
intros.
rewrite H.
rewrite (H0 a2).
rewrite <- (H a1).
rewrite (H0 a1).
rewrite IHl.
reflexivity.
Qed.

End Functions_on_lists.


(** Exporting list notations *)

Infix "::" := cons (at level 60, right associativity) : list_scope.

Infix "++" := app (right associativity, at level 60) : list_scope.

Open Scope list_scope.

(** Declare Scope list_scope with key list *)
Delimit Scope list_scope with list.

Bind Scope list_scope with list.
