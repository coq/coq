(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id$ i*)

(** Booleans  *)

(** The type [bool] is defined in the prelude as
    [Inductive bool : Set := true : bool | false : bool] *)

(** Interpretation of booleans as Proposition *)
Definition Is_true (b:bool) :=
  match b with
  | true => True
  | false => False
  end.
Hint Unfold Is_true: bool.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof.
  intros; rewrite H; auto with bool.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof.
  intros; rewrite <- H; auto with bool.
Qed.

Hint Immediate Is_true_eq_right Is_true_eq_left: bool.

(*******************)
(** Discrimination *)
(*******************)

Lemma diff_true_false : true <> false.
Proof.
unfold not in |- *; intro contr; change (Is_true false) in |- *.
elim contr; simpl in |- *; trivial with bool.
Qed.
Hint Resolve diff_true_false: bool v62.

Lemma diff_false_true : false <> true.
Proof.
red in |- *; intros H; apply diff_true_false.
symmetry  in |- *.
assumption.
Qed.
Hint Resolve diff_false_true: bool v62.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
intros b H; rewrite H; auto with bool.
Qed.
Hint Resolve eq_true_false_abs: bool.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
destruct b.
intros.
red in H; elim H.
reflexivity.
intros abs.
reflexivity.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
destruct b.
intros.
reflexivity.
intro H; red in H; elim H.
reflexivity.
Qed.

(**********************)
(** Order on booleans *)
(**********************)

Definition leb (b1 b2:bool) :=
  match b1 with
  | true => b2 = true
  | false => True
  end.
Hint Unfold leb: bool v62.

(*************)
(** Equality *)
(*************)

Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
destruct x; simpl in |- *; auto with bool.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
destruct x; destruct y; simpl in |- *; tauto.
Qed.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
destruct x; simpl in |- *; tauto.
Qed.
 
Lemma Is_true_eq_true2 : forall x:bool, x = true -> Is_true x.
destruct x; simpl in |- *; auto with bool.
Qed.

Lemma eqb_subst :
 forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
unfold eqb in |- *.
intros P b1.
intros b2.
case b1.
case b2.
trivial with bool.
intros H.
inversion_clear H.
case b2.
intros H.
inversion_clear H.
trivial with bool.
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
intro b.
case b.
trivial with bool.
trivial with bool.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
destruct a; destruct b; simpl in |- *; intro; discriminate H || reflexivity.
Qed.


(************************)
(** Logical combinators *)
(************************)
 
Definition ifb (b1 b2 b3:bool) : bool :=
  match b1 with
  | true => b2
  | false => b3
  end.

Definition andb (b1 b2:bool) : bool := ifb b1 b2 false.

Definition orb (b1 b2:bool) : bool := ifb b1 true b2.

Definition implb (b1 b2:bool) : bool := ifb b1 b2 true.

Definition xorb (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => false
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Definition negb (b:bool) := match b with
                            | true => false
                            | false => true
                            end.

Infix "||" := orb (at level 50, left associativity) : bool_scope.
Infix "&&" := andb (at level 40, left associativity) : bool_scope.

Open Scope bool_scope.

Delimit Scope bool_scope with bool.

Bind Scope bool_scope with bool.

(**************************)
(** Lemmas about [negb]   *)
(**************************)

Lemma negb_intro : forall b:bool, b = negb (negb b).
Proof.
destruct b; reflexivity.
Qed.

Lemma negb_elim : forall b:bool, negb (negb b) = b.
Proof.
destruct b; reflexivity.
Qed.
       
Lemma negb_orb : forall b1 b2:bool, negb (b1 || b2) = negb b1 && negb b2.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (b1 && b2) = negb b1 || negb b2.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof.
destruct b; destruct b'; intros; simpl in |- *; trivial with bool.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof.
destruct b; simpl in |- *; intro; apply diff_true_false;
 auto with bool.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
destruct b.
trivial with bool.
trivial with bool.
Qed.
 
Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
destruct b.
trivial with bool.
trivial with bool.
Qed.


Lemma if_negb :
 forall (A:Set) (b:bool) (x y:A),
   (if negb b then x else y) = (if b then y else x).
Proof.
  destruct b; trivial.
Qed.


(****************************)
(** A few lemmas about [or] *)
(****************************)

Lemma orb_prop : forall a b:bool, a || b = true -> a = true \/ b = true.
destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
 auto with bool.
Qed.

Lemma orb_prop2 : forall a b:bool, Is_true (a || b) -> Is_true a \/ Is_true b.
destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
 auto with bool.
Qed.

Lemma orb_true_intro :
 forall b1 b2:bool, b1 = true \/ b2 = true -> b1 || b2 = true.
destruct b1; auto with bool.
destruct 1; intros.
elim diff_true_false; auto with bool.
rewrite H; trivial with bool.
Qed.
Hint Resolve orb_true_intro: bool v62.

Lemma orb_b_true : forall b:bool, b || true = true.
auto with bool.
Qed.
Hint Resolve orb_b_true: bool v62.

Lemma orb_true_b : forall b:bool, true || b = true.
trivial with bool.
Qed.

Definition orb_true_elim :
  forall b1 b2:bool, b1 || b2 = true -> {b1 = true} + {b2 = true}.
destruct b1; simpl in |- *; auto with bool.
Defined.

Lemma orb_false_intro :
 forall b1 b2:bool, b1 = false -> b2 = false -> b1 || b2 = false.
intros b1 b2 H1 H2; rewrite H1; rewrite H2; trivial with bool.
Qed.
Hint Resolve orb_false_intro: bool v62.

Lemma orb_b_false : forall b:bool, b || false = b.
Proof.
  destruct b; trivial with bool.
Qed.
Hint Resolve orb_b_false: bool v62.

Lemma orb_false_b : forall b:bool, false || b = b.
Proof.
  destruct b; trivial with bool.
Qed.
Hint Resolve orb_false_b: bool v62.

Lemma orb_false_elim :
 forall b1 b2:bool, b1 || b2 = false -> b1 = false /\ b2 = false.
Proof.
  destruct b1.
  intros; elim diff_true_false; auto with bool.
  destruct b2.
  intros; elim diff_true_false; auto with bool.
  auto with bool.
Qed.

Lemma orb_neg_b : forall b:bool, b || negb b = true.
Proof.
  destruct b; reflexivity.
Qed.
Hint Resolve orb_neg_b: bool v62.

Lemma orb_comm : forall b1 b2:bool, b1 || b2 = b2 || b1.
destruct b1; destruct b2; reflexivity.
Qed.

Lemma orb_assoc : forall b1 b2 b3:bool, b1 || (b2 || b3) = b1 || b2 || b3.
Proof.
  destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Hint Resolve orb_comm orb_assoc orb_b_false orb_false_b: bool v62.

(*****************************)
(** A few lemmas about [and] *)
(*****************************)

Lemma andb_prop : forall a b:bool, a && b = true -> a = true /\ b = true.

Proof.
  destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
   auto with bool.
Qed.
Hint Resolve andb_prop: bool v62.

Definition andb_true_eq :
  forall a b:bool, true = a && b -> true = a /\ true = b.
Proof.
  destruct a; destruct b; auto.
Defined.

Lemma andb_prop2 :
 forall a b:bool, Is_true (a && b) -> Is_true a /\ Is_true b.
Proof.
  destruct a; destruct b; simpl in |- *; try (intro H; discriminate H);
   auto with bool.
Qed.
Hint Resolve andb_prop2: bool v62.

Lemma andb_true_intro :
 forall b1 b2:bool, b1 = true /\ b2 = true -> b1 && b2 = true.
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.
Hint Resolve andb_true_intro: bool v62.

Lemma andb_true_intro2 :
 forall b1 b2:bool, Is_true b1 -> Is_true b2 -> Is_true (b1 && b2).
Proof.
  destruct b1; destruct b2; simpl in |- *; tauto.
Qed.
Hint Resolve andb_true_intro2: bool v62.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false -> b1 && b2 = false.
destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> b1 && b2 = false.
destruct b1; destruct b2; simpl in |- *; tauto || auto with bool.
Qed.

Lemma andb_b_false : forall b:bool, b && false = false.
destruct b; auto with bool.
Qed.

Lemma andb_false_b : forall b:bool, false && b = false.
trivial with bool.
Qed.

Lemma andb_b_true : forall b:bool, b && true = b.
destruct b; auto with bool.
Qed.

Lemma andb_true_b : forall b:bool, true && b = b.
trivial with bool.
Qed.

Definition andb_false_elim :
  forall b1 b2:bool, b1 && b2 = false -> {b1 = false} + {b2 = false}.
destruct b1; simpl in |- *; auto with bool.
Defined.
Hint Resolve andb_false_elim: bool v62.

Lemma andb_neg_b : forall b:bool, b && negb b = false.
destruct b; reflexivity.
Qed.   
Hint Resolve andb_neg_b: bool v62.

Lemma andb_comm : forall b1 b2:bool, b1 && b2 = b2 && b1.
destruct b1; destruct b2; reflexivity.
Qed.

Lemma andb_assoc : forall b1 b2 b3:bool, b1 && (b2 && b3) = b1 && b2 && b3.
destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Hint Resolve andb_comm andb_assoc: bool v62.

(*******************************)
(** Properties of [xorb]       *)
(*******************************)

Lemma xorb_false : forall b:bool, xorb b false = b.
Proof.
  destruct b; trivial.
Qed.

Lemma false_xorb : forall b:bool, xorb false b = b.
Proof.
  destruct b; trivial.
Qed.

Lemma xorb_true : forall b:bool, xorb b true = negb b.
Proof.
  trivial.
Qed.

Lemma true_xorb : forall b:bool, xorb true b = negb b.
Proof.
  destruct b; trivial.
Qed.

Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof.
  destruct b; trivial.
Qed.

Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof.
  destruct b; destruct b'; trivial.
Qed.

Lemma xorb_assoc :
 forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof.
  destruct b; destruct b'; destruct b''; trivial.
Qed.

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof.
  destruct b; destruct b'; trivial.
  unfold xorb in |- *. intros. rewrite H. reflexivity.
Qed.

Lemma xorb_move_l_r_1 :
 forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof.
  intros. rewrite <- (false_xorb b'). rewrite <- (xorb_nilpotent b). rewrite xorb_assoc.
  rewrite H. reflexivity.
Qed.

Lemma xorb_move_l_r_2 :
 forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof.
  intros. rewrite xorb_comm in H. rewrite (xorb_move_l_r_1 b' b b'' H). apply xorb_comm.
Qed.

Lemma xorb_move_r_l_1 :
 forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof.
  intros. rewrite H. rewrite <- xorb_assoc. rewrite xorb_nilpotent. apply false_xorb.
Qed.

Lemma xorb_move_r_l_2 :
 forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof.
  intros. rewrite H. rewrite xorb_assoc. rewrite xorb_nilpotent. apply xorb_false.
Qed.

(*******************************)
(** De Morgan's law            *)
(*******************************)

Lemma demorgan1 :
 forall b1 b2 b3:bool, b1 && (b2 || b3) = b1 && b2 || b1 && b3.
destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma demorgan2 :
 forall b1 b2 b3:bool, (b1 || b2) && b3 = b1 && b3 || b2 && b3.
destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma demorgan3 :
 forall b1 b2 b3:bool, b1 || b2 && b3 = (b1 || b2) && (b1 || b3).
destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma demorgan4 :
 forall b1 b2 b3:bool, b1 && b2 || b3 = (b1 || b3) && (b2 || b3).
destruct b1; destruct b2; destruct b3; reflexivity.
Qed.

Lemma absoption_andb : forall b1 b2:bool, b1 && (b1 || b2) = b1.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.

Lemma absoption_orb : forall b1 b2:bool, b1 || b1 && b2 = b1.
Proof.
  destruct b1; destruct b2; simpl in |- *; reflexivity.
Qed.


(** Misc. equalities between booleans (to be used by Auto) *)

Lemma bool_1 : forall b1 b2:bool, (b1 = true <-> b2 = true) -> b1 = b2. 
Proof. 
 intros b1 b2; case b1; case b2; intuition.
Qed.

Lemma bool_2 : forall b1 b2:bool, b1 = b2 -> b1 = true -> b2 = true.
Proof. 
 intros b1 b2; case b1; case b2; intuition.
Qed. 

Lemma bool_3 : forall b:bool, negb b <> true -> b = true.
Proof.
  destruct b; intuition.
Qed.

Lemma bool_4 : forall b:bool, b = true -> negb b <> true.  
Proof.
  destruct b; intuition.
Qed.

Lemma bool_5 : forall b:bool, negb b = true -> b <> true.
Proof.
  destruct b; intuition.
Qed.

Lemma bool_6 : forall b:bool, b <> true -> negb b = true.  
Proof.
  destruct b; intuition.
Qed.

Hint Resolve bool_1 bool_2 bool_3 bool_4 bool_5 bool_6.
