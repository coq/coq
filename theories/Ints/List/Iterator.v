
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Export List.
Require Export LPermutation.
Require Import Arith.
 
Section Iterator.
Variables A B : Set.
Variable zero : B.
Variable f : A ->  B.
Variable g : B -> B ->  B.
Hypothesis g_zero : forall a,  g a zero = a.
Hypothesis g_trans : forall a b c,  g a (g b c) = g (g a b) c.
Hypothesis g_sym : forall a b,  g a b = g b a.
 
Definition iter := fold_right (fun a r => g (f a) r) zero.
Hint Unfold iter .
 
Theorem iter_app: forall l1 l2,  iter (app l1 l2) = g (iter l1) (iter l2).
intros l1; elim l1; simpl; auto.
intros l2; rewrite g_sym; auto.
intros a l H l2; rewrite H.
rewrite g_trans; auto.
Qed.
 
Theorem iter_permutation: forall l1 l2, permutation l1 l2 ->  iter l1 = iter l2.
intros l1 l2 H; elim H; simpl; auto; clear H l1 l2.
intros a l1 l2 H1 H2; apply f_equal2 with ( f := g ); auto.
intros a b l; (repeat rewrite g_trans).
apply f_equal2 with ( f := g ); auto.
intros l1 l2 l3 H H0 H1 H2; apply trans_equal with ( 1 := H0 ); auto.
Qed.
 
Lemma iter_inv:
 forall P l,
 P zero ->
 (forall a b, P a -> P b ->  P (g a b)) ->
 (forall x, In x l ->  P (f x)) ->  P (iter l).
intros P l H H0; (elim l; simpl; auto).
Qed.
Variable next : A ->  A.
 
Fixpoint progression (m : A) (n : nat) {struct n} : list A :=
 match n with   0 => nil
               | S n1 => cons m (progression (next m) n1) end.
 
Fixpoint next_n (c : A) (n : nat) {struct n} : A :=
 match n with 0 => c | S n1 => next_n (next c) n1 end.
 
Theorem progression_app:
 forall a b n m,
 le m n ->
 b = next_n a m ->
  progression a n = app (progression a m) (progression b (n - m)).
intros a b n m; generalize a b n; clear a b n; elim m; clear m; simpl.
intros a b n H H0; apply f_equal2 with ( f := progression ); auto with arith.
intros m H a b n; case n; simpl; clear n.
intros H1; absurd (0 < 1 + m); auto with arith.
intros n H0 H1; apply f_equal2 with ( f := @cons A ); auto with arith.
Qed.
 
Let iter_progression := fun m n => iter (progression m n).
 
Theorem iter_progression_app:
 forall a b n m,
 le m n ->
 b = next_n a m ->
  iter (progression a n) =
  g (iter (progression a m)) (iter (progression b (n - m))).
intros a b n m H H0; unfold iter_progression; rewrite (progression_app a b n m);
 (try apply iter_app); auto.
Qed.
 
Theorem length_progression: forall z n,  length (progression z n) = n.
intros z n; generalize z; elim n; simpl; auto.
Qed.
 
End Iterator.
Implicit Arguments iter [A B].
Implicit Arguments progression [A].
Implicit Arguments next_n [A].
Hint Unfold iter .
Hint Unfold progression .
Hint Unfold next_n .
 
Theorem iter_ext:
 forall (A B : Set) zero (f1 : A ->  B) f2 g l,
 (forall a, In a l ->  f1 a = f2 a) ->  iter zero f1 g l = iter zero f2 g l.
intros A B zero f1 f2 g l; elim l; simpl; auto.
intros a l0 H H0; apply f_equal2 with ( f := g ); auto.
Qed.
 
Theorem iter_map:
 forall (A B C : Set) zero (f : B ->  C) g (k : A ->  B) l,
  iter zero f g (map k l) = iter zero (fun x => f (k x)) g l.
intros A B C zero f g k l; elim l; simpl; auto.
intros; apply f_equal2 with ( f := g ); auto with arith.
Qed.
 
Theorem iter_comp:
 forall (A B : Set) zero (f1 f2 : A ->  B) g l,
 (forall a,  g a zero = a) ->
 (forall a b c,  g a (g b c) = g (g a b) c) ->
 (forall a b,  g a b = g b a) ->
  g (iter zero f1 g l) (iter zero f2 g l) =
  iter zero (fun x => g (f1 x) (f2 x)) g l.
intros A B zero f1 f2 g l g_zero g_trans g_sym; elim l; simpl; auto.
intros a l0 H; rewrite <- H; (repeat rewrite <- g_trans).
apply f_equal2 with ( f := g ); auto.
(repeat rewrite g_trans); apply f_equal2 with ( f := g ); auto.
Qed.
 
Theorem iter_com:
 forall (A B : Set) zero (f : A -> A ->  B) g l1 l2,
 (forall a,  g a zero = a) ->
 (forall a b c,  g a (g b c) = g (g a b) c) ->
 (forall a b,  g a b = g b a) ->
  iter zero (fun x => iter zero (fun y => f x y) g l1) g l2 =
  iter zero (fun y => iter zero (fun x => f x y) g l2) g l1.
intros A B zero f g l1 l2 H H0 H1; generalize l2; elim l1; simpl; auto;
 clear l1 l2.
intros l2; elim l2; simpl; auto with arith.
intros; rewrite H1; rewrite H; auto with arith.
intros a l1 H2 l2; case l2; clear l2; simpl; auto.
elim l1; simpl; auto with arith.
intros; rewrite H1; rewrite H; auto with arith.
intros b l2.
rewrite <- (iter_comp
             _ _ zero (fun x => f x a)
             (fun x => iter zero (fun (y : A) => f x y) g l1)); auto with arith.
rewrite <- (iter_comp
             _ _ zero (fun y => f b y)
             (fun y => iter zero (fun (x : A) => f x y) g l2)); auto with arith.
(repeat rewrite H0); auto.
apply f_equal2 with ( f := g ); auto.
(repeat rewrite <- H0); auto.
apply f_equal2 with ( f := g ); auto.
Qed.
 
Theorem iter_comp_const:
 forall (A B : Set) zero (f : A ->  B) g k l,
 k zero = zero ->
 (forall a b,  k (g a b) = g (k a) (k b)) ->
  k (iter zero f g l) = iter zero (fun x => k (f x)) g l.
intros A B zero f g k l H H0; elim l; simpl; auto.
intros a l0 H1; rewrite H0; apply f_equal2 with ( f := g ); auto.
Qed.
 
Lemma next_n_S: forall n m,  next_n S n m = plus n m.
intros n m; generalize n; elim m; clear n m; simpl; auto with arith.
intros m H n; case n; simpl; auto with arith.
rewrite H; auto with arith.
intros n1; rewrite H; simpl; auto with arith.
Qed.
 
Theorem progression_S_le_init:
 forall n m p, In p (progression S n m) ->  le n p.
intros n m; generalize n; elim m; clear n m; simpl; auto.
intros; contradiction.
intros m H n p [H1|H1]; auto with arith.
subst n; auto.
apply le_S_n; auto with arith.
Qed.
 
Theorem progression_S_le_end:
 forall n m p, In p (progression S n m) ->  lt p (n + m).
intros n m; generalize n; elim m; clear n m; simpl; auto.
intros; contradiction.
intros m H n p [H1|H1]; auto with arith.
subst n; auto with arith.
rewrite <- plus_n_Sm; auto with arith.
rewrite <- plus_n_Sm; auto with arith.
generalize (H (S n) p); auto with arith.
Qed.
