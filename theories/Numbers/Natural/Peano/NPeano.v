(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import
 Bool Peano Peano_dec Compare_dec Plus Minus Le Lt EqNat NAxioms NProperties.

(** Functions not already defined *)

Fixpoint pow n m :=
  match m with
    | O => 1
    | S m => n * (pow n m)
  end.

Infix "^" := pow : nat_scope.

Lemma pow_0_r : forall a, a^0 = 1.
Proof. reflexivity. Qed.

Lemma pow_succ_r : forall a b, 0<=b -> a^(S b) = a * a^b.
Proof. reflexivity. Qed.

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

Fixpoint even n :=
  match n with
    | O => true
    | 1 => false
    | S (S n') => even n'
  end.

Definition odd n := negb (even n).

Lemma even_spec : forall n, even n = true <-> Even n.
Proof.
 fix 1.
  destruct n as [|[|n]]; simpl; try rewrite even_spec; split.
  now exists 0.
  trivial.
  discriminate.
  intros (m,H). destruct m. discriminate.
   simpl in H. rewrite <- plus_n_Sm in H. discriminate.
  intros (m,H). exists (S m). rewrite H. simpl. now rewrite plus_n_Sm.
  intros (m,H). destruct m. discriminate. exists m.
   simpl in H. rewrite <- plus_n_Sm in H. inversion H. reflexivity.
Qed.

Lemma odd_spec : forall n, odd n = true <-> Odd n.
Proof.
 unfold odd.
 fix 1.
  destruct n as [|[|n]]; simpl; try rewrite odd_spec; split.
  discriminate.
  intros (m,H). rewrite <- plus_n_Sm in H; discriminate.
  now exists 0.
  trivial.
  intros (m,H). exists (S m). rewrite H. simpl. now rewrite <- (plus_n_Sm m).
  intros (m,H). destruct m. discriminate. exists m.
   simpl in H. rewrite <- plus_n_Sm in H. inversion H. simpl.
   now rewrite <- !plus_n_Sm, <- !plus_n_O.
Qed.

(* A linear, tail-recursive, division for nat.

   In [divmod], [y] is the predecessor of the actual divisor,
   and [u] is [y] minus the real remainder
*)

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition div x y :=
  match y with
    | 0 => 0
    | S y' => fst (divmod x y' 0 y')
  end.

Definition modulo x y :=
  match y with
    | 0 => 0
    | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "/" := div : nat_scope.
Infix "mod" := modulo (at level 40, no associativity) : nat_scope.

Lemma divmod_spec : forall x y q u, u <= y ->
 let (q',u') := divmod x y q u in
 x + (S y)*q + (y-u) = (S y)*q' + (y-u') /\ u' <= y.
Proof.
 induction x. simpl. intuition.
 intros y q u H. destruct u; simpl divmod.
 generalize (IHx y (S q) y (le_n y)). destruct divmod as (q',u').
 intros (EQ,LE); split; trivial.
 rewrite <- EQ, <- minus_n_O, minus_diag, <- plus_n_O.
 now rewrite !plus_Sn_m, plus_n_Sm, <- plus_assoc, mult_n_Sm.
 generalize (IHx y q u (le_Sn_le _ _ H)). destruct divmod as (q',u').
 intros (EQ,LE); split; trivial.
 rewrite <- EQ.
 rewrite !plus_Sn_m, plus_n_Sm. f_equal. now apply minus_Sn_m.
Qed.

Lemma div_mod : forall x y, y<>0 -> x = y*(x/y) + x mod y.
Proof.
 intros x y Hy.
 destruct y; [ now elim Hy | clear Hy ].
 unfold div, modulo.
 generalize (divmod_spec x y 0 y (le_n y)).
 destruct divmod as (q,u).
 intros (U,V).
 simpl in *.
 now rewrite <- mult_n_O, minus_diag, <- !plus_n_O in U.
Qed.

Lemma mod_upper_bound : forall x y, y<>0 -> x mod y < y.
Proof.
 intros x y Hy.
 destruct y; [ now elim Hy | clear Hy ].
 unfold modulo.
 apply le_n_S, le_minus.
Qed.

(** Square root *)

(** The following square root function is linear (and tail-recursive).
  With Peano representation, we can't do better. For faster algorithm,
  see Psqrt/Zsqrt/Nsqrt...

  We search the square root of n = k + p^2 + (q - r)
  with q = 2p and 0<=r<=q. We starts with p=q=r=0, hence
  looking for the square root of n = k. Then we progressively
  decrease k and r. When k = S k' and r=0, it means we can use (S p)
  as new sqrt candidate, since (S k')+p^2+2p = k'+(S p)^2.
  When k reaches 0, we have found the biggest p^2 square contained
  in n, hence the square root of n is p.
*)

Fixpoint sqrt_iter k p q r :=
  match k with
    | O => p
    | S k' => match r with
                | O => sqrt_iter k' (S p) (S (S q)) (S (S q))
                | S r' => sqrt_iter k' p q r'
              end
  end.

Definition sqrt n := sqrt_iter n 0 0 0.

Lemma sqrt_iter_spec : forall k p q r,
 q = p+p -> r<=q ->
 let s := sqrt_iter k p q r in
 s*s <= k + p*p + (q - r) < (S s)*(S s).
Proof.
 induction k.
 (* k = 0 *)
 simpl; intros p q r Hq Hr.
 split.
 apply le_plus_l.
 apply le_lt_n_Sm.
 rewrite <- mult_n_Sm.
 rewrite plus_assoc, (plus_comm p), <- plus_assoc.
 apply plus_le_compat; trivial.
 rewrite <- Hq. apply le_minus.
 (* k = S k' *)
 destruct r.
 (* r = 0 *)
 intros Hq _.
 replace (S k + p*p + (q-0)) with (k + (S p)*(S p) + (S (S q) - S (S q))).
 apply IHk.
 simpl. rewrite <- plus_n_Sm. congruence.
 auto with arith.
 rewrite minus_diag, <- minus_n_O, <- plus_n_O. simpl.
 rewrite <- plus_n_Sm; f_equal. rewrite <- plus_assoc; f_equal.
 rewrite <- mult_n_Sm, (plus_comm p), <- plus_assoc. congruence.
 (* r = S r' *)
 intros Hq Hr.
 replace (S k + p*p + (q-S r)) with (k + p*p + (q - r)).
 apply IHk; auto with arith.
 simpl. rewrite plus_n_Sm. f_equal. rewrite minus_Sn_m; auto.
Qed.

Lemma sqrt_spec : forall n,
 let s := sqrt n in s*s <= n < S s * S s.
Proof.
 intros.
 replace n with (n + 0*0 + (0-0)).
 apply sqrt_iter_spec; auto.
 simpl. now rewrite <- 2 plus_n_O.
Qed.


(** * Implementation of [NAxiomsSig] by [nat] *)

Module Nat
 <: NAxiomsSig <: UsualDecidableTypeFull <: OrderedTypeFull <: TotalOrder.

(** Bi-directional induction. *)

Theorem bi_induction :
  forall A : nat -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
Qed.

(** Basic operations. *)

Definition eq_equiv : Equivalence (@eq nat) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
Program Instance succ_wd : Proper (eq==>eq) S.
Program Instance pred_wd : Proper (eq==>eq) pred.
Program Instance add_wd : Proper (eq==>eq==>eq) plus.
Program Instance sub_wd : Proper (eq==>eq==>eq) minus.
Program Instance mul_wd : Proper (eq==>eq==>eq) mult.

Theorem pred_succ : forall n : nat, pred (S n) = n.
Proof.
reflexivity.
Qed.

Theorem one_succ : 1 = S 0.
Proof.
reflexivity.
Qed.

Theorem two_succ : 2 = S 1.
Proof.
reflexivity.
Qed.

Theorem add_0_l : forall n : nat, 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem add_succ_l : forall n m : nat, (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Theorem sub_0_r : forall n : nat, n - 0 = n.
Proof.
intro n; now destruct n.
Qed.

Theorem sub_succ_r : forall n m : nat, n - (S m) = pred (n - m).
Proof.
induction n; destruct m; simpl; auto. apply sub_0_r.
Qed.

Theorem mul_0_l : forall n : nat, 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem mul_succ_l : forall n m : nat, S n * m = n * m + m.
Proof.
assert (add_S_r : forall n m, n+S m = S(n+m)) by (induction n; auto).
assert (add_comm : forall n m, n+m = m+n).
 induction n; simpl; auto. intros; rewrite add_S_r; auto.
intros n m; now rewrite add_comm.
Qed.

(** Order on natural numbers *)

Program Instance lt_wd : Proper (eq==>eq==>iff) lt.

Theorem lt_succ_r : forall n m : nat, n < S m <-> n <= m.
Proof.
unfold lt; split. apply le_S_n. induction 1; auto.
Qed.


Theorem lt_eq_cases : forall n m : nat, n <= m <-> n < m \/ n = m.
Proof.
split.
inversion 1; auto. rewrite lt_succ_r; auto.
destruct 1; [|subst; auto]. rewrite <- lt_succ_r; auto.
Qed.

Theorem lt_irrefl : forall n : nat, ~ (n < n).
Proof.
induction n. intro H; inversion H. rewrite lt_succ_r; auto.
Qed.

(** Facts specific to natural numbers, not integers. *)

Theorem pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

(** Recursion fonction *)

Definition recursion {A} : A -> (nat -> A -> A) -> nat -> A :=
  nat_rect (fun _ => A).

Instance recursion_wd {A} (Aeq : relation A) :
 Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) recursion.
Proof.
intros a a' Ha f f' Hf n n' Hn. subst n'.
induction n; simpl; auto. apply Hf; auto.
Qed.

Theorem recursion_0 :
  forall {A} (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem recursion_succ :
  forall {A} (Aeq : relation A) (a : A) (f : nat -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
unfold Proper, respectful in *; induction n; simpl; auto.
Qed.

(** The instantiation of operations.
    Placing them at the very end avoids having indirections in above lemmas. *)

Definition t := nat.
Definition eq := @eq nat.
Definition eqb := beq_nat.
Definition compare := nat_compare.
Definition zero := 0.
Definition one := 1.
Definition two := 2.
Definition succ := S.
Definition pred := pred.
Definition add := plus.
Definition sub := minus.
Definition mul := mult.
Definition lt := lt.
Definition le := le.

Definition min := min.
Definition max := max.
Definition max_l := max_l.
Definition max_r := max_r.
Definition min_l := min_l.
Definition min_r := min_r.

Definition eqb_eq := beq_nat_true_iff.
Definition compare_spec := nat_compare_spec.
Definition eq_dec := eq_nat_dec.

Definition Even := Even.
Definition Odd := Odd.
Definition even := even.
Definition odd := odd.
Definition even_spec := even_spec.
Definition odd_spec := odd_spec.

Program Instance pow_wd : Proper (eq==>eq==>eq) pow.
Definition pow_0_r := pow_0_r.
Definition pow_succ_r := pow_succ_r.
Definition pow := pow.

Definition sqrt_spec a (Ha:0<=a) := sqrt_spec a.
Program Instance sqrt_wd : Proper (eq==>eq) sqrt.
Definition sqrt := sqrt.

Definition div := div.
Definition modulo := modulo.
Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.
Definition div_mod := div_mod.
Definition mod_upper_bound := mod_upper_bound.

(** Generic Properties *)

Include NProp
 <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

End Nat.

(** [Nat] contains an [order] tactic for natural numbers *)

(** Note that [Nat.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 Nat.order.
 Qed.
End TestOrder.
