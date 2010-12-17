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
 Bool Peano Peano_dec Compare_dec Plus Mult Minus Le Lt EqNat Div2 Wf_nat
 NAxioms NProperties.

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

Lemma Even_equiv : forall n, Even n <-> Even.even n.
Proof.
 split. intros (p,->). apply Even.even_mult_l. do 3 constructor.
 intros H. destruct (even_2n n H) as (p,->).
 exists p. unfold double. simpl. now rewrite <- plus_n_O.
Qed.

Lemma Odd_equiv : forall n, Odd n <-> Even.odd n.
Proof.
 split. intros (p,->). rewrite <- plus_n_Sm, <- plus_n_O.
 apply Even.odd_S. apply Even.even_mult_l. do 3 constructor.
 intros H. destruct (odd_S2n n H) as (p,->).
 exists p. unfold double. simpl. now rewrite <- plus_n_Sm, <- !plus_n_O.
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

Lemma mod_bound_pos : forall x y, 0<=x -> 0<y -> 0 <= x mod y < y.
Proof.
 intros x y Hx Hy. split. auto with arith.
 destruct y; [ now elim Hy | clear Hy ].
 unfold modulo.
 apply le_n_S, le_minus.
Qed.

(** Square root *)

(** The following square root function is linear (and tail-recursive).
  With Peano representation, we can't do better. For faster algorithm,
  see Psqrt/Zsqrt/Nsqrt...

  We search the square root of n = k + p^2 + (q - r)
  with q = 2p and 0<=r<=q. We start with p=q=r=0, hence
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
 (sqrt n)*(sqrt n) <= n < S (sqrt n) * S (sqrt n).
Proof.
 intros.
 set (s:=sqrt n).
 replace n with (n + 0*0 + (0-0)).
 apply sqrt_iter_spec; auto.
 simpl. now rewrite <- 2 plus_n_O.
Qed.

(** A linear tail-recursive base-2 logarithm

  In [log2_iter], we maintain the logarithm [p] of the counter [q],
  while [r] is the distance between [q] and the next power of 2,
  more precisely [q + S r = 2^(S p)] and [r<2^p]. At each
  recursive call, [q] goes up while [r] goes down. When [r]
  is 0, we know that [q] has almost reached a power of 2,
  and we increase [p] at the next call, while resetting [r]
  to [q].

  Graphically (numbers are [q], stars are [r]) :

<<
                    10
                  9
                8
              7   *
            6       *
          5           ...
        4
      3   *
    2       *
  1   *       *
0   *   *       *
>>

  We stop when [k], the global downward counter reaches 0.
  At that moment, [q] is the number we're considering (since
  [k+q] is invariant), and [p] its logarithm.
*)

Fixpoint log2_iter k p q r :=
  match k with
    | O => p
    | S k' => match r with
                | O => log2_iter k' (S p) (S q) q
                | S r' => log2_iter k' p (S q) r'
              end
  end.

Definition log2 n := log2_iter (pred n) 0 1 0.

Lemma log2_iter_spec : forall k p q r,
 2^(S p) = q + S r -> r < 2^p ->
 let s := log2_iter k p q r in
 2^s <= k + q < 2^(S s).
Proof.
 induction k.
 (* k = 0 *)
 intros p q r EQ LT. simpl log2_iter. cbv zeta.
 split.
 rewrite plus_O_n.
 apply plus_le_reg_l with (2^p).
 simpl pow in EQ. rewrite <- plus_n_O in EQ. rewrite EQ.
 rewrite plus_comm. apply plus_le_compat_r. now apply lt_le_S.
 rewrite EQ, plus_comm. apply plus_lt_compat_l. apply lt_0_Sn.
 (* k = S k' *)
 intros p q r EQ LT. destruct r.
 (* r = 0 *)
 rewrite <- plus_n_Sm, <- plus_n_O in EQ.
 rewrite plus_Sn_m, plus_n_Sm. apply IHk.
 rewrite <- EQ. remember (S p) as p'; simpl. now rewrite <- plus_n_O.
 unfold lt. now rewrite EQ.
 (* r = S r' *)
 rewrite plus_Sn_m, plus_n_Sm. apply IHk.
 now rewrite plus_Sn_m, plus_n_Sm.
 unfold lt.
 now apply lt_le_weak.
Qed.

Lemma log2_spec : forall n, 0<n ->
 2^(log2 n) <= n < 2^(S (log2 n)).
Proof.
 intros.
 set (s:=log2 n).
 replace n with (pred n + 1).
 apply log2_iter_spec; auto.
 rewrite <- plus_n_Sm, <- plus_n_O.
 symmetry. now apply S_pred with 0.
Qed.

Lemma log2_nonpos : forall n, n<=0 -> log2 n = 0.
Proof.
 inversion 1; now subst.
Qed.

(** * Gcd *)

(** We use Euclid algorithm, which is normally not structural,
    but Coq is now clever enough to accept this (behind modulo
    there is a subtraction, which now preserves being a subterm)
*)

Fixpoint gcd a b :=
  match a with
   | O => b
   | S a' => gcd (b mod (S a')) (S a')
  end.

Definition divide x y := exists z, x*z=y.
Notation "( x | y )" := (divide x y) (at level 0) : nat_scope.

Lemma gcd_divide : forall a b, (gcd a b | a) /\ (gcd a b | b).
Proof.
 fix 1.
 intros [|a] b; simpl.
 split.
  exists 0; now rewrite <- mult_n_O.
  exists 1; now rewrite <- mult_n_Sm, <- mult_n_O.
 fold (b mod (S a)).
 destruct (gcd_divide (b mod (S a)) (S a)) as (H,H').
 set (a':=S a) in *.
 split; auto.
 rewrite (div_mod b a') at 2 by discriminate.
 destruct H as (u,Hu), H' as (v,Hv).
 exists ((b/a')*v + u).
 rewrite mult_plus_distr_l.
 now rewrite (mult_comm _ v), mult_assoc, Hv, Hu.
Qed.

Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof.
 intros. apply gcd_divide.
Qed.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof.
 intros. apply gcd_divide.
Qed.

Lemma gcd_greatest : forall a b c, (c|a) -> (c|b) -> (c|gcd a b).
Proof.
 fix 1.
 intros [|a] b; simpl; auto.
 fold (b mod (S a)).
 intros c H H'. apply gcd_greatest; auto.
 set (a':=S a) in *.
 rewrite (div_mod b a') in H' by discriminate.
 destruct H as (u,Hu), H' as (v,Hv).
 exists (v - u * (b/a')).
 now rewrite mult_minus_distr_l, mult_assoc, Hu, Hv, minus_plus.
Qed.

(** * Bitwise operations *)

(** We provide here some bitwise operations for unary numbers.
  Some might be really naive, they are just there for fullfiling
  the same interface as other for natural representations. As
  soon as binary representations such as NArith are available,
  it is clearly better to convert to/from them and use their ops.
*)

Fixpoint testbit a n :=
 match n with
   | O => odd a
   | S n => testbit (div2 a) n
 end.

Definition shiftl a n := iter_nat n _ double a.
Definition shiftr a n := iter_nat n _ div2 a.

Fixpoint bitwise (op:bool->bool->bool) n a b :=
 match n with
  | O => O
  | S n' =>
    (if op (odd a) (odd b) then 1 else 0) +
    2*(bitwise op n' (div2 a) (div2 b))
 end.

Definition land a b := bitwise andb a a b.
Definition lor a b := bitwise orb (max a b) a b.
Definition ldiff a b := bitwise (fun b b' => b && negb b') a a b.
Definition lxor a b := bitwise xorb (max a b) a b.

Lemma double_twice : forall n, double n = 2*n.
Proof.
 simpl; intros. now rewrite <- plus_n_O.
Qed.

Lemma testbit_0_l : forall n, testbit 0 n = false.
Proof.
 now induction n.
Qed.

Lemma testbit_spec : forall a n,
 exists l h, 0<=l<2^n /\
  a = l + ((if testbit a n then 1 else 0) + 2*h)*2^n.
Proof.
 intros a n. revert a. induction n; intros a; simpl testbit.
 exists 0. exists (div2 a).
 split. simpl.  unfold lt. now split.
 case_eq (odd a); intros EQ; simpl.
 rewrite mult_1_r, <- plus_n_O.
  now apply odd_double, Odd_equiv, odd_spec.
 rewrite mult_1_r, <- plus_n_O. apply even_double.
  destruct (Even.even_or_odd a) as [H|H]; trivial.
  apply Odd_equiv, odd_spec in H. rewrite H in EQ; discriminate.
 destruct (IHn (div2 a)) as (l & h & (_,H) & EQ).
 destruct (Even.even_or_odd a) as [EV|OD].
 exists (double l). exists h.
 split. split. apply le_O_n.
 unfold double; simpl. rewrite <- plus_n_O. now apply plus_lt_compat.
 pattern a at 1. rewrite (even_double a EV).
 pattern (div2 a) at 1. rewrite EQ.
 rewrite !double_twice, mult_plus_distr_l. f_equal.
 rewrite mult_assoc, (mult_comm 2), <- mult_assoc. f_equal.
 exists (S (double l)). exists h.
 split. split. apply le_O_n.
 red. red in H.
 unfold double; simpl. rewrite <- plus_n_O, plus_n_Sm, <- plus_Sn_m.
 now apply plus_le_compat.
 rewrite plus_Sn_m.
 pattern a at 1. rewrite (odd_double a OD). f_equal.
 pattern (div2 a) at 1. rewrite EQ.
 rewrite !double_twice, mult_plus_distr_l. f_equal.
 rewrite mult_assoc, (mult_comm 2), <- mult_assoc. f_equal.
Qed.

Lemma shiftr_spec : forall a n m,
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 induction n; intros m. trivial.
 now rewrite <- plus_n_O.
 now rewrite <- plus_n_Sm, <- plus_Sn_m, <- IHn.
Qed.

Lemma shiftl_spec_high : forall a n m, n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 induction n; intros m H. trivial.
 now rewrite <- minus_n_O.
 destruct m. inversion H.
 simpl. apply le_S_n in H.
 change (shiftl a (S n)) with (double (shiftl a n)).
 rewrite double_twice, div2_double. now apply IHn.
Qed.

Lemma shiftl_spec_low : forall a n m, m<n ->
 testbit (shiftl a n) m = false.
Proof.
 induction n; intros m H. inversion H.
 change (shiftl a (S n)) with (double (shiftl a n)).
 destruct m; simpl.
 unfold odd. apply negb_false_iff.
 apply even_spec. exists (shiftl a n). apply double_twice.
 rewrite double_twice, div2_double. apply IHn.
 now apply lt_S_n.
Qed.

Lemma div2_bitwise : forall op n a b,
 div2 (bitwise op (S n) a b) = bitwise op n (div2 a) (div2 b).
Proof.
 intros. unfold bitwise; fold bitwise.
 destruct (op (odd a) (odd b)).
 now rewrite div2_double_plus_one.
 now rewrite plus_O_n, div2_double.
Qed.

Lemma odd_bitwise : forall op n a b,
 odd (bitwise op (S n) a b) = op (odd a) (odd b).
Proof.
 intros. unfold bitwise; fold bitwise.
 destruct (op (odd a) (odd b)).
 apply odd_spec. rewrite plus_comm. eexists; eauto.
 unfold odd. apply negb_false_iff. apply even_spec.
 rewrite plus_O_n; eexists; eauto.
Qed.

Lemma div2_decr : forall a n, a <= S n -> div2 a <= n.
Proof.
 destruct a; intros. apply le_0_n.
 apply le_trans with a.
 apply lt_n_Sm_le, lt_div2, lt_0_Sn. now apply le_S_n.
Qed.

Lemma testbit_bitwise_1 : forall op, (forall b, op false b = false) ->
 forall n m a b, a<=n ->
 testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
Proof.
 intros op Hop.
 induction n; intros m a b Ha.
 simpl. inversion Ha; subst. now rewrite testbit_0_l.
 destruct m.
 apply odd_bitwise.
 unfold testbit; fold testbit. rewrite div2_bitwise.
 apply IHn; now apply div2_decr.
Qed.

Lemma testbit_bitwise_2 : forall op, op false false = false ->
 forall n m a b, a<=n -> b<=n ->
 testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
Proof.
 intros op Hop.
 induction n; intros m a b Ha Hb.
 simpl. inversion Ha; inversion Hb; subst. now rewrite testbit_0_l.
 destruct m.
 apply odd_bitwise.
 unfold testbit; fold testbit. rewrite div2_bitwise.
 apply IHn; now apply div2_decr.
Qed.

Lemma land_spec : forall a b n,
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 intros. unfold land. apply testbit_bitwise_1; trivial.
Qed.

Lemma ldiff_spec : forall a b n,
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 intros. unfold ldiff. apply testbit_bitwise_1; trivial.
Qed.

Lemma lor_spec : forall a b n,
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 intros. unfold lor. apply testbit_bitwise_2. trivial.
 destruct (le_ge_dec a b). now rewrite max_r. now rewrite max_l.
 destruct (le_ge_dec a b). now rewrite max_r. now rewrite max_l.
Qed.

Lemma lxor_spec : forall a b n,
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 intros. unfold lxor. apply testbit_bitwise_2. trivial.
 destruct (le_ge_dec a b). now rewrite max_r. now rewrite max_l.
 destruct (le_ge_dec a b). now rewrite max_r. now rewrite max_l.
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
Lemma pow_neg_r : forall a b, b<0 -> a^b = 0. inversion 1. Qed.
Definition pow := pow.

Definition log2_spec := log2_spec.
Definition log2_nonpos := log2_nonpos.
Definition log2 := log2.

Definition sqrt_spec a (Ha:0<=a) := sqrt_spec a.
Lemma sqrt_neg : forall a, a<0 -> sqrt a = 0. inversion 1. Qed.
Definition sqrt := sqrt.

Definition div := div.
Definition modulo := modulo.
Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.
Definition div_mod := div_mod.
Definition mod_bound_pos := mod_bound_pos.

Definition divide := divide.
Definition gcd := gcd.
Definition gcd_divide_l := gcd_divide_l.
Definition gcd_divide_r := gcd_divide_r.
Definition gcd_greatest := gcd_greatest.
Lemma gcd_nonneg : forall a b, 0<=gcd a b.
Proof. intros. apply le_O_n. Qed.

Definition testbit := testbit.
Definition shiftl := shiftl.
Definition shiftr := shiftr.
Definition lxor := lxor.
Definition land := land.
Definition lor := lor.
Definition ldiff := ldiff.
Definition div2 := div2.

Definition testbit_spec a n (_:0<=n) := testbit_spec a n.
Lemma testbit_neg_r a n (H:n<0) : testbit a n = false.
Proof. inversion H. Qed.
Definition shiftl_spec_low := shiftl_spec_low.
Definition shiftl_spec_high a n m (_:0<=m) := shiftl_spec_high a n m.
Definition shiftr_spec a n m (_:0<=m) := shiftr_spec a n m.
Definition lxor_spec := lxor_spec.
Definition land_spec := land_spec.
Definition lor_spec := lor_spec.
Definition ldiff_spec := ldiff_spec.
Definition div2_spec a : div2 a = shiftr a 1 := eq_refl _.

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
