(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NAxioms NProperties OrdersFacts DecidableClass.

(** Implementation of [NAxiomsSig] by [nat] *)

Module Nat
  <: NAxiomsSig
  <: UsualDecidableTypeFull
  <: OrderedTypeFull
  <: TotalOrder.

(** Operations over [nat] are defined in a separate module *)

Include Corelib.Init.Nat.

(** When including property functors, inline t eq zero one two lt le succ *)

Set Inline Level 50.

(** All operations are well-defined (trivial here since eq is Leibniz) *)

Definition eq_equiv : Equivalence (@eq nat) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
#[global] Program Instance succ_wd : Proper (eq==>eq) S.
#[global] Program Instance pred_wd : Proper (eq==>eq) pred.
#[global] Program Instance add_wd : Proper (eq==>eq==>eq) plus.
#[global] Program Instance sub_wd : Proper (eq==>eq==>eq) minus.
#[global] Program Instance mul_wd : Proper (eq==>eq==>eq) mult.
#[global] Program Instance pow_wd : Proper (eq==>eq==>eq) pow.
#[global] Program Instance div_wd : Proper (eq==>eq==>eq) div.
#[global] Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.
#[global] Program Instance lt_wd : Proper (eq==>eq==>iff) lt.
#[global] Program Instance testbit_wd : Proper (eq==>eq==>eq) testbit.

(** Bi-directional induction. *)

Theorem bi_induction :
  forall A : nat -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
  intros A A_wd A0 AS; apply nat_ind.
  - assumption.
  - intros; now apply -> AS.
Qed.

(** Recursion function *)

Definition recursion {A} : A -> (nat -> A -> A) -> nat -> A :=
  nat_rect (fun _ => A).

#[global] Instance recursion_wd {A} (Aeq : relation A) :
  Proper (Aeq ==> (eq==>Aeq==>Aeq) ==> eq ==> Aeq) recursion.
Proof.
  intros a a' Ha f f' Hf n n' <-.
  induction n; simpl; auto.
  apply Hf; auto.
Qed.

Theorem recursion_0 :
  forall {A} (a : A) (f : nat -> A -> A), recursion a f 0 = a.
Proof. reflexivity. Qed.

Theorem recursion_succ :
  forall {A} (Aeq : relation A) (a : A) (f : nat -> A -> A),
    Aeq a a -> Proper (eq==>Aeq==>Aeq) f ->
      forall n : nat, Aeq (recursion a f (S n)) (f n (recursion a f n)).
Proof.
  unfold Proper, respectful in *.
  intros A Aeq a f ? ? n.
  induction n; simpl; auto.
Qed.

(** ** Remaining constants not defined in Stdlib.Init.Nat *)

(** NB: Aliasing [le] is mandatory, since only a Definition can implement
    an interface Parameter... *)

Definition eq := @Logic.eq nat.
Definition le := Peano.le.
Definition lt := Peano.lt.

(** ** Basic specifications : pred add sub mul *)

Lemma pred_succ n : pred (S n) = n.
Proof. reflexivity. Qed.

Lemma pred_0 : pred 0 = 0.
Proof. reflexivity. Qed.

Lemma one_succ : 1 = S 0.
Proof. reflexivity. Qed.

Lemma two_succ : 2 = S 1.
Proof. reflexivity. Qed.

Lemma add_0_l n : 0 + n = n.
Proof. reflexivity. Qed.

Lemma add_succ_l n m : (S n) + m = S (n + m).
Proof. reflexivity. Qed.

Lemma sub_0_r n : n - 0 = n.
Proof. now destruct n. Qed.

Lemma sub_succ_r n m : n - (S m) = pred (n - m).
Proof.
  revert m; induction n; intro m; destruct m; simpl; auto.
  apply sub_0_r.
Qed.

Lemma mul_0_l n : 0 * n = 0.
Proof. reflexivity. Qed.

Lemma mul_succ_l n m : S n * m = n * m + m.
Proof.
  assert (succ_r : forall x y, x+S y = S(x+y)) by now intro x; induction x.
  assert (comm : forall x y, x+y = y+x).
  { intro x; induction x; simpl; auto.
    intros; rewrite succ_r; now f_equal. }
  now rewrite comm.
Qed.

Lemma lt_succ_r n m : n < S m <-> n <= m.
Proof.
  split.
  - apply Peano.le_S_n.
  - induction 1; auto.
Qed.

(** ** Boolean comparisons *)

Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; simpl; rewrite ?IHn; split; try easy.
  - now intros ->.
  - now injection 1.
Qed.

#[global]
Instance Decidable_eq_nat : forall (x y : nat), Decidable (eq x y) := {
  Decidable_spec := Nat.eqb_eq x y
}.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
  revert m.
  induction n as [|n IHn]; intro m; destruct m; simpl.
  - now split.
  - split; trivial.
    intros; apply Peano.le_0_n.
  - now split.
  - rewrite IHn; split.
    + apply Peano.le_n_S.
    + apply Peano.le_S_n.
Qed.

#[global]
Instance Decidable_le_nat : forall (x y : nat), Decidable (x <= y) := {
  Decidable_spec := Nat.leb_le x y
}.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof. apply leb_le. Qed.

(* Note: Decidable_lt_nat, Decidable_ge_nat, Decidable_gt_nat are not required,
   because lt, ge and gt are defined based on le in a way which type class
   resolution seems to understand. *)

(** ** Decidability of equality over [nat]. *)

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intro n; induction n as [|n IHn]; intro m; destruct m as [|m].
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.

(** ** Ternary comparison *)

(** With [nat], it would be easier to prove first [compare_spec],
    then the properties below. But then we wouldn't be able to
    benefit from functor [BoolOrderFacts] *)

Lemma compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof.
  revert m; induction n as [|n IHn]; intro m; destruct m;
  simpl; rewrite ?IHn; split; auto; easy.
Qed.

Lemma compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof.
  revert m; induction n as [|n IHn]; intro m; destruct m;
  simpl; rewrite ?IHn; split; try easy.
  - intros _; apply Peano.le_n_S, Peano.le_0_n.
  - apply Peano.le_n_S.
  - apply Peano.le_S_n.
Qed.

Lemma compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof.
  revert m; induction n as [|n IHn]; intro m; destruct m; simpl; rewrite ?IHn.
  - now split.
  - split; intros.
    + apply Peano.le_0_n.
    + easy.
  - split.
    + now destruct 1.
    + inversion 1.
  - split; intros.
    + now apply Peano.le_n_S.
    + now apply Peano.le_S_n.
Qed.

Lemma compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof. revert m; induction n; intro m; destruct m; simpl; trivial. Qed.

Lemma compare_succ n m : (S n ?= S m) = (n ?= m).
Proof. reflexivity. Qed.


(** ** Minimum, maximum *)

Lemma max_l : forall n m, m <= n -> max n m = n.
Proof. exact Peano.max_l. Qed.

Lemma max_r : forall n m, n <= m -> max n m = m.
Proof. exact Peano.max_r. Qed.

Lemma min_l : forall n m, n <= m -> min n m = n.
Proof. exact Peano.min_l. Qed.

Lemma min_r : forall n m, m <= n -> min n m = m.
Proof. exact Peano.min_r. Qed.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include NBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

Lemma strong_induction_le (A : nat -> Prop) :
  A 0 -> (forall n, (forall m, m <= n -> A m) -> A (S n)) -> forall n, A n.
Proof. apply Private_strong_induction_le; intros x y ->; reflexivity. Qed.

(** ** Power *)

Lemma pow_neg_r a b : b<0 -> a^b = 0.
Proof. inversion 1. Qed.

Lemma pow_0_r a : a^0 = 1.
Proof. reflexivity. Qed.

Lemma pow_succ_r a b : 0<=b -> a^(S b) = a * a^b.
Proof. reflexivity. Qed.

(** ** Square *)

Lemma square_spec n : square n = n * n.
Proof. reflexivity. Qed.

(** ** Parity *)

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

Module Private_Parity.

Lemma Even_0 : Even 0.
Proof. exists 0; reflexivity. Qed.

Lemma Even_1 : ~ Even 1.
Proof.
  intros ([|], H); try discriminate.
  simpl in H.
  now rewrite <- plus_n_Sm in H.
Qed.

Lemma Even_2 n : Even n <-> Even (S (S n)).
Proof.
  split; intros (m,H).
  - exists (S m).
    rewrite H; simpl.
    now rewrite plus_n_Sm.
  - destruct m as [|m]; try discriminate.
    exists m.
    simpl in H; rewrite <- plus_n_Sm in H.
    now inversion H.
Qed.

Lemma Odd_0 : ~ Odd 0.
Proof. now intros ([|], H). Qed.

Lemma Odd_1 : Odd 1.
Proof. exists 0; reflexivity. Qed.

Lemma Odd_2 n : Odd n <-> Odd (S (S n)).
Proof.
  split; intros (m,H).
  - exists (S m).
    rewrite H. simpl.
    now rewrite <- (plus_n_Sm m).
  - destruct m as [|m]; try discriminate.
    exists m.
    simpl in H; rewrite <- plus_n_Sm in H.
    inversion H; simpl.
    now rewrite <- !plus_n_Sm, <- !plus_n_O.
Qed.

End Private_Parity.
Import Private_Parity.

Lemma even_spec : forall n, even n = true <-> Even n.
Proof.
  fix even_spec 1.
    intro n; destruct n as [|[|n]]; simpl.
    - split; [ intros; apply Even_0  | trivial ].
    - split; [ discriminate | intro H; elim (Even_1 H) ].
    - rewrite even_spec.
      apply Even_2.
Qed.

Lemma odd_spec : forall n, odd n = true <-> Odd n.
Proof.
  unfold odd.
  fix odd_spec 1.
    intro n; destruct n as [|[|n]]; simpl.
    - split; [ discriminate | intro H; elim (Odd_0 H) ].
    - split; [ intros; apply Odd_1 | trivial ].
    - rewrite odd_spec.
      apply Odd_2.
Qed.

(** ** Division *)

Lemma divmod_spec : forall x y q u, u <= y ->
  let (q',u') := divmod x y q u in
  x + (S y)*q + (y-u) = (S y)*q' + (y-u') /\ u' <= y.
Proof.
  intro x; induction x as [|x IHx].
  - simpl; intuition.
  - intros y q u H.
    destruct u as [|u]; simpl divmod.
    + generalize (IHx y (S q) y (le_n y)).
      destruct divmod as (q',u').
      intros (EQ,LE); split; trivial.
      rewrite <- EQ, sub_0_r, sub_diag, add_0_r.
      now rewrite !add_succ_l, <- add_succ_r, <- add_assoc, mul_succ_r.
    + assert (H' : u <= y).
      { apply le_trans with (S u); trivial.
        do 2 constructor. }
      generalize (IHx y q u H').
      destruct divmod as (q',u').
      intros (EQ,LE); split; trivial.
      rewrite <- EQ, !add_succ_l, <- add_succ_r; f_equal.
      now rewrite <- sub_succ_l.
Qed.

Lemma div_mod_eq x y : x = y*(x/y) + x mod y.
Proof.
  destruct y as [|y]; [reflexivity | ].
  unfold div, modulo.
  generalize (divmod_spec x y 0 y (le_n y)).
  destruct divmod as (q,u).
  intros (U,V).
  simpl in *.
  now rewrite mul_0_r, sub_diag, !add_0_r in U.
Qed.

(** The [y <> 0] hypothesis is needed to fit in [NAxiomsSig]. *)
Lemma div_mod x y : y <> 0 -> x = y*(x/y) + x mod y.
Proof.
  intros _; apply div_mod_eq.
Qed.

Lemma mod_bound_pos x y : 0<=x -> 0<y -> 0 <= x mod y < y.
Proof.
  intros Hx Hy.
  split.
  - apply le_0_l.
  - destruct y; [ now elim Hy | clear Hy ].
    unfold modulo.
    apply lt_succ_r, le_sub_l.
Qed.

(** ** Square root *)

Lemma sqrt_iter_spec : forall k p q r,
  q = p+p -> r<=q ->
  let s := sqrt_iter k p q r in
  s*s <= k + p*p + (q - r) < (S s)*(S s).
Proof.
  intro k; induction k as [|k IHk].
  - (* k = 0 *)
    simpl; intros p q r Hq Hr.
    split.
    + apply le_add_r.
    + apply lt_succ_r.
      rewrite mul_succ_r, add_assoc, (add_comm p), <- add_assoc.
      apply add_le_mono_l.
      rewrite <- Hq.
      apply le_sub_l.
  - (* k = S k' *)
    intros p q r; destruct r as [|r].
    + (* r = 0 *)
      intros Hq _.
      replace (S k + p*p + (q-0)) with (k + (S p)*(S p) + (S (S q) - S (S q))).
      2:{ rewrite sub_diag, sub_0_r, add_0_r. simpl.
          rewrite add_succ_r; f_equal. rewrite <- add_assoc; f_equal.
          rewrite mul_succ_r, (add_comm p), <- add_assoc. now f_equal. }
      apply IHk; simpl.
      * now rewrite add_succ_r, Hq.
      * apply le_n.
    + (* r = S r' *)
      intros Hq Hr.
      replace (S k + p*p + (q-S r)) with (k + p*p + (q - r))
        by (simpl; rewrite <- add_succ_r; f_equal; rewrite <- sub_succ_l; trivial).
      apply IHk; trivial.
      apply le_trans with (S r); trivial.
      do 2 constructor.
Qed.

Lemma sqrt_specif n : (sqrt n)*(sqrt n) <= n < S (sqrt n) * S (sqrt n).
Proof.
  set (s:=sqrt n).
  replace n with (n + 0*0 + (0-0)).
  - apply sqrt_iter_spec; auto.
  - simpl.
    now rewrite !add_0_r.
Qed.

Definition sqrt_spec a (Ha:0<=a) := sqrt_specif a.

Lemma sqrt_neg a : a<0 -> sqrt a = 0.
Proof. inversion 1. Qed.

(** ** Logarithm *)

Lemma log2_iter_spec : forall k p q r,
  2^(S p) = q + S r -> r < 2^p ->
  let s := log2_iter k p q r in
  2^s <= k + q < 2^(S s).
Proof.
  intro k; induction k as [|k IHk].
  - (* k = 0 *)
    intros p q r EQ LT.
    simpl log2_iter; cbv zeta.
    split.
    + rewrite add_0_l, (add_le_mono_l _ _ (2^p)).
      simpl pow in EQ.
      rewrite add_0_r in EQ; rewrite EQ, add_comm.
      apply add_le_mono_r, LT.
    + rewrite EQ, add_comm.
      apply add_lt_mono_l.
      apply lt_succ_r, le_0_l.
  - (* k = S k' *)
    intros p q r EQ LT.
    destruct r as [|r].
    + (* r = 0 *)
      rewrite add_succ_r, add_0_r in EQ.
      rewrite add_succ_l, <- add_succ_r.
      apply IHk.
      * rewrite <- EQ.
        remember (S p) as p'; simpl.
        now rewrite add_0_r.
      * rewrite EQ; constructor.
    + (* r = S r' *)
      rewrite add_succ_l, <- add_succ_r.
      apply IHk.
      * now rewrite add_succ_l, <- add_succ_r.
      * apply le_lt_trans with (S r); trivial.
        do 2 constructor.
Qed.

Lemma log2_spec n : 0<n ->
  2^(log2 n) <= n < 2^(S (log2 n)).
Proof.
  intros.
  set (s:=log2 n).
  replace n with (pred n + 1).
  - apply log2_iter_spec; auto.
  - rewrite add_1_r.
    apply succ_pred.
    now apply neq_sym, lt_neq.
Qed.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof. inversion 1; now subst. Qed.

(** ** Properties of [iter] *)

Lemma iter_swap_gen A B (f:A -> B) (g:A -> A) (h:B -> B) :
 (forall a, f (g a) = h (f a)) -> forall n a,
 f (iter n g a) = iter n h (f a).
Proof.
  intros H n a.
  induction n as [|n Hn].
  - reflexivity.
  - simpl. rewrite H, Hn. reflexivity.
Qed.

Lemma iter_swap :
  forall n (A:Type) (f:A -> A) (x:A),
    iter n f (f x) = f (iter n f x).
Proof.
 intros. symmetry. now apply iter_swap_gen.
Qed.

Lemma iter_succ :
  forall n (A:Type) (f:A -> A) (x:A),
    iter (S n) f x = f (iter n f x).
Proof.
  reflexivity.
Qed.

Lemma iter_succ_r :
  forall n (A:Type) (f:A -> A) (x:A),
    iter (S n) f x = iter n f (f x).
Proof.
 intros; now rewrite iter_succ, iter_swap.
Qed.

Lemma iter_add :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter (p+q) f x = iter p f (iter q f x).
Proof.
  intro p. induction p as [|p IHp].
  - reflexivity.
  - intros q A f x. simpl. now rewrite IHp.
Qed.

Lemma iter_ind (A:Type) (f:A -> A) (a:A) (P:nat -> A -> Prop) :
    P 0 a ->
    (forall n a', P n a' -> P (S n) (f a')) ->
    forall n, P n (iter n f a).
Proof.
  intros H0 HS n. induction n as [|n Hn].
  - exact H0.
  - apply HS. exact Hn.
Qed.

Lemma iter_rect (A:Type) (f:A -> A) (a:A) (P:nat -> A -> Type) :
    P 0 a ->
    (forall n a', P n a' -> P (S n) (f a')) ->
    forall n, P n (iter n f a).
Proof.
  intros H0 HS n. induction n as [|n Hn].
  - exact H0.
  - apply HS. exact Hn.
Defined.

Lemma iter_invariant :
  forall (n:nat) (A:Type) (f:A -> A) (Inv:A -> Prop),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter n f x).
Proof.
 intros; apply iter_ind; trivial.
Qed.

(** ** Gcd *)

Definition divide x y := exists z, y=z*x.
Notation "( x | y )" := (divide x y) (at level 0) : nat_scope.

Lemma gcd_divide : forall a b, (gcd a b | a) /\ (gcd a b | b).
Proof.
  fix gcd_divide 1.
    intros [|a] b; simpl.
    - split.
      + now exists 0.
      + exists 1; simpl.
        now rewrite <- plus_n_O.
    - fold (b mod (S a)).
      destruct (gcd_divide (b mod (S a)) (S a)) as (H,H').
      set (a':=S a) in *.
      split; auto.
      rewrite (div_mod_eq b a') at 2.
      destruct H as (u,Hu), H' as (v,Hv).
      rewrite mul_comm.
      exists ((b/a')*v + u).
      rewrite mul_add_distr_r.
      now rewrite <- mul_assoc, <- Hv, <- Hu.
Qed.

Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof. apply gcd_divide. Qed.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof. apply gcd_divide. Qed.

Lemma gcd_greatest : forall a b c, (c|a) -> (c|b) -> (c|gcd a b).
Proof.
  fix gcd_greatest 1.
    intros [|a] b; simpl; auto.
    fold (b mod (S a)).
    intros c H H'.
    apply gcd_greatest; auto.
    set (a':=S a) in *.
    rewrite (div_mod_eq b a') in H'.
    destruct H as (u,Hu), H' as (v,Hv).
    exists (v - (b/a')*u).
    rewrite mul_comm in Hv.
    rewrite mul_sub_distr_r, <- Hv, <- mul_assoc, <-Hu.
    now rewrite add_comm, add_sub.
Qed.

Lemma gcd_nonneg a b : 0<=gcd a b.
Proof. apply le_0_l. Qed.


(** ** Bitwise operations *)

Definition double_S : forall n, double (S n) = S (S (double n))
                    := fun n => add_succ_r (S n) n.

Definition double_add : forall n m, double (n + m) = double n + double m
                      := fun n m => add_shuffle1 n m n m.

Lemma double_twice : forall n, double n = 2*n.
Proof. simpl; intros; now rewrite add_0_r. Qed.

(* We use a Module Type to hide intermediate lemmas we will get from Natural
   anyway. *)
Module Type PrivateBitwiseSpec.
  (* needed to implement Numbers.NatInt.NZBitsSpec *)
  Parameter testbit_odd_0 : forall a : nat, testbit (add (mul 2 a) 1) 0 = true.
  Parameter testbit_even_0 : forall a : nat, testbit (mul 2 a) 0 = false.
  Parameter testbit_odd_succ : forall a n : nat, le 0 n ->
    testbit (add (mul 2 a) 1) (succ n) = testbit a n.
  Parameter testbit_even_succ : forall a n : nat, le 0 n ->
    testbit (mul 2 a) (succ n) = testbit a n.
  Parameter testbit_neg_r : forall a n : nat, lt n 0 -> testbit a n = false.
  Parameter shiftr_spec : forall a n m : nat, le 0 m ->
    testbit (shiftr a n) m = testbit a (add m n).
  Parameter shiftl_spec_high :
    forall a n m : nat, le 0 m ->
    le n m -> testbit (shiftl a n) m = testbit a (sub m n).
  Parameter shiftl_spec_low :
    forall a n m : nat, lt m n -> testbit (shiftl a n) m = false.
  Parameter land_spec :
    forall a b n : nat, testbit (land a b) n = testbit a n && testbit b n.
  Parameter lor_spec :
    forall a b n : nat, testbit (lor a b) n = testbit a n || testbit b n.
  Parameter ldiff_spec :
    forall a b n : nat,
    testbit (ldiff a b) n = testbit a n && negb (testbit b n).
  Parameter lxor_spec :
    forall a b n : nat, testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
  Parameter div2_spec :
    forall a : nat, eq (div2 a) (shiftr a 1).
  (* not yet generalized to Numbers.Natural.Abstract *)
  Parameter div2_double : forall n, div2 (2*n) = n.
  Parameter div2_succ_double : forall n, div2 (S (2*n)) = n.
  Parameter div2_bitwise : forall op n a b,
    div2 (bitwise op (S n) a b) = bitwise op n (div2 a) (div2 b).
  Parameter odd_bitwise : forall op n a b,
    odd (bitwise op (S n) a b) = op (odd a) (odd b).
  Parameter testbit_bitwise_1 : forall op, (forall b, op false b = false) ->
    forall n m a b, a<=n ->
    testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
  Parameter testbit_bitwise_2 : forall op, op false false = false ->
    forall n m a b, a<=n -> b<=n ->
    testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
End PrivateBitwiseSpec.

(* The following module has to be included (it semmes that importing it is not
   enough to implement NZBitsSpec), therefore it has to be "Private", otherwise,
   its lemmas will appear twice in [Search]es *)

Module PrivateImplementsBitwiseSpec : PrivateBitwiseSpec.

Lemma div2_double n : div2 (2*n) = n.
Proof.
  induction n; trivial.
  simpl mul.
  rewrite add_succ_r; simpl.
  now f_equal.
Qed.

Lemma div2_succ_double n : div2 (S (2*n)) = n.
Proof.
  induction n; trivial.
  simpl; f_equal.
  now rewrite add_succ_r.
Qed.

Lemma le_div2 n : div2 (S n) <= n.
Proof.
  revert n.
  fix le_div2 1.
    intro n; destruct n as [|n]; simpl; trivial.
    apply lt_succ_r.
    destruct n; [simpl|]; trivial.
    now constructor.
Qed.

Lemma lt_div2 n : 0 < n -> div2 n < n.
Proof.
  destruct n.
  - inversion 1.
  - intros _; apply lt_succ_r, le_div2.
Qed.

Lemma div2_decr a n : a <= S n -> div2 a <= n.
Proof.
  destruct a as [|a]; intros H.
  - simpl; apply le_0_l.
  - apply succ_le_mono in H.
    apply le_trans with a; [ apply le_div2 | trivial ].
Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma testbit_0_l : forall n, testbit 0 n = false.
Proof. now intro n; induction n. Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof. unfold testbit; rewrite odd_spec; now exists a. Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof.
  unfold testbit, odd.
  rewrite (proj2 (even_spec _)); trivial.
  now exists a.
Qed.

Lemma testbit_odd_succ' a n : testbit (2*a+1) (S n) = testbit a n.
Proof.
  unfold testbit; fold testbit.
  rewrite add_1_r; f_equal.
  apply div2_succ_double.
Qed.

Lemma testbit_even_succ' a n : testbit (2*a) (S n) = testbit a n.
Proof. unfold testbit; fold testbit; f_equal; apply div2_double. Qed.

Lemma shiftr_specif : forall a n m,
  testbit (shiftr a n) m = testbit a (m+n).
Proof.
  intros a n; induction n as [|n IHn]; intros m.
  - now rewrite add_0_r.
  - now rewrite add_succ_r, <- add_succ_l, <- IHn.
Qed.

Lemma shiftl_specif_high : forall a n m, n<=m ->
  testbit (shiftl a n) m = testbit a (m-n).
Proof.
  intros a n; induction n as [|n IHn]; intros m H; [ trivial | ].
  - now rewrite sub_0_r.
  - destruct m; [ inversion H | ].
    simpl; apply succ_le_mono in H.
    change (shiftl a (S n)) with (double (shiftl a n)).
    rewrite double_twice, div2_double.
    now apply IHn.
Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma shiftl_spec_low : forall a n m, m<n ->
  testbit (shiftl a n) m = false.
Proof.
  intros a n; induction n as [|n IHn]; intros m H; [ inversion H | ].
  change (shiftl a (S n)) with (double (shiftl a n)).
  destruct m; simpl.
  - unfold odd; apply negb_false_iff.
    apply even_spec.
    exists (shiftl a n).
    apply double_twice.
  - rewrite double_twice, div2_double.
    apply IHn.
    now apply succ_le_mono.
Qed.

(* not yet generalized, part of the interface at this point *)
Lemma div2_bitwise : forall op n a b,
  div2 (bitwise op (S n) a b) = bitwise op n (div2 a) (div2 b).
Proof.
  intros op n a b; unfold bitwise; fold bitwise.
  destruct (op (odd a) (odd b)).
  - now rewrite div2_succ_double.
  - now rewrite add_0_l, div2_double.
Qed.

(* not yet generalized, part of the interface at this point *)
Lemma odd_bitwise : forall op n a b,
  odd (bitwise op (S n) a b) = op (odd a) (odd b).
Proof.
  intros op n a b; unfold bitwise; fold bitwise.
  destruct (op (odd a) (odd b)).
  - apply odd_spec.
    rewrite add_comm; eexists; eauto.
  - unfold odd; apply negb_false_iff.
    apply even_spec.
    rewrite add_0_l; eexists; eauto.
Qed.

(* not yet generalized, part of the interface at this point *)
Lemma testbit_bitwise_1 : forall op, (forall b, op false b = false) ->
  forall n m a b, a<=n ->
  testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
Proof.
  intros op Hop.
  intro n; induction n as [|n IHn]; intros m a b Ha.
  - simpl; inversion Ha; subst.
    now rewrite testbit_0_l.
  - destruct m.
    + apply odd_bitwise.
    + unfold testbit; fold testbit; rewrite div2_bitwise.
      apply IHn; now apply div2_decr.
Qed.

(* not yet generalized, part of the interface at this point *)
Lemma testbit_bitwise_2 : forall op, op false false = false ->
  forall n m a b, a<=n -> b<=n ->
  testbit (bitwise op n a b) m = op (testbit a m) (testbit b m).
Proof.
  intros op Hop.
  intro n; induction n as [|n IHn]; intros m a b Ha Hb.
  - simpl; inversion Ha; inversion Hb; subst.
    now rewrite testbit_0_l.
  - destruct m.
    + apply odd_bitwise.
    + unfold testbit; fold testbit; rewrite div2_bitwise.
      apply IHn; now apply div2_decr.
Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma land_spec a b n :
  testbit (land a b) n = testbit a n && testbit b n.
Proof. unfold land; apply testbit_bitwise_1; trivial. Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma ldiff_spec a b n :
  testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof. unfold ldiff; apply testbit_bitwise_1; trivial. Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma lor_spec a b n :
  testbit (lor a b) n = testbit a n || testbit b n.
Proof.
  unfold lor; apply testbit_bitwise_2.
  - trivial.
  - destruct (compare_spec a b) as [H|H|H].
    + rewrite max_l; subst; trivial.
    + now apply lt_le_incl in H; rewrite max_r.
    + now apply lt_le_incl in H; rewrite max_l.
  - destruct (compare_spec a b) as [H|H|H].
    + rewrite max_r; subst; trivial.
    + now apply lt_le_incl in H; rewrite max_r.
    + now apply lt_le_incl in H; rewrite max_l.
Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma lxor_spec a b n :
  testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
  unfold lxor; apply testbit_bitwise_2.
  - trivial.
  - destruct (compare_spec a b) as [H|H|H].
    + rewrite max_l; subst; trivial.
    + now apply lt_le_incl in H; rewrite max_r.
    + now apply lt_le_incl in H; rewrite max_l.
  - destruct (compare_spec a b) as [H|H|H].
    + rewrite max_r; subst; trivial.
    + now apply lt_le_incl in H; rewrite max_r.
    + now apply lt_le_incl in H; rewrite max_l.
Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma div2_spec a : div2 a = shiftr a 1.
Proof. reflexivity. Qed.

(** Aliases with extra dummy hypothesis, to fulfil the interface *)

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Definition testbit_odd_succ a n (_:0<=n) := testbit_odd_succ' a n.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Definition testbit_even_succ a n (_:0<=n) := testbit_even_succ' a n.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Lemma testbit_neg_r a n (H:n<0) : testbit a n = false.
Proof. inversion H. Qed.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Definition shiftl_spec_high a n m (_:0<=m) := shiftl_specif_high a n m.

(* needed to implement Stdlib.Numbers.NatInt.NZBitsSpec *)
Definition shiftr_spec a n m (_:0<=m) := shiftr_specif a n m.
End PrivateImplementsBitwiseSpec.
Include PrivateImplementsBitwiseSpec.

Lemma div_0_r a : a / 0 = 0.
Proof. reflexivity. Qed.

Lemma mod_0_r a : a mod 0 = a.
Proof. reflexivity. Qed.

(** Properties of advanced functions (pow, sqrt, log2, ...) *)

Include NExtraPreProp <+ NExtraProp0.

Lemma binary_induction (A : nat -> Prop) :
  A 0 -> (forall n, A n -> A (2 * n)) -> (forall n, A n -> A (2 * n + 1))
  -> forall n, A n.
Proof. apply Private_binary_induction; intros x y ->; reflexivity. Qed.

(** Properties of tail-recursive addition and multiplication *)

Lemma tail_add_spec n m : tail_add n m = n + m.
Proof.
  revert m; induction n as [|n IH]; simpl; trivial; intros.
  now rewrite IH, add_succ_r.
Qed.

Lemma tail_addmul_spec r n m : tail_addmul r n m = r + n * m.
Proof.
  revert m r; induction n as [| n IH]; simpl; trivial; intros.
  rewrite IH, tail_add_spec.
  rewrite add_assoc.
  f_equal; apply add_comm.
Qed.

Lemma tail_mul_spec n m : tail_mul n m = n * m.
Proof. unfold tail_mul; now rewrite tail_addmul_spec. Qed.

(** Additional results about [Even] and [Odd] *)

Definition Even_Odd_dec n : {Even n} + {Odd n}.
Proof.
  induction n as [|n IHn].
  - left; apply Even_0.
  - elim IHn; intros.
    + right; apply Even_succ, Even_succ_succ; assumption.
    + left; apply Odd_succ, Odd_succ_succ; assumption.
Defined.

Lemma Even_add_split n m :
  Even (n + m) -> Even n /\ Even m \/ Odd n /\ Odd m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_split n m :
  Odd (n + m) -> Odd n /\ Even m \/ Even n /\ Odd m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Even_Even_add n m: Even n -> Even m -> Even (n + m).
Proof. rewrite <- ? even_spec, even_add; do 2 destruct even; auto. Qed.

Lemma Odd_add_l n m : Odd n -> Even m -> Odd (n + m).
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_r n m : Even n -> Odd m -> Odd (n + m).
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_Odd_add n m : Odd n -> Odd m -> Even (n + m).
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Even_add_aux n m :
  (Odd (n + m) <-> Odd n /\ Even m \/ Even n /\ Odd m) /\
  (Even (n + m) <-> Even n /\ Even m \/ Odd n /\ Odd m).
Proof.
  split; split.
  - apply Odd_add_split.
  - intros [[HO HE]|[HE HO]]; [ apply Odd_add_l | apply Odd_add_r ]; assumption.
  - apply Even_add_split.
  - intros [[HO HE]|[HE HO]]; [ apply Even_Even_add | apply Odd_Odd_add ]; assumption.
Qed.

Lemma Even_add_Even_inv_r n m : Even (n + m) -> Even n -> Even m.
Proof. rewrite <- ? even_spec, even_add; do 2 destruct even; auto. Qed.

Lemma Even_add_Even_inv_l n m : Even (n + m) -> Even m -> Even n.
Proof. rewrite <- ? even_spec, even_add; do 2 destruct even; auto. Qed.

Lemma Even_add_Odd_inv_r n m : Even (n + m) -> Odd n -> Odd m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Even_add_Odd_inv_l n m : Even (n + m) -> Odd m -> Odd n.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_Even_inv_l n m : Odd (n + m) -> Odd m -> Even n.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_Even_inv_r n m : Odd (n + m) -> Odd n -> Even m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_Odd_inv_l n m : Odd (n + m) -> Even m -> Odd n.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_add_Odd_inv_r n m : Odd (n + m) -> Even n -> Odd m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_add; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Even_mul_aux n m :
  (Odd (n * m) <-> Odd n /\ Odd m) /\ (Even (n * m) <-> Even n \/ Even m).
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, odd_mul, even_mul; unfold odd; do 2 destruct even; tauto.
Qed.

Lemma Even_mul_l n m : Even n -> Even (n * m).
Proof. rewrite <- ? even_spec, even_mul; do 2 destruct even; auto. Qed.

Lemma Even_mul_r n m : Even m -> Even (n * m).
Proof. rewrite <- ? even_spec, even_mul; do 2 destruct even; auto. Qed.

Lemma Even_mul_inv_r n m : Even (n * m) -> Odd n -> Even m.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_mul; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Even_mul_inv_l n m : Even (n * m) -> Odd m -> Even n.
Proof.
  rewrite <- ? even_spec, <- ? odd_spec, even_mul; unfold odd; do 2 destruct even; auto.
Qed.

Lemma Odd_mul n m : Odd n -> Odd m -> Odd (n * m).
Proof. rewrite <- ? odd_spec, odd_mul; unfold odd; do 2 destruct even; auto. Qed.

Lemma Odd_mul_inv_l n m : Odd (n * m) -> Odd n.
Proof. rewrite <- ? odd_spec, odd_mul; unfold odd; do 2 destruct even; auto. Qed.

Lemma Odd_mul_inv_r n m : Odd (n * m) -> Odd m.
Proof. rewrite <- ? odd_spec, odd_mul; unfold odd; do 2 destruct even; auto. Qed.

Lemma Even_div2 n : Even n -> div2 n = div2 (S n).
Proof. intros [p ->]; rewrite div2_succ_double; apply div2_double. Qed.

Lemma Odd_div2 n : Odd n -> S (div2 n) = div2 (S n).
Proof.
  intros [p ->]; rewrite add_1_r, div2_succ_double; cbn.
  f_equal; symmetry; apply div2_double.
Qed.

Lemma div2_Even n : div2 n = div2 (S n) -> Even n.
Proof.
  destruct (Even_or_Odd n) as [Ev|Od]; trivial.
  apply Odd_div2 in Od; rewrite <- Od.
  intro Od'; destruct (neq_succ_diag_r _ Od').
Qed.

Lemma div2_Odd n : S (div2 n) = div2 (S n) -> Odd n.
Proof.
  destruct (Even_or_Odd n) as [Ev|Od]; trivial.
  apply Even_div2 in Ev; rewrite <- Ev.
  intro Ev'; symmetry in Ev'; destruct (neq_succ_diag_r _ Ev').
Qed.

Lemma Even_Odd_div2 n :
  (Even n <-> div2 n = div2 (S n)) /\ (Odd n <-> S (div2 n) = div2 (S n)).
Proof.
  split; split; [ apply Even_div2 | apply div2_Even | apply Odd_div2 | apply div2_Odd ].
Qed.

Lemma Even_Odd_double n :
  (Even n <-> n = double (div2 n)) /\ (Odd n <-> n = S (double (div2 n))).
Proof.
  revert n.
  fix Even_Odd_double 1.
    intros n; destruct n as [|[|n]].
    - (* n = 0 *)
      split; split; intros H; [ reflexivity | apply Even_0 | apply Odd_0 in H as [] | inversion H ].
    - (* n = 1 *)
      split; split; intros H; [ apply Even_1 in H as [] | inversion H | reflexivity | apply Odd_1 ].
    - (* n = (S (S n')) *)
      destruct (Even_Odd_double n) as ((Ev,Ev'),(Od,Od')).
      split; split; simpl div2; rewrite ? double_S, ? Even_succ_succ, ? Odd_succ_succ.
      + intros; do 2 f_equal; auto.
      + injection 1; auto.
      + intros; do 2 f_equal; auto.
      + injection 1; auto.
Qed.

Lemma Even_double n : Even n -> n = double (div2 n).
Proof proj1 (proj1 (Even_Odd_double n)).

Lemma double_Even n : n = double (div2 n) -> Even n.
Proof proj2 (proj1 (Even_Odd_double n)).

Lemma Odd_double n : Odd n -> n = S (double (div2 n)).
Proof proj1 (proj2 (Even_Odd_double n)).

Lemma double_Odd n : n = S (double (div2 n)) -> Odd n.
Proof proj2 (proj2 (Even_Odd_double n)).

(** Inductive definition of even and odd *)
Inductive Even_alt : nat -> Prop :=
| Even_alt_O : Even_alt 0
| Even_alt_S : forall n, Odd_alt n -> Even_alt (S n)
with Odd_alt : nat -> Prop :=
| Odd_alt_S : forall n, Even_alt n -> Odd_alt (S n).

Lemma Even_alt_Even : forall n, Even_alt n <-> Even n.
Proof.
  fix Even_alt_Even 1.
    intros n; destruct n as [|[|n]]; simpl.
    - split; [now exists 0 | constructor].
    - split.
      + inversion_clear 1 as [|? H0].
        inversion_clear H0.
      + now rewrite <- Nat.even_spec.
    - rewrite Nat.Even_succ_succ, <- Even_alt_Even.
      split.
      + inversion_clear 1 as [|? H0].
        now inversion_clear H0.
      + now do 2 constructor.
Qed.

Lemma Odd_alt_Odd : forall n, Odd_alt n <-> Odd n.
Proof.
  fix Odd_alt_Odd 1.
    intros n; destruct n as [|[|n]]; simpl.
    - split.
      + inversion_clear 1.
      + now rewrite <- Nat.odd_spec.
    - split; [ now exists 0 | do 2 constructor ].
    - rewrite Nat.Odd_succ_succ, <- Odd_alt_Odd.
      split.
      + inversion_clear 1 as [? H0].
        now inversion_clear H0.
      + now do 2 constructor.
Qed.

Scheme Odd_alt_Even_alt_ind := Minimality for Odd_alt Sort Prop
with Even_alt_Odd_alt_ind := Minimality for Even_alt Sort Prop.

Lemma Odd_Even_ind (P Q : nat -> Prop) :
  (forall n, Even n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, Odd n -> P n -> Q (S n)) -> forall n, Odd n -> P n.
Proof.
  intros HSE H0 HSO n HO%Odd_alt_Odd.
  apply Odd_alt_Even_alt_ind with Q; try assumption.
  - intros m HSE'%Even_alt_Even; auto.
  - intros m HSO'%Odd_alt_Odd; auto.
Qed.

Lemma Even_Odd_ind (P Q : nat -> Prop) :
  (forall n, Even n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, Odd n -> P n -> Q (S n)) -> forall n, Even n -> Q n.
Proof.
  intros HSE H0 HSO n HE%Even_alt_Even.
  apply Even_alt_Odd_alt_ind with P; try assumption.
  - intros m HSE'%Even_alt_Even; auto.
  - intros m HSO'%Odd_alt_Odd; auto.
Qed.

(* Anomaly see Issue #15413
Combined Scheme Even_Odd_mutind from Even_Odd_ind, Odd_Even_ind.
*)

Scheme Odd_alt_Even_alt_sind := Minimality for Odd_alt Sort SProp
with Even_alt_Odd_alt_sind := Minimality for Even_alt Sort SProp.

Lemma Odd_Even_sind (P Q : nat -> SProp) :
  (forall n, Even n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, Odd n -> P n -> Q (S n)) -> forall n, Odd n -> P n.
Proof.
  intros HSE H0 HSO n HO%Odd_alt_Odd.
  apply Odd_alt_Even_alt_sind with Q; try assumption.
  - intros m HSE'%Even_alt_Even; auto.
  - intros m HSO'%Odd_alt_Odd; auto.
Qed.

Lemma Even_Odd_sind (P Q : nat -> SProp) :
  (forall n, Even n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, Odd n -> P n -> Q (S n)) -> forall n, Even n -> Q n.
Proof.
  intros HSE H0 HSO n HE%Even_alt_Even.
  apply Even_alt_Odd_alt_sind with P; try assumption.
  - intros m HSE'%Even_alt_Even; auto.
  - intros m HSO'%Odd_alt_Odd; auto.
Qed.

(* Anomaly see Issue #15413
Combined Scheme Even_Odd_mutsind from Even_Odd_sind, Odd_Even_sind.
*)

(** additional versions of parity predicates in [Type]
    useful for eliminating into [Type], but still with opaque proofs *)

Definition EvenT n := { m | n = 2 * m }.
Definition OddT n := { m | n = 2 * m + 1 }.

Lemma EvenT_0 : EvenT 0.
Proof. exists 0; reflexivity. Qed.

Lemma EvenT_2 n : EvenT n -> EvenT (S (S n)).
Proof.
  intros [m H]; exists (S m); rewrite H.
  cbn; rewrite add_succ_r; reflexivity.
Qed.

Lemma OddT_1 : OddT 1.
Proof. exists 0; reflexivity. Qed.

Lemma OddT_2 n : OddT n -> OddT (S (S n)).
Proof.
  intros [m H]; exists (S m).
  rewrite H, ? mul_succ_r, <- ? add_1_r, add_assoc; reflexivity.
Qed.

Lemma EvenT_S_OddT n : EvenT (S n) -> OddT n.
Proof.
  intros [[|k] HE]; inversion HE.
  exists k; rewrite add_succ_r, add_1_r; reflexivity.
Qed.

Lemma OddT_S_EvenT n : OddT (S n) -> EvenT n.
Proof.
  intros [k HO]; rewrite add_1_r in HO; injection HO; intros ->.
  exists k; reflexivity.
Qed.

Lemma even_EvenT : forall n, even n = true -> EvenT n.
Proof.
  fix even_specT 1.
    intro n; destruct n as [|[|n]]; simpl.
    - intros; apply EvenT_0.
    - intros H; discriminate.
    - intros He%even_specT; apply EvenT_2; assumption.
Qed.

Lemma odd_OddT : forall n, odd n = true -> OddT n.
Proof.
  unfold odd.
  fix odd_specT 1.
    intro n; destruct n as [|[|n]]; simpl.
    - intro H; discriminate.
    - intros; apply OddT_1.
    - intros He%odd_specT; apply OddT_2; assumption.
Qed.

Lemma EvenT_Even n : EvenT n -> Even n.
Proof. intros [k ?]; exists k; assumption. Qed.

Lemma OddT_Odd n : OddT n -> Odd n.
Proof. intros [k ?]; exists k; assumption. Qed.

Lemma Even_EvenT n : Even n -> EvenT n.
Proof. intros; apply even_EvenT, even_spec; assumption. Qed.

Lemma Odd_OddT n : Odd n -> OddT n.
Proof. intros; apply odd_OddT, odd_spec; assumption. Qed.

Lemma EvenT_even n : EvenT n -> even n = true.
Proof. intros; apply even_spec, EvenT_Even; assumption. Qed.

Lemma OddT_odd n : OddT n -> odd n = true.
Proof. intros; apply odd_spec, OddT_Odd; assumption. Qed.

Lemma EvenT_OddT_dec n : EvenT n + OddT n.
Proof.
  case_eq (even n); intros Hp.
  - left; apply even_EvenT; assumption.
  - right; apply odd_OddT.
    unfold odd; rewrite Hp; reflexivity.
Qed.

Lemma OddT_EvenT_rect (P Q : nat -> Type) :
  (forall n, EvenT n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, OddT n -> P n -> Q (S n)) -> forall n, OddT n -> P n.
Proof.
  intros HQP HQ0 HPQ.
  fix OddT_EvenT_rect 1.
    intros [|[|n]].
    - intros [[|k] H0]; inversion H0.
    - intros _; apply (HQP _ EvenT_0 HQ0).
    - intros HOSS.
      assert (EvenT (S n)) as HES by apply (OddT_S_EvenT _ HOSS).
      assert (OddT n) as HO by apply (EvenT_S_OddT _ HES).
      apply (HQP _ HES (HPQ _ HO (OddT_EvenT_rect _ HO))).
Qed.

Lemma EvenT_OddT_rect (P Q : nat -> Type) :
  (forall n, EvenT n -> Q n -> P (S n)) ->
  Q 0 -> (forall n, OddT n -> P n -> Q (S n)) -> forall n, EvenT n -> Q n.
Proof.
  intros HQP HQ0 HPQ [|n] HES; [ assumption | ].
  assert (OddT n) as HO by apply (EvenT_S_OddT _ HES).
  apply HPQ, (OddT_EvenT_rect P Q); assumption.
Qed.

(* Anomaly see Issue #15413
Combined Scheme EvenT_OddT_mutrect from EvenT_OddT_rect, OddT_EvenT_rect.
*)
End Nat.

(** Re-export notations that should be available even when
    the [Nat] module is not imported. *)

Bind Scope nat_scope with Nat.t nat.

Infix "^" := Nat.pow : nat_scope.
Infix "=?" := Nat.eqb (at level 70) : nat_scope.
Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "?=" := Nat.compare (at level 70) : nat_scope.
Infix "/" := Nat.div : nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.

#[global] Hint Unfold Nat.le : core.
#[global] Hint Unfold Nat.lt : core.

(* Register *)
#[local]
Definition lt_n_Sm_le := (fun n m => (proj1 (Nat.lt_succ_r n m))).
Register lt_n_Sm_le as num.nat.lt_n_Sm_le.
#[local]
Definition le_lt_n_Sm := (fun n m => (proj2 (Nat.lt_succ_r n m))).
Register le_lt_n_Sm as num.nat.le_lt_n_Sm.
#[local]
Definition lt_S_n := (fun n m => (proj2 (Nat.succ_lt_mono n m))).
Register lt_S_n as num.nat.lt_S_n.
Register Nat.le_lt_trans as num.nat.le_lt_trans.
#[local]
Definition pred_of_minus := (fun n => eq_sym (Nat.sub_1_r n)).
Register pred_of_minus as num.nat.pred_of_minus.
Register Nat.le_trans as num.nat.le_trans.
Register Nat.nlt_0_r as num.nat.nlt_0_r.

(** [Nat] contains an [order] tactic for natural numbers *)

(** Note that [Nat.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
  Let test : forall x y, x<=y -> y<=x -> x=y.
  Proof. Nat.order. Defined.
End TestOrder.
