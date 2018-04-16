(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(*                      Evgeny Makarov, INRIA, 2007                     *)
(************************************************************************)

Require Import NAxioms NProperties OrdersFacts.

(** Implementation of [NAxiomsSig] by [nat] *)

Module Nat
 <: NAxiomsSig
 <: UsualDecidableTypeFull
 <: OrderedTypeFull
 <: TotalOrder.

(** Operations over [nat] are defined in a separate module *)

Include Coq.Init.Nat.

(** When including property functors, inline t eq zero one two lt le succ *)

Set Inline Level 50.

(** All operations are well-defined (trivial here since eq is Leibniz) *)

Definition eq_equiv : Equivalence (@eq nat) := eq_equivalence.
Local Obligation Tactic := simpl_relation.
Program Instance succ_wd : Proper (eq==>eq) S.
Program Instance pred_wd : Proper (eq==>eq) pred.
Program Instance add_wd : Proper (eq==>eq==>eq) plus.
Program Instance sub_wd : Proper (eq==>eq==>eq) minus.
Program Instance mul_wd : Proper (eq==>eq==>eq) mult.
Program Instance pow_wd : Proper (eq==>eq==>eq) pow.
Program Instance div_wd : Proper (eq==>eq==>eq) div.
Program Instance mod_wd : Proper (eq==>eq==>eq) modulo.
Program Instance lt_wd : Proper (eq==>eq==>iff) lt.
Program Instance testbit_wd : Proper (eq==>eq==>eq) testbit.

(** Bi-directional induction. *)

Theorem bi_induction :
  forall A : nat -> Prop, Proper (eq==>iff) A ->
    A 0 -> (forall n : nat, A n <-> A (S n)) -> forall n : nat, A n.
Proof.
intros A A_wd A0 AS. apply nat_ind. assumption. intros; now apply -> AS.
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

(** ** Remaining constants not defined in Coq.Init.Nat *)

(** NB: Aliasing [le] is mandatory, since only a Definition can implement
    an interface Parameter... *)

Definition eq := @Logic.eq nat.
Definition le := Peano.le.
Definition lt := Peano.lt.

(** ** Basic specifications : pred add sub mul *)

Lemma pred_succ n : pred (S n) = n.
Proof.
reflexivity.
Qed.

Lemma pred_0 : pred 0 = 0.
Proof.
reflexivity.
Qed.

Lemma one_succ : 1 = S 0.
Proof.
reflexivity.
Qed.

Lemma two_succ : 2 = S 1.
Proof.
reflexivity.
Qed.

Lemma add_0_l n : 0 + n = n.
Proof.
reflexivity.
Qed.

Lemma add_succ_l n m : (S n) + m = S (n + m).
Proof.
reflexivity.
Qed.

Lemma sub_0_r n : n - 0 = n.
Proof.
now destruct n.
Qed.

Lemma sub_succ_r n m : n - (S m) = pred (n - m).
Proof.
revert m. induction n; destruct m; simpl; auto. apply sub_0_r.
Qed.

Lemma mul_0_l n : 0 * n = 0.
Proof.
reflexivity.
Qed.

Lemma mul_succ_l n m : S n * m = n * m + m.
Proof.
assert (succ_r : forall x y, x+S y = S(x+y)) by now induction x.
assert (comm : forall x y, x+y = y+x).
{ induction x; simpl; auto. intros; rewrite succ_r; now f_equal. }
now rewrite comm.
Qed.

Lemma lt_succ_r n m : n < S m <-> n <= m.
Proof.
split. apply Peano.le_S_n. induction 1; auto.
Qed.

(** ** Boolean comparisons *)

Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof.
 revert m.
 induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
 - now intros ->.
 - now injection 1.
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
 revert m.
 induction n; destruct m; simpl.
 - now split.
 - split; trivial. intros; apply Peano.le_0_n.
 - now split.
 - rewrite IHn; split.
   + apply Peano.le_n_S.
   + apply Peano.le_S_n.
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
 apply leb_le.
Qed.

(** ** Decidability of equality over [nat]. *)

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n; destruct m.
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
 revert m; induction n; destruct m; simpl; rewrite ?IHn; split; auto; easy.
Qed.

Lemma compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof.
 revert m; induction n; destruct m; simpl; rewrite ?IHn; split; try easy.
 - intros _. apply Peano.le_n_S, Peano.le_0_n.
 - apply Peano.le_n_S.
 - apply Peano.le_S_n.
Qed.

Lemma compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof.
 revert m; induction n; destruct m; simpl; rewrite ?IHn.
 - now split.
 - split; intros. apply Peano.le_0_n. easy.
 - split. now destruct 1. inversion 1.
 - split; intros. now apply Peano.le_n_S. now apply Peano.le_S_n.
Qed.

Lemma compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof.
 revert m; induction n; destruct m; simpl; trivial.
Qed.

Lemma compare_succ n m : (S n ?= S m) = (n ?= m).
Proof.
 reflexivity.
Qed.


(* BUG: Ajout d'un cas * après preuve finie (deuxième niveau +++*** ) :
    *  --->   Anomaly: Uncaught exception Proofview.IndexOutOfRange(_). Please report. *)

(** ** Minimum, maximum *)

Lemma max_l : forall n m, m <= n -> max n m = n.
Proof.
 exact Peano.max_l.
Qed.

Lemma max_r : forall n m, n <= m -> max n m = m.
Proof.
 exact Peano.max_r.
Qed.

Lemma min_l : forall n m, n <= m -> min n m = n.
Proof.
 exact Peano.min_l.
Qed.

Lemma min_r : forall n m, m <= n -> min n m = m.
Proof.
 exact Peano.min_r.
Qed.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include NBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

(** ** Power *)

Lemma pow_neg_r a b : b<0 -> a^b = 0. inversion 1. Qed.

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

Lemma Even_1 : ~ Even 1.
Proof.
 intros ([|], H); try discriminate.
 simpl in H. now rewrite <- plus_n_Sm in H.
Qed.

Lemma Even_2 n : Even n <-> Even (S (S n)).
Proof.
 split; intros (m,H).
 - exists (S m). rewrite H. simpl. now rewrite plus_n_Sm.
 - destruct m; try discriminate.
   exists m. simpl in H. rewrite <- plus_n_Sm in H. now inversion H.
Qed.

Lemma Odd_0 : ~ Odd 0.
Proof.
 now intros ([|], H).
Qed.

Lemma Odd_2 n : Odd n <-> Odd (S (S n)).
Proof.
 split; intros (m,H).
 - exists (S m). rewrite H. simpl. now rewrite <- (plus_n_Sm m).
 - destruct m; try discriminate.
   exists m. simpl in H. rewrite <- plus_n_Sm in H. inversion H.
   simpl. now rewrite <- !plus_n_Sm, <- !plus_n_O.
Qed.

End Private_Parity.
Import Private_Parity.

Lemma even_spec : forall n, even n = true <-> Even n.
Proof.
 fix even_spec 1.
  destruct n as [|[|n]]; simpl.
  - split; [ now exists 0 | trivial ].
  - split; [ discriminate | intro H; elim (Even_1 H) ].
  - rewrite even_spec. apply Even_2.
Qed.

Lemma odd_spec : forall n, odd n = true <-> Odd n.
Proof.
 unfold odd.
 fix odd_spec 1.
  destruct n as [|[|n]]; simpl.
  - split; [ discriminate | intro H; elim (Odd_0 H) ].
  - split; [ now exists 0 | trivial ].
  - rewrite odd_spec. apply Odd_2.
Qed.

(** ** Division *)

Lemma divmod_spec : forall x y q u, u <= y ->
 let (q',u') := divmod x y q u in
 x + (S y)*q + (y-u) = (S y)*q' + (y-u') /\ u' <= y.
Proof.
 induction x.
 - simpl; intuition.
 - intros y q u H. destruct u; simpl divmod.
   + generalize (IHx y (S q) y (le_n y)). destruct divmod as (q',u').
     intros (EQ,LE); split; trivial.
     rewrite <- EQ, sub_0_r, sub_diag, add_0_r.
     now rewrite !add_succ_l, <- add_succ_r, <- add_assoc, mul_succ_r.
   + assert (H' : u <= y).
     { apply le_trans with (S u); trivial. do 2 constructor. }
     generalize (IHx y q u H'). destruct divmod as (q',u').
     intros (EQ,LE); split; trivial.
     rewrite <- EQ.
     rewrite !add_succ_l, <- add_succ_r. f_equal. now rewrite <- sub_succ_l.
Qed.

Lemma div_mod x y : y<>0 -> x = y*(x/y) + x mod y.
Proof.
 intros Hy.
 destruct y; [ now elim Hy | clear Hy ].
 unfold div, modulo.
 generalize (divmod_spec x y 0 y (le_n y)).
 destruct divmod as (q,u).
 intros (U,V).
 simpl in *.
 now rewrite mul_0_r, sub_diag, !add_0_r in U.
Qed.

Lemma mod_bound_pos x y : 0<=x -> 0<y -> 0 <= x mod y < y.
Proof.
 intros Hx Hy. split. apply le_0_l.
 destruct y; [ now elim Hy | clear Hy ].
 unfold modulo.
 apply lt_succ_r, le_sub_l.
Qed.

(** ** Square root *)

Lemma sqrt_iter_spec : forall k p q r,
 q = p+p -> r<=q ->
 let s := sqrt_iter k p q r in
 s*s <= k + p*p + (q - r) < (S s)*(S s).
Proof.
 induction k.
 - (* k = 0 *)
   simpl; intros p q r Hq Hr.
   split.
   + apply le_add_r.
   + apply lt_succ_r.
     rewrite mul_succ_r.
     rewrite add_assoc, (add_comm p), <- add_assoc.
     apply add_le_mono_l.
     rewrite <- Hq. apply le_sub_l.
 - (* k = S k' *)
   destruct r.
   + (* r = 0 *)
     intros Hq _.
     replace (S k + p*p + (q-0)) with (k + (S p)*(S p) + (S (S q) - S (S q))).
     * apply IHk.
       simpl. now rewrite add_succ_r, Hq. apply le_n.
     * rewrite sub_diag, sub_0_r, add_0_r. simpl.
       rewrite add_succ_r; f_equal. rewrite <- add_assoc; f_equal.
       rewrite mul_succ_r, (add_comm p), <- add_assoc. now f_equal.
   + (* r = S r' *)
     intros Hq Hr.
     replace (S k + p*p + (q-S r)) with (k + p*p + (q - r)).
     * apply IHk; trivial. apply le_trans with (S r); trivial. do 2 constructor.
     * simpl. rewrite <- add_succ_r. f_equal. rewrite <- sub_succ_l; trivial.
Qed.

Lemma sqrt_specif n : (sqrt n)*(sqrt n) <= n < S (sqrt n) * S (sqrt n).
Proof.
 set (s:=sqrt n).
 replace n with (n + 0*0 + (0-0)).
 apply sqrt_iter_spec; auto.
 simpl. now rewrite !add_0_r.
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
 induction k.
 - (* k = 0 *)
   intros p q r EQ LT. simpl log2_iter. cbv zeta.
   split.
   + rewrite add_0_l.
     rewrite (add_le_mono_l _ _ (2^p)).
     simpl pow in EQ. rewrite add_0_r in EQ. rewrite EQ.
     rewrite add_comm. apply add_le_mono_r. apply LT.
   + rewrite EQ, add_comm. apply add_lt_mono_l.
     apply lt_succ_r, le_0_l.
 - (* k = S k' *)
   intros p q r EQ LT. destruct r.
   + (* r = 0 *)
     rewrite add_succ_r, add_0_r in EQ.
     rewrite add_succ_l, <- add_succ_r. apply IHk.
     * rewrite <- EQ. remember (S p) as p'; simpl. now rewrite add_0_r.
     * rewrite EQ. constructor.
   + (* r = S r' *)
     rewrite add_succ_l, <- add_succ_r. apply IHk.
     * now rewrite add_succ_l, <- add_succ_r.
     * apply le_lt_trans with (S r); trivial. do 2 constructor.
Qed.

Lemma log2_spec n : 0<n ->
 2^(log2 n) <= n < 2^(S (log2 n)).
Proof.
 intros.
 set (s:=log2 n).
 replace n with (pred n + 1).
 apply log2_iter_spec; auto.
 rewrite add_1_r.
 apply succ_pred. now apply neq_sym, lt_neq.
Qed.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof.
 inversion 1; now subst.
Qed.

(** ** Gcd *)

Definition divide x y := exists z, y=z*x.
Notation "( x | y )" := (divide x y) (at level 0) : nat_scope.

Lemma gcd_divide : forall a b, (gcd a b | a) /\ (gcd a b | b).
Proof.
 fix gcd_divide 1.
 intros [|a] b; simpl.
 split.
  now exists 0.
  exists 1. simpl. now rewrite <- plus_n_O.
 fold (b mod (S a)).
 destruct (gcd_divide (b mod (S a)) (S a)) as (H,H').
 set (a':=S a) in *.
 split; auto.
 rewrite (div_mod b a') at 2 by discriminate.
 destruct H as (u,Hu), H' as (v,Hv).
 rewrite mul_comm.
 exists ((b/a')*v + u).
 rewrite mul_add_distr_r.
 now rewrite <- mul_assoc, <- Hv, <- Hu.
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
 fix gcd_greatest 1.
 intros [|a] b; simpl; auto.
 fold (b mod (S a)).
 intros c H H'. apply gcd_greatest; auto.
 set (a':=S a) in *.
 rewrite (div_mod b a') in H' by discriminate.
 destruct H as (u,Hu), H' as (v,Hv).
 exists (v - (b/a')*u).
 rewrite mul_comm in Hv.
 rewrite mul_sub_distr_r, <- Hv, <- mul_assoc, <-Hu.
 now rewrite add_comm, add_sub.
Qed.

Lemma gcd_nonneg a b : 0<=gcd a b.
Proof. apply le_0_l. Qed.


(** ** Bitwise operations *)

Lemma div2_double n : div2 (2*n) = n.
Proof.
 induction n; trivial.
 simpl mul. rewrite add_succ_r. simpl. now f_equal.
Qed.

Lemma div2_succ_double n : div2 (S (2*n)) = n.
Proof.
 induction n; trivial.
 simpl. f_equal. now rewrite add_succ_r.
Qed.

Lemma le_div2 n : div2 (S n) <= n.
Proof.
 revert n.
 fix le_div2 1.
 destruct n; simpl; trivial. apply lt_succ_r.
 destruct n; [simpl|]; trivial. now constructor.
Qed.

Lemma lt_div2 n : 0 < n -> div2 n < n.
Proof.
 destruct n.
 - inversion 1.
 - intros _. apply lt_succ_r, le_div2.
Qed.

Lemma div2_decr a n : a <= S n -> div2 a <= n.
Proof.
 destruct a; intros H.
 - simpl. apply le_0_l.
 - apply succ_le_mono in H.
   apply le_trans with a; [ apply le_div2 | trivial ].
Qed.

Lemma double_twice : forall n, double n = 2*n.
Proof.
 simpl; intros. now rewrite add_0_r.
Qed.

Lemma testbit_0_l : forall n, testbit 0 n = false.
Proof.
 now induction n.
Qed.

Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof.
 unfold testbit. rewrite odd_spec. now exists a.
Qed.

Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof.
 unfold testbit, odd. rewrite (proj2 (even_spec _)); trivial.
 now exists a.
Qed.

Lemma testbit_odd_succ' a n : testbit (2*a+1) (S n) = testbit a n.
Proof.
 unfold testbit; fold testbit.
 rewrite add_1_r. f_equal.
 apply div2_succ_double.
Qed.

Lemma testbit_even_succ' a n : testbit (2*a) (S n) = testbit a n.
Proof.
 unfold testbit; fold testbit. f_equal. apply div2_double.
Qed.

Lemma shiftr_specif : forall a n m,
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 induction n; intros m. trivial.
 now rewrite add_0_r.
 now rewrite add_succ_r, <- add_succ_l, <- IHn.
Qed.

Lemma shiftl_specif_high : forall a n m, n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 induction n; intros m H. trivial.
 now rewrite sub_0_r.
 destruct m. inversion H.
 simpl. apply succ_le_mono in H.
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
 now apply succ_le_mono.
Qed.

Lemma div2_bitwise : forall op n a b,
 div2 (bitwise op (S n) a b) = bitwise op n (div2 a) (div2 b).
Proof.
 intros. unfold bitwise; fold bitwise.
 destruct (op (odd a) (odd b)).
 now rewrite div2_succ_double.
 now rewrite add_0_l, div2_double.
Qed.

Lemma odd_bitwise : forall op n a b,
 odd (bitwise op (S n) a b) = op (odd a) (odd b).
Proof.
 intros. unfold bitwise; fold bitwise.
 destruct (op (odd a) (odd b)).
 apply odd_spec. rewrite add_comm. eexists; eauto.
 unfold odd. apply negb_false_iff. apply even_spec.
 rewrite add_0_l; eexists; eauto.
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
 apply IHn. now apply div2_decr.
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

Lemma land_spec a b n :
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 unfold land. apply testbit_bitwise_1; trivial.
Qed.

Lemma ldiff_spec a b n :
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 unfold ldiff. apply testbit_bitwise_1; trivial.
Qed.

Lemma lor_spec a b n :
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 unfold lor. apply testbit_bitwise_2.
 - trivial.
 - destruct (compare_spec a b).
   + rewrite max_l; subst; trivial.
   + apply lt_le_incl in H. now rewrite max_r.
   + apply lt_le_incl in H. now rewrite max_l.
 - destruct (compare_spec a b).
   + rewrite max_r; subst; trivial.
   + apply lt_le_incl in H. now rewrite max_r.
   + apply lt_le_incl in H. now rewrite max_l.
Qed.

Lemma lxor_spec a b n :
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 unfold lxor. apply testbit_bitwise_2.
 - trivial.
 - destruct (compare_spec a b).
   + rewrite max_l; subst; trivial.
   + apply lt_le_incl in H. now rewrite max_r.
   + apply lt_le_incl in H. now rewrite max_l.
 - destruct (compare_spec a b).
   + rewrite max_r; subst; trivial.
   + apply lt_le_incl in H. now rewrite max_r.
   + apply lt_le_incl in H. now rewrite max_l.
Qed.

Lemma div2_spec a : div2 a = shiftr a 1.
Proof.
 reflexivity.
Qed.

(** Aliases with extra dummy hypothesis, to fulfil the interface *)

Definition testbit_odd_succ a n (_:0<=n) := testbit_odd_succ' a n.
Definition testbit_even_succ a n (_:0<=n) := testbit_even_succ' a n.
Lemma testbit_neg_r a n (H:n<0) : testbit a n = false.
Proof. inversion H. Qed.

Definition shiftl_spec_high a n m (_:0<=m) := shiftl_specif_high a n m.
Definition shiftr_spec a n m (_:0<=m) := shiftr_specif a n m.

(** Properties of advanced functions (pow, sqrt, log2, ...) *)

Include NExtraProp.

(** Properties of tail-recursive addition and multiplication *)

Lemma tail_add_spec n m : tail_add n m = n + m.
Proof.
 revert m. induction n as [|n IH]; simpl; trivial.
 intros. now rewrite IH, add_succ_r.
Qed.

Lemma tail_addmul_spec r n m : tail_addmul r n m = r + n * m.
Proof.
 revert m r. induction n as [| n IH]; simpl; trivial.
 intros. rewrite IH, tail_add_spec.
 rewrite add_assoc. f_equal. apply add_comm.
Qed.

Lemma tail_mul_spec n m : tail_mul n m = n * m.
Proof.
 unfold tail_mul. now rewrite tail_addmul_spec.
Qed.

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

Hint Unfold Nat.le : core.
Hint Unfold Nat.lt : core.

(** [Nat] contains an [order] tactic for natural numbers *)

(** Note that [Nat.order] is domain-agnostic: it will not prove
    [1<=2] or [x<=x+x], but rather things like [x<=y -> y<=x -> x=y]. *)

Section TestOrder.
 Let test : forall x y, x<=y -> y<=x -> x=y.
 Proof.
 Nat.order.
 Qed.
End TestOrder.
