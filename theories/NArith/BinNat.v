(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums.
Require Import BinPos RelationClasses Morphisms Setoid
 Equalities OrdersFacts GenericMinMax Bool NAxioms NMaxMin NProperties.
Require BinNatDef.

(**********************************************************************)
(** * Binary natural numbers, operations and properties *)
(**********************************************************************)

(** The type [N] and its constructors [N0] and [Npos] are now
    defined in [BinNums.v] *)

(** Every definitions and properties about binary natural numbers
    are placed in a module [N] for qualification purpose. *)

Local Open Scope N_scope.

(** Every definitions and early properties about positive numbers
    are placed in a module [N] for qualification purpose. *)

Module N
 <: NAxiomsSig
 <: UsualOrderedTypeFull
 <: UsualDecidableTypeFull
 <: TotalOrder.

(** Definitions of operations, now in a separate file *)

Include BinNatDef.N.

(** When including property functors, only inline t eq zero one two *)

Set Inline Level 30.

(** Logical predicates *)

Definition eq := @Logic.eq N.
Definition eq_equiv := @eq_equivalence N.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : N_scope.
Infix "<" := lt : N_scope.
Infix ">=" := ge : N_scope.
Infix ">" := gt : N_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : N_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : N_scope.
Notation "x < y < z" := (x < y /\ y < z) : N_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : N_scope.

Definition divide p q := exists r, q = r*p.
Notation "( p | q )" := (divide p q) (at level 0) : N_scope.

Definition Even n := exists m, n = 2*m.
Definition Odd n := exists m, n = 2*m+1.

(** Proofs of morphisms, obvious since eq is Leibniz *)

Local Obligation Tactic := simpl_relation.
Program Definition succ_wd : Proper (eq==>eq) succ := _.
Program Definition pred_wd : Proper (eq==>eq) pred := _.
Program Definition add_wd : Proper (eq==>eq==>eq) add := _.
Program Definition sub_wd : Proper (eq==>eq==>eq) sub := _.
Program Definition mul_wd : Proper (eq==>eq==>eq) mul := _.
Program Definition lt_wd : Proper (eq==>eq==>iff) lt := _.
Program Definition div_wd : Proper (eq==>eq==>eq) div := _.
Program Definition mod_wd : Proper (eq==>eq==>eq) modulo := _.
Program Definition pow_wd : Proper (eq==>eq==>eq) pow := _.
Program Definition testbit_wd : Proper (eq==>eq==>Logic.eq) testbit := _.

(** Decidability of equality. *)

Definition eq_dec : forall n m : N, { n = m } + { n <> m }.
Proof.
 decide equality.
 apply Pos.eq_dec.
Defined.

(** Discrimination principle *)

Definition discr n : { p:positive | n = pos p } + { n = 0 }.
Proof.
 destruct n; auto.
 left; exists p; auto.
Defined.

(** Convenient induction principles *)

Definition binary_rect (P:N -> Type) (f0 : P 0)
  (f2 : forall n, P n -> P (double n))
  (fS2 : forall n, P n -> P (succ_double n)) (n : N) : P n :=
 let P' p := P (pos p) in
 let f2' p := f2 (pos p) in
 let fS2' p := fS2 (pos p) in
 match n with
 | 0 => f0
 | pos p => positive_rect P' fS2' f2' (fS2 0 f0) p
 end.

Definition binary_rec (P:N -> Set) := binary_rect P.
Definition binary_ind (P:N -> Prop) := binary_rect P.

(** Peano induction on binary natural numbers *)

Definition peano_rect
  (P : N -> Type) (f0 : P 0)
    (f : forall n : N, P n -> P (succ n)) (n : N) : P n :=
let P' p := P (pos p) in
let f' p := f (pos p) in
match n with
| 0 => f0
| pos p => Pos.peano_rect P' (f 0 f0) f' p
end.

Theorem peano_rect_base P a f : peano_rect P a f 0 = a.
Proof.
reflexivity.
Qed.

Theorem peano_rect_succ P a f n :
 peano_rect P a f (succ n) = f n (peano_rect P a f n).
Proof.
destruct n; simpl.
trivial.
now rewrite Pos.peano_rect_succ.
Qed.

Definition peano_ind (P : N -> Prop) := peano_rect P.

Definition peano_rec (P : N -> Set) := peano_rect P.

Theorem peano_rec_base P a f : peano_rec P a f 0 = a.
Proof.
apply peano_rect_base.
Qed.

Theorem peano_rec_succ P a f n :
 peano_rec P a f (succ n) = f n (peano_rec P a f n).
Proof.
apply peano_rect_succ.
Qed.

(** Generic induction / recursion *)

Theorem bi_induction :
  forall A : N -> Prop, Proper (Logic.eq==>iff) A ->
    A 0 -> (forall n, A n <-> A (succ n)) -> forall n : N, A n.
Proof.
intros A A_wd A0 AS. apply peano_rect. assumption. intros; now apply -> AS.
Qed.

Definition recursion {A} : A -> (N -> A -> A) -> N -> A :=
  peano_rect (fun _ => A).

Instance recursion_wd {A} (Aeq : relation A) :
 Proper (Aeq==>(Logic.eq==>Aeq==>Aeq)==>Logic.eq==>Aeq) recursion.
Proof.
intros a a' Ea f f' Ef x x' Ex. subst x'.
induction x using peano_ind.
trivial.
unfold recursion in *. rewrite 2 peano_rect_succ. now apply Ef.
Qed.

Theorem recursion_0 {A} (a:A) (f:N->A->A) : recursion a f 0 = a.
Proof. reflexivity. Qed.

Theorem recursion_succ {A} (Aeq : relation A) (a : A) (f : N -> A -> A):
 Aeq a a -> Proper (Logic.eq==>Aeq==>Aeq) f ->
  forall n : N, Aeq (recursion a f (succ n)) (f n (recursion a f n)).
Proof.
unfold recursion; intros a_wd f_wd n. induction n using peano_ind.
rewrite peano_rect_succ. now apply f_wd.
rewrite !peano_rect_succ in *. now apply f_wd.
Qed.

(** Specification of constants *)

Lemma one_succ : 1 = succ 0.
Proof. reflexivity. Qed.

Lemma two_succ : 2 = succ 1.
Proof. reflexivity. Qed.

Definition pred_0 : pred 0 = 0.
Proof. reflexivity. Qed.

(** Properties of mixed successor and predecessor. *)

Lemma pos_pred_spec p : Pos.pred_N p = pred (pos p).
Proof.
 now destruct p.
Qed.

Lemma succ_pos_spec n : pos (succ_pos n) = succ n.
Proof.
 now destruct n.
Qed.

Lemma pos_pred_succ n : Pos.pred_N (succ_pos n) = n.
Proof.
 destruct n. trivial. apply Pos.pred_N_succ.
Qed.

Lemma succ_pos_pred p : succ (Pos.pred_N p) = pos p.
Proof.
 destruct p; simpl; trivial. f_equal. apply Pos.succ_pred_double.
Qed.

(** Properties of successor and predecessor *)

Theorem pred_succ n : pred (succ n) = n.
Proof.
destruct n; trivial. simpl. apply Pos.pred_N_succ.
Qed.

Theorem pred_sub n : pred n = sub n 1.
Proof.
 now destruct n as [|[p|p|]].
Qed.

Theorem succ_0_discr n : succ n <> 0.
Proof.
now destruct n.
Qed.

(** Specification of addition *)

Theorem add_0_l n : 0 + n = n.
Proof.
reflexivity.
Qed.

Theorem add_succ_l n m : succ n + m = succ (n + m).
Proof.
destruct n, m; unfold succ, add; now rewrite ?Pos.add_1_l, ?Pos.add_succ_l.
Qed.

(** Specification of subtraction. *)

Theorem sub_0_r n : n - 0 = n.
Proof.
now destruct n.
Qed.

Theorem sub_succ_r n m : n - succ m = pred (n - m).
Proof.
destruct n as [|p], m as [|q]; trivial.
now destruct p.
simpl. rewrite Pos.sub_mask_succ_r, Pos.sub_mask_carry_spec.
now destruct (Pos.sub_mask p q) as [|[r|r|]|].
Qed.

(** Specification of multiplication *)

Theorem mul_0_l n : 0 * n = 0.
Proof.
reflexivity.
Qed.

Theorem mul_succ_l n m : (succ n) * m = n * m + m.
Proof.
destruct n, m; simpl; trivial. f_equal. rewrite Pos.add_comm.
apply Pos.mul_succ_l.
Qed.

(** Specification of boolean comparisons. *)

Lemma eqb_eq n m : eqb n m = true <-> n=m.
Proof.
destruct n as [|n], m as [|m]; simpl; try easy'.
rewrite Pos.eqb_eq. split; intro H. now subst. now destr_eq H.
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
  unfold ltb, lt. destruct compare; easy'.
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
  unfold leb, le. destruct compare; easy'.
Qed.

(** Basic properties of comparison *)

Theorem compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof.
destruct n, m; simpl; rewrite ?Pos.compare_eq_iff; split; congruence.
Qed.

Theorem compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof.
reflexivity.
Qed.

Theorem compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof.
reflexivity.
Qed.

Theorem compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof.
destruct n, m; simpl; trivial. apply Pos.compare_antisym.
Qed.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** Specification of minimum and maximum *)

Theorem min_l n m : n <= m -> min n m = n.
Proof.
unfold min, le. case compare; trivial. now destruct 1.
Qed.

Theorem min_r n m : m <= n -> min n m = m.
Proof.
unfold min, le. rewrite compare_antisym.
case compare_spec; trivial. now destruct 2.
Qed.

Theorem max_l n m : m <= n -> max n m = n.
Proof.
unfold max, le. rewrite compare_antisym.
case compare_spec; auto. now destruct 2.
Qed.

Theorem max_r n m : n <= m -> max n m = m.
Proof.
unfold max, le. case compare; trivial. now destruct 1.
Qed.

(** Specification of lt and le. *)

Lemma lt_succ_r n m : n < succ m <-> n<=m.
Proof.
destruct n as [|p], m as [|q]; simpl; try easy'.
split. now destruct p. now destruct 1.
apply Pos.lt_succ_r.
Qed.

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include NBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.


(** Properties of [double] and [succ_double] *)

Lemma double_spec n : double n = 2 * n.
Proof.
 reflexivity.
Qed.

Lemma succ_double_spec n : succ_double n = 2 * n + 1.
Proof.
 now destruct n.
Qed.

Lemma double_add n m : double (n+m) = double n + double m.
Proof.
 now destruct n, m.
Qed.

Lemma succ_double_add n m : succ_double (n+m) = double n + succ_double m.
Proof.
 now destruct n, m.
Qed.

Lemma double_mul n m : double (n*m) = double n * m.
Proof.
 now destruct n, m.
Qed.

Lemma succ_double_mul n m :
 succ_double n * m = double n * m + m.
Proof.
 destruct n; simpl; destruct m; trivial.
 now rewrite Pos.add_comm.
Qed.

Lemma div2_double n : div2 (double n) = n.
Proof.
now destruct n.
Qed.

Lemma div2_succ_double n : div2 (succ_double n) = n.
Proof.
now destruct n.
Qed.

Lemma double_inj n m : double n = double m -> n = m.
Proof.
intro H. rewrite <- (div2_double n), H. apply div2_double.
Qed.

Lemma succ_double_inj n m : succ_double n = succ_double m -> n = m.
Proof.
intro H. rewrite <- (div2_succ_double n), H. apply div2_succ_double.
Qed.

Lemma succ_double_lt n m : n<m -> succ_double n < double m.
Proof.
 destruct n as [|n], m as [|m]; intros H; try easy.
 unfold lt in *; simpl in *. now rewrite Pos.compare_xI_xO, H.
Qed.


(** 0 is the least natural number *)

Theorem compare_0_r n : (n ?= 0) <> Lt.
Proof.
now destruct n.
Qed.

(** Specifications of power *)

Lemma pow_0_r n : n ^ 0 = 1.
Proof. reflexivity. Qed.

Lemma pow_succ_r n p : 0<=p -> n^(succ p) = n * n^p.
Proof.
 intros _.
 destruct n, p; simpl; trivial; f_equal. apply Pos.pow_succ_r.
Qed.

Lemma pow_neg_r n p : p<0 -> n^p = 0.
Proof.
 now destruct p.
Qed.

(** Specification of square *)

Lemma square_spec n : square n = n * n.
Proof.
 destruct n; trivial. simpl. f_equal. apply Pos.square_spec.
Qed.

(** Specification of Base-2 logarithm *)

Lemma size_log2 n : n<>0 -> size n = succ (log2 n).
Proof.
 destruct n as [|[n|n| ]]; trivial. now destruct 1.
Qed.

Lemma size_gt n : n < 2^(size n).
Proof.
 destruct n. reflexivity. simpl. apply Pos.size_gt.
Qed.

Lemma size_le n : 2^(size n) <= succ_double n.
Proof.
 destruct n. discriminate. simpl.
 change (2^Pos.size p <= Pos.succ (p~0))%positive.
 apply Pos.lt_le_incl, Pos.lt_succ_r, Pos.size_le.
Qed.

Lemma log2_spec n : 0 < n ->
 2^(log2 n) <= n < 2^(succ (log2 n)).
Proof.
 destruct n as [|[p|p|]]; discriminate || intros _; simpl; split.
 apply (size_le (pos p)).
 apply Pos.size_gt.
 apply Pos.size_le.
 apply Pos.size_gt.
 discriminate.
 reflexivity.
Qed.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof.
 destruct n; intros Hn. reflexivity. now destruct Hn.
Qed.

(** Specification of parity functions *)

Lemma even_spec n : even n = true <-> Even n.
Proof.
 destruct n.
 split. now exists 0.
 trivial.
 destruct p; simpl; split; try easy.
 intros (m,H). now destruct m.
 now exists (pos p).
 intros (m,H). now destruct m.
Qed.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof.
 destruct n.
 split. discriminate.
 intros (m,H). now destruct m.
 destruct p; simpl; split; try easy.
 now exists (pos p).
 intros (m,H). now destruct m.
 now exists 0.
Qed.

(** Specification of the euclidean division *)

Theorem pos_div_eucl_spec (a:positive)(b:N) :
  let (q,r) := pos_div_eucl a b in pos a = q * b + r.
Proof.
  induction a; cbv beta iota delta [pos_div_eucl]; fold pos_div_eucl; cbv zeta.
  (* a~1 *)
  destruct pos_div_eucl as (q,r).
  change (pos a~1) with (succ_double (pos a)).
  rewrite IHa, succ_double_add, double_mul.
  case leb_spec; intros H; trivial.
  rewrite succ_double_mul, <- add_assoc. f_equal.
  now rewrite (add_comm b), sub_add.
  (* a~0 *)
  destruct pos_div_eucl as (q,r).
  change (pos a~0) with (double (pos a)).
  rewrite IHa, double_add, double_mul.
  case leb_spec; intros H; trivial.
  rewrite succ_double_mul, <- add_assoc. f_equal.
  now rewrite (add_comm b), sub_add.
  (* 1 *)
  now destruct b as [|[ | | ]].
Qed.

Theorem div_eucl_spec a b :
 let (q,r) := div_eucl a b in a = b * q + r.
Proof.
  destruct a as [|a], b as [|b]; unfold div_eucl; trivial.
  generalize (pos_div_eucl_spec a (pos b)).
  destruct pos_div_eucl. now rewrite mul_comm.
Qed.

Theorem div_mod' a b : a = b * (a/b) + (a mod b).
Proof.
  generalize (div_eucl_spec a b).
  unfold div, modulo. now destruct div_eucl.
Qed.

Definition div_mod a b : b<>0 -> a = b * (a/b) + (a mod b).
Proof.
 intros _. apply div_mod'.
Qed.

Theorem pos_div_eucl_remainder (a:positive) (b:N) :
  b<>0 -> snd (pos_div_eucl a b) < b.
Proof.
  intros Hb.
  induction a; cbv beta iota delta [pos_div_eucl]; fold pos_div_eucl; cbv zeta.
  (* a~1 *)
  destruct pos_div_eucl as (q,r); simpl in *.
  case leb_spec; intros H; simpl; trivial.
  apply add_lt_mono_l with b. rewrite add_comm, sub_add by trivial.
  destruct b as [|b]; [now destruct Hb| simpl; rewrite Pos.add_diag ].
  apply (succ_double_lt _ _ IHa).
  (* a~0 *)
  destruct pos_div_eucl as (q,r); simpl in *.
  case leb_spec; intros H; simpl; trivial.
  apply add_lt_mono_l with b. rewrite add_comm, sub_add by trivial.
  destruct b as [|b]; [now destruct Hb| simpl; rewrite Pos.add_diag ].
  now destruct r.
  (* 1 *)
  destruct b as [|[ | | ]]; easy || (now destruct Hb).
Qed.

Theorem mod_lt a b : b<>0 -> a mod b < b.
Proof.
  destruct b as [ |b]. now destruct 1.
  destruct a as [ |a]. reflexivity.
  unfold modulo. simpl. apply pos_div_eucl_remainder.
Qed.

Theorem mod_bound_pos a b : 0<=a -> 0<b -> 0 <= a mod b < b.
Proof.
 intros _ H. split. apply le_0_l. apply mod_lt. now destruct b.
Qed.

(** Specification of square root *)

Lemma sqrtrem_sqrt n : fst (sqrtrem n) = sqrt n.
Proof.
 destruct n. reflexivity.
 unfold sqrtrem, sqrt, Pos.sqrt.
 destruct (Pos.sqrtrem p) as (s,r). now destruct r.
Qed.

Lemma sqrtrem_spec n :
 let (s,r) := sqrtrem n in n = s*s + r /\ r <= 2*s.
Proof.
 destruct n. now split.
 generalize (Pos.sqrtrem_spec p). simpl.
 destruct 1; simpl; subst; now split.
Qed.

Lemma sqrt_spec n : 0<=n ->
 let s := sqrt n in s*s <= n < (succ s)*(succ s).
Proof.
 intros _. destruct n. now split. apply (Pos.sqrt_spec p).
Qed.

Lemma sqrt_neg n : n<0 -> sqrt n = 0.
Proof.
 now destruct n.
Qed.

(** Specification of gcd *)

(** The first component of ggcd is gcd *)

Lemma ggcd_gcd a b : fst (ggcd a b) = gcd a b.
Proof.
 destruct a as [|p], b as [|q]; simpl; auto.
 assert (H := Pos.ggcd_gcd p q).
 destruct Pos.ggcd as (g,(aa,bb)); simpl; now f_equal.
Qed.

(** The other components of ggcd are indeed the correct factors. *)

Lemma ggcd_correct_divisors a b :
  let '(g,(aa,bb)) := ggcd a b in
  a=g*aa /\ b=g*bb.
Proof.
 destruct a as [|p], b as [|q]; simpl; auto.
 now rewrite Pos.mul_1_r.
 now rewrite Pos.mul_1_r.
 generalize (Pos.ggcd_correct_divisors p q).
 destruct Pos.ggcd as (g,(aa,bb)); simpl.
 destruct 1; split; now f_equal.
Qed.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma gcd_divide_l a b : (gcd a b | a).
Proof.
 rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa.
  now rewrite mul_comm.
Qed.

Lemma gcd_divide_r a b : (gcd a b | b).
Proof.
 rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb.
  now rewrite mul_comm.
Qed.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma gcd_greatest a b c : (c|a) -> (c|b) -> (c|gcd a b).
Proof.
 destruct a as [ |p], b as [ |q]; simpl; trivial.
 destruct c as [ |r]. intros (s,H). destruct s; discriminate.
 intros ([ |s],Hs) ([ |t],Ht); try discriminate; simpl in *.
 destruct (Pos.gcd_greatest p q r) as (u,H).
 exists s. now inversion Hs.
 exists t. now inversion Ht.
 exists (pos u). simpl; now f_equal.
Qed.

Lemma gcd_nonneg a b : 0 <= gcd a b.
Proof. apply le_0_l. Qed.

(** Specification of bitwise functions *)

(** Correctness proofs for [testbit]. *)

Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof.
 now destruct a.
Qed.

Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof.
 now destruct a.
Qed.

Lemma testbit_succ_r_div2 a n : 0<=n ->
 testbit a (succ n) = testbit (div2 a) n.
Proof.
 intros _. destruct a as [|[a|a| ]], n as [|n]; simpl; trivial;
  f_equal; apply Pos.pred_N_succ.
Qed.

Lemma testbit_odd_succ a n : 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof.
 intros H. rewrite testbit_succ_r_div2 by trivial. f_equal. now destruct a.
Qed.

Lemma testbit_even_succ a n : 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof.
 intros H. rewrite testbit_succ_r_div2 by trivial. f_equal. now destruct a.
Qed.

Lemma testbit_neg_r a n : n<0 -> testbit a n = false.
Proof.
 now destruct n.
Qed.

(** Correctness proofs for shifts *)

Lemma shiftr_succ_r a n :
 shiftr a (succ n) = div2 (shiftr a n).
Proof.
 destruct n; simpl; trivial. apply Pos.iter_succ.
Qed.

Lemma shiftl_succ_r a n :
 shiftl a (succ n) = double (shiftl a n).
Proof.
 destruct n, a; simpl; trivial. f_equal. apply Pos.iter_succ.
Qed.

Lemma shiftr_spec a n m : 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros _. revert a m.
 induction n using peano_ind; intros a m. now rewrite add_0_r.
 rewrite add_comm, add_succ_l, add_comm, <- add_succ_l.
 now rewrite <- IHn, testbit_succ_r_div2, shiftr_succ_r by apply le_0_l.
Qed.

Lemma shiftl_spec_high a n m : 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros _ H.
 rewrite <- (sub_add n m H) at 1.
 set (m' := m-n). clearbody m'. clear H m. revert a m'.
 induction n using peano_ind; intros a m.
 rewrite add_0_r; now destruct a.
 rewrite shiftl_succ_r.
 rewrite add_comm, add_succ_l, add_comm.
 now rewrite testbit_succ_r_div2, div2_double by apply le_0_l.
Qed.

Lemma shiftl_spec_low a n m : m<n ->
 testbit (shiftl a n) m = false.
Proof.
 revert a m.
 induction n using peano_ind; intros a m H.
 elim (le_0_l m). now rewrite compare_antisym, H.
 rewrite shiftl_succ_r.
 destruct m. now destruct (shiftl a n).
 rewrite <- (succ_pos_pred p), testbit_succ_r_div2, div2_double by apply le_0_l.
 apply IHn.
 apply add_lt_mono_l with 1. rewrite 2 (add_succ_l 0). simpl.
 now rewrite succ_pos_pred.
Qed.

Definition div2_spec a : div2 a = shiftr a 1.
Proof.
 reflexivity.
Qed.

(** Semantics of bitwise operations *)

Lemma pos_lxor_spec p p' n :
 testbit (Pos.lxor p p') n = xorb (Pos.testbit p n) (Pos.testbit p' n).
Proof.
 revert p' n.
 induction p as [p IH|p IH|]; intros [p'|p'|] [|n]; trivial; simpl;
 (specialize (IH p'); destruct Pos.lxor; trivial; now rewrite <-IH) ||
 (now destruct Pos.testbit).
Qed.

Lemma lxor_spec a a' n :
 testbit (lxor a a') n = xorb (testbit a n) (testbit a' n).
Proof.
 destruct a, a'; simpl; trivial.
 now destruct Pos.testbit.
 now destruct Pos.testbit.
 apply pos_lxor_spec.
Qed.

Lemma pos_lor_spec p p' n :
 Pos.testbit (Pos.lor p p') n = (Pos.testbit p n) || (Pos.testbit p' n).
Proof.
 revert p' n.
 induction p as [p IH|p IH|]; intros [p'|p'|] [|n]; trivial; simpl;
  apply IH || now rewrite orb_false_r.
Qed.

Lemma lor_spec a a' n :
 testbit (lor a a') n = (testbit a n) || (testbit a' n).
Proof.
 destruct a, a'; simpl; trivial.
 now rewrite orb_false_r.
 apply pos_lor_spec.
Qed.

Lemma pos_land_spec p p' n :
 testbit (Pos.land p p') n = (Pos.testbit p n) && (Pos.testbit p' n).
Proof.
 revert p' n.
 induction p as [p IH|p IH|]; intros [p'|p'|] [|n]; trivial; simpl;
 (specialize (IH p'); destruct Pos.land; trivial; now rewrite <-IH) ||
 (now rewrite andb_false_r).
Qed.

Lemma land_spec a a' n :
 testbit (land a a') n = (testbit a n) && (testbit a' n).
Proof.
 destruct a, a'; simpl; trivial.
 now rewrite andb_false_r.
 apply pos_land_spec.
Qed.

Lemma pos_ldiff_spec p p' n :
 testbit (Pos.ldiff p p') n = (Pos.testbit p n) && negb (Pos.testbit p' n).
Proof.
 revert p' n.
 induction p as [p IH|p IH|]; intros [p'|p'|] [|n]; trivial; simpl;
 (specialize (IH p'); destruct Pos.ldiff; trivial; now rewrite <-IH) ||
 (now rewrite andb_true_r).
Qed.

Lemma ldiff_spec a a' n :
 testbit (ldiff a a') n = (testbit a n) && negb (testbit a' n).
Proof.
 destruct a, a'; simpl; trivial.
 now rewrite andb_true_r.
 apply pos_ldiff_spec.
Qed.

(** Instantiation of generic properties of advanced functions
    (pow, sqrt, log2, div, gcd, ...) *)

Include NExtraProp.

(** In generic statements, the predicates [lt] and [le] have been
  favored, whereas [gt] and [ge] don't even exist in the abstract
  layers. The use of [gt] and [ge] is hence not recommended. We provide
  here the bare minimal results to related them with [lt] and [le]. *)

Lemma gt_lt_iff n m : n > m <-> m < n.
Proof.
 unfold lt, gt. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma gt_lt n m : n > m -> m < n.
Proof.
 apply gt_lt_iff.
Qed.

Lemma lt_gt n m : n < m -> m > n.
Proof.
 apply gt_lt_iff.
Qed.

Lemma ge_le_iff n m : n >= m <-> m <= n.
Proof.
 unfold le, ge. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma ge_le n m : n >= m -> m <= n.
Proof.
 apply ge_le_iff.
Qed.

Lemma le_ge n m : n <= m -> m >= n.
Proof.
 apply ge_le_iff.
Qed.

(** Auxiliary results about right shift on positive numbers,
    used in BinInt *)

Lemma pos_pred_shiftl_low : forall p n m, m<n ->
 testbit (Pos.pred_N (Pos.shiftl p n)) m = true.
Proof.
 induction n using peano_ind.
 now destruct m.
 intros m H. unfold Pos.shiftl.
 destruct n as [|n]; simpl in *.
 destruct m. now destruct p. elim (Pos.nlt_1_r _ H).
 rewrite Pos.iter_succ. simpl.
 set (u:=Pos.iter xO p n) in *; clearbody u.
 destruct m as [|m]. now destruct u.
 rewrite <- (IHn (Pos.pred_N m)).
 rewrite <- (testbit_odd_succ _ (Pos.pred_N m)).
 rewrite succ_pos_pred. now destruct u.
 apply le_0_l.
 apply succ_lt_mono. now rewrite succ_pos_pred.
Qed.

Lemma pos_pred_shiftl_high : forall p n m, n<=m ->
 testbit (Pos.pred_N (Pos.shiftl p n)) m =
 testbit (shiftl (Pos.pred_N p) n) m.
Proof.
 induction n using peano_ind; intros m H.
 unfold shiftl. simpl. now destruct (Pos.pred_N p).
 rewrite shiftl_succ_r.
 destruct n as [|n].
 destruct m as [|m]. now destruct H. now destruct p.
 destruct m as [|m]. now destruct H.
 rewrite <- (succ_pos_pred m).
 rewrite double_spec, testbit_even_succ by apply le_0_l.
 rewrite <- IHn.
 rewrite testbit_succ_r_div2 by apply le_0_l.
 f_equal. simpl. rewrite Pos.iter_succ.
 now destruct (Pos.iter xO p n).
 apply succ_le_mono. now rewrite succ_pos_pred.
Qed.

Lemma pred_div2_up p : Pos.pred_N (Pos.div2_up p) = div2 (Pos.pred_N p).
Proof.
 destruct p as [p|p| ]; trivial.
 simpl. apply Pos.pred_N_succ.
 destruct p; simpl; trivial.
Qed.

End N.

Bind Scope N_scope with N.t N.

(** Exportation of notations *)

Numeral Notation N N.of_uint N.to_uint : N_scope.

Infix "+" := N.add : N_scope.
Infix "-" := N.sub : N_scope.
Infix "*" := N.mul : N_scope.
Infix "^" := N.pow : N_scope.

Infix "?=" := N.compare (at level 70, no associativity) : N_scope.

Infix "<=" := N.le : N_scope.
Infix "<" := N.lt : N_scope.
Infix ">=" := N.ge : N_scope.
Infix ">" := N.gt : N_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : N_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : N_scope.
Notation "x < y < z" := (x < y /\ y < z) : N_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : N_scope.

Infix "=?" := N.eqb (at level 70, no associativity) : N_scope.
Infix "<=?" := N.leb (at level 70, no associativity) : N_scope.
Infix "<?" := N.ltb (at level 70, no associativity) : N_scope.

Infix "/" := N.div : N_scope.
Infix "mod" := N.modulo (at level 40, no associativity) : N_scope.

Notation "( p | q )" := (N.divide p q) (at level 0) : N_scope.

(** Compatibility notations *)

Notation N_rect := N_rect (only parsing).
Notation N_rec := N_rec (only parsing).
Notation N_ind := N_ind (only parsing).
Notation N0 := N0 (only parsing).
Notation Npos := N.pos (only parsing).

Notation Ndiscr := N.discr (compat "8.7").
Notation Ndouble_plus_one := N.succ_double (only parsing).
Notation Ndouble := N.double (compat "8.7").
Notation Nsucc := N.succ (compat "8.7").
Notation Npred := N.pred (compat "8.7").
Notation Nsucc_pos := N.succ_pos (compat "8.7").
Notation Ppred_N := Pos.pred_N (compat "8.7").
Notation Nplus := N.add (only parsing).
Notation Nminus := N.sub (only parsing).
Notation Nmult := N.mul (only parsing).
Notation Neqb := N.eqb (compat "8.7").
Notation Ncompare := N.compare (compat "8.7").
Notation Nlt := N.lt (compat "8.7").
Notation Ngt := N.gt (compat "8.7").
Notation Nle := N.le (compat "8.7").
Notation Nge := N.ge (compat "8.7").
Notation Nmin := N.min (compat "8.7").
Notation Nmax := N.max (compat "8.7").
Notation Ndiv2 := N.div2 (compat "8.7").
Notation Neven := N.even (compat "8.7").
Notation Nodd := N.odd (compat "8.7").
Notation Npow := N.pow (compat "8.7").
Notation Nlog2 := N.log2 (compat "8.7").

Notation nat_of_N := N.to_nat (only parsing).
Notation N_of_nat := N.of_nat (only parsing).
Notation N_eq_dec := N.eq_dec (compat "8.7").
Notation Nrect := N.peano_rect (only parsing).
Notation Nrect_base := N.peano_rect_base (only parsing).
Notation Nrect_step := N.peano_rect_succ (only parsing).
Notation Nind := N.peano_ind (only parsing).
Notation Nrec := N.peano_rec (only parsing).
Notation Nrec_base := N.peano_rec_base (only parsing).
Notation Nrec_succ := N.peano_rec_succ (only parsing).

Notation Npred_succ := N.pred_succ (compat "8.7").
Notation Npred_minus := N.pred_sub (only parsing).
Notation Nsucc_pred := N.succ_pred (compat "8.7").
Notation Ppred_N_spec := N.pos_pred_spec (only parsing).
Notation Nsucc_pos_spec := N.succ_pos_spec (compat "8.7").
Notation Ppred_Nsucc := N.pos_pred_succ (only parsing).
Notation Nplus_0_l := N.add_0_l (only parsing).
Notation Nplus_0_r := N.add_0_r (only parsing).
Notation Nplus_comm := N.add_comm (only parsing).
Notation Nplus_assoc := N.add_assoc (only parsing).
Notation Nplus_succ := N.add_succ_l (only parsing).
Notation Nsucc_0 := N.succ_0_discr (only parsing).
Notation Nsucc_inj := N.succ_inj (compat "8.7").
Notation Nminus_N0_Nle := N.sub_0_le (only parsing).
Notation Nminus_0_r := N.sub_0_r (only parsing).
Notation Nminus_succ_r:= N.sub_succ_r (only parsing).
Notation Nmult_0_l := N.mul_0_l (only parsing).
Notation Nmult_1_l := N.mul_1_l (only parsing).
Notation Nmult_1_r := N.mul_1_r (only parsing).
Notation Nmult_comm := N.mul_comm (only parsing).
Notation Nmult_assoc := N.mul_assoc (only parsing).
Notation Nmult_plus_distr_r := N.mul_add_distr_r (only parsing).
Notation Neqb_eq := N.eqb_eq (compat "8.7").
Notation Nle_0 := N.le_0_l (only parsing).
Notation Ncompare_refl := N.compare_refl (compat "8.7").
Notation Ncompare_Eq_eq := N.compare_eq (only parsing).
Notation Ncompare_eq_correct := N.compare_eq_iff (only parsing).
Notation Nlt_irrefl := N.lt_irrefl (compat "8.7").
Notation Nlt_trans := N.lt_trans (compat "8.7").
Notation Nle_lteq := N.lt_eq_cases (only parsing).
Notation Nlt_succ_r := N.lt_succ_r (compat "8.7").
Notation Nle_trans := N.le_trans (compat "8.7").
Notation Nle_succ_l := N.le_succ_l (compat "8.7").
Notation Ncompare_spec := N.compare_spec (compat "8.7").
Notation Ncompare_0 := N.compare_0_r (only parsing).
Notation Ndouble_div2 := N.div2_double (only parsing).
Notation Ndouble_plus_one_div2 := N.div2_succ_double (only parsing).
Notation Ndouble_inj := N.double_inj (compat "8.7").
Notation Ndouble_plus_one_inj := N.succ_double_inj (only parsing).
Notation Npow_0_r := N.pow_0_r (compat "8.7").
Notation Npow_succ_r := N.pow_succ_r (compat "8.7").
Notation Nlog2_spec := N.log2_spec (compat "8.7").
Notation Nlog2_nonpos := N.log2_nonpos (compat "8.7").
Notation Neven_spec := N.even_spec (compat "8.7").
Notation Nodd_spec := N.odd_spec (compat "8.7").
Notation Nlt_not_eq := N.lt_neq (only parsing).
Notation Ngt_Nlt := N.gt_lt (only parsing).

(** More complex compatibility facts, expressed as lemmas
    (to preserve scopes for instance) *)

Lemma Nplus_reg_l n m p : n + m = n + p -> m = p.
Proof (proj1 (N.add_cancel_l m p n)).
Lemma Nmult_Sn_m n m : N.succ n * m = m + n * m.
Proof (eq_trans (N.mul_succ_l n m) (N.add_comm _ _)).
Lemma Nmult_plus_distr_l n m p : p * (n + m) = p * n + p * m.
Proof (N.mul_add_distr_l p n m).
Lemma Nmult_reg_r n m p : p <> 0 -> n * p = m * p -> n = m.
Proof (fun H => proj1 (N.mul_cancel_r n m p H)).
Lemma Ncompare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof (eq_sym (N.compare_antisym n m)).

Definition N_ind_double a P f0 f2 fS2 := N.binary_ind P f0 f2 fS2 a.
Definition N_rec_double a P f0 f2 fS2 := N.binary_rec P f0 f2 fS2 a.

(** Not kept : Ncompare_n_Sm Nplus_lt_cancel_l *)
