(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Export BinNums BinPos Pnat.
Require Import BinNat Bool Plus Mult Equalities GenericMinMax
 ZAxioms ZProperties.
Require BinIntDef.

(***********************************************************)
(** * Binary Integers *)
(***********************************************************)

(** Initial author: Pierre Crégut, CNET, Lannion, France *)

(** The type [Z] and its constructors [Z0] and [Zpos] and [Zneg]
    are now defined in [BinNums.v] *)

Local Open Scope Z_scope.

(** Every definitions and early properties about binary integers
    are placed in a module [Z] for qualification purpose. *)

Module Z
 <: ZAxiomsSig
 <: UsualOrderedTypeFull
 <: UsualDecidableTypeFull
 <: TotalOrder.

(** * Definitions of operations, now in a separate file *)

Include BinIntDef.Z.

(** * Logic Predicates *)

Definition eq := @Logic.eq Z.
Definition eq_equiv := @eq_equivalence Z.

Definition lt x y := (x ?= y) = Lt.
Definition gt x y := (x ?= y) = Gt.
Definition le x y := (x ?= y) <> Gt.
Definition ge x y := (x ?= y) <> Lt.

Infix "<=" := le : Z_scope.
Infix "<" := lt : Z_scope.
Infix ">=" := ge : Z_scope.
Infix ">" := gt : Z_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

Definition divide x y := exists z, x*z = y.
Notation "( x | y )" := (divide x y) (at level 0).

Definition Even a := exists b, a = 2*b.
Definition Odd a := exists b, a = 2*b+1.

(** * Decidability of equality. *)

Definition eq_dec (x y : Z) : {x = y} + {x <> y}.
Proof.
 decide equality; apply Pos.eq_dec.
Defined.

(** * Properties of [pos_sub] *)

(** [pos_sub] can be written in term of positive comparison
    and subtraction (cf. earlier definition of addition of Z) *)

Lemma pos_sub_spec p q :
 pos_sub p q =
 match (p ?= q)%positive with
   | Eq => 0
   | Lt => Zneg (q - p)
   | Gt => Zpos (p - q)
 end.
Proof.
 revert q. induction p; destruct q; simpl; trivial;
 rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI,
  ?Pos.compare_xI_xO, ?Pos.compare_xO_xO, IHp; simpl;
 case Pos.compare_spec; intros; simpl; trivial;
  (now rewrite Pos.sub_xI_xI) || (now rewrite Pos.sub_xO_xO) ||
  (now rewrite Pos.sub_xO_xI) || (now rewrite Pos.sub_xI_xO) ||
  subst; unfold Pos.sub; simpl; now rewrite Pos.sub_mask_diag.
Qed.

(** Particular cases of the previous result *)

Lemma pos_sub_diag p : pos_sub p p = 0.
Proof.
 now rewrite pos_sub_spec, Pos.compare_refl.
Qed.

Lemma pos_sub_lt p q : (p < q)%positive -> pos_sub p q = Zneg (q - p).
Proof.
 intros H. now rewrite pos_sub_spec, H.
Qed.

Lemma pos_sub_gt p q : (q < p)%positive -> pos_sub p q = Zpos (p - q).
Proof.
 intros H. now rewrite pos_sub_spec, Pos.compare_antisym, H.
Qed.

(** The opposite of [pos_sub] is [pos_sub] with reversed arguments *)

Lemma pos_sub_opp p q : - pos_sub p q = pos_sub q p.
Proof.
 revert q; induction p; destruct q; simpl; trivial;
 rewrite <- IHp; now destruct pos_sub.
Qed.

(** * Results concerning [Zpos] and [Zneg] and the operators *)

Lemma opp_Zneg p : - Zneg p = Zpos p.
Proof.
 reflexivity.
Qed.

Lemma opp_Zpos p : - Zpos p = Zneg p.
Proof.
 reflexivity.
Qed.

Lemma succ_Zpos p : succ (Zpos p) = Zpos (Pos.succ p).
Proof.
 simpl. f_equal. apply Pos.add_1_r.
Qed.

Lemma add_Zpos p q : Zpos p + Zpos q = Zpos (p+q).
Proof.
 reflexivity.
Qed.

Lemma add_Zneg p q : Zneg p + Zneg q = Zneg (p+q).
Proof.
 reflexivity.
Qed.

Lemma add_Zpos_Zneg p q : Zpos p + Zneg q = pos_sub p q.
Proof.
 reflexivity.
Qed.

Lemma add_Zneg_Zpos p q : Zneg p + Zpos q = pos_sub q p.
Proof.
 reflexivity.
Qed.

Lemma sub_Zpos n m : (n < m)%positive -> Zpos m - Zpos n = Zpos (m-n).
Proof.
 intros H. simpl. now apply pos_sub_gt.
Qed.

Lemma mul_Zpos (p q : positive) : Zpos p * Zpos q = Zpos (p*q).
Proof.
 reflexivity.
Qed.

Lemma pow_Zpos p q : (Zpos p)^(Zpos q) = Zpos (p^q).
Proof.
 unfold Pos.pow, pow, pow_pos.
 symmetry. now apply Pos.iter_swap_gen.
Qed.

Lemma inj_Zpos p q : Zpos p = Zpos q <-> p = q.
Proof.
 split; intros H. now injection H. now f_equal.
Qed.

Lemma inj_Zneg p q : Zneg p = Zneg q <-> p = q.
Proof.
 split; intros H. now injection H. now f_equal.
Qed.

Lemma pos_xI p : Zpos p~1 = 2 * Zpos p + 1.
Proof.
 reflexivity.
Qed.

Lemma pos_xO p : Zpos p~0 = 2 * Zpos p.
Proof.
 reflexivity.
Qed.

Lemma neg_xI p : Zneg p~1 = 2 * Zneg p - 1.
Proof.
 reflexivity.
Qed.

Lemma neg_xO p : Zneg p~0 = 2 * Zneg p.
Proof.
 reflexivity.
Qed.

(** In the following module, we group results that are needed now
  to prove specifications of operations, but will also be provided
  later by the generic functor of properties. *)

Module Import BootStrap.

(** * Properties of addition *)

(** ** Zero is neutral for addition *)

Lemma add_0_r n : n + 0 = n.
Proof.
 now destruct n.
Qed.

(** ** Addition is commutative *)

Lemma add_comm n m : n + m = m + n.
Proof.
 destruct n, m; simpl; trivial; now rewrite Pos.add_comm.
Qed.

(** ** Opposite distributes over addition *)

Lemma opp_add_distr n m : - (n + m) = - n + - m.
Proof.
 destruct n, m; simpl; trivial using pos_sub_opp.
Qed.

(** ** Opposite is injective *)

Lemma opp_inj n m : -n = -m -> n = m.
Proof.
 destruct n, m; simpl; intros H; destr_eq H; now f_equal.
Qed.

(** ** Addition is associative *)

Lemma pos_sub_add p q r :
  pos_sub (p + q) r = Zpos p + pos_sub q r.
Proof.
 simpl. rewrite !pos_sub_spec.
 case (Pos.compare_spec q r); intros E0.
 (* q = r *)
 subst.
 assert (H := Pos.lt_add_r r p).
 rewrite Pos.add_comm in H. apply Pos.lt_gt in H.
 now rewrite H, Pos.add_sub.
 (* q < r *)
 rewrite pos_sub_spec.
 assert (Hr : (r = (r-q)+q)%positive) by (now rewrite Pos.sub_add).
 rewrite Hr at 1. rewrite Pos.add_compare_mono_r.
 case Pos.compare_spec; intros E1; trivial; f_equal.
 rewrite Pos.add_comm. apply Pos.sub_add_distr.
 rewrite Hr, Pos.add_comm. now apply Pos.add_lt_mono_r.
 symmetry. apply Pos.sub_sub_distr; trivial.
 (* r < q *)
 assert (LT : (r < p + q)%positive).
  apply Pos.lt_trans with q; trivial. rewrite Pos.add_comm. apply Pos.lt_add_r.
 apply Pos.lt_gt in LT. rewrite LT. f_equal.
 symmetry. now apply Pos.add_sub_assoc.
Qed.

Lemma add_assoc n m p : n + (m + p) = n + m + p.
Proof.
 assert (AUX : forall x y z, Zpos x + (y + z) = Zpos x + y + z).
  intros x [|y|y] [|z|z]; rewrite ?add_0_r; trivial.
  simpl. now rewrite Pos.add_assoc.
  simpl (_ + Zneg _). symmetry. apply pos_sub_add.
  simpl (Zneg _ + _); simpl (_ + Zneg _).
  now rewrite (add_comm _ (Zpos _)), <- 2 pos_sub_add, Pos.add_comm.
  apply opp_inj. rewrite !opp_add_distr, opp_Zpos, !opp_Zneg.
  simpl (Zneg _ + _); simpl (_ + Zneg _).
  rewrite add_comm, Pos.add_comm. apply pos_sub_add.
 (* main *)
 destruct n as [|n|n]. trivial. apply AUX.
 apply opp_inj. rewrite !opp_add_distr, opp_Zneg. apply AUX.
Qed.

(** ** Subtraction and successor *)

Lemma sub_succ_l n m : succ n - m = succ (n - m).
Proof.
 unfold sub, succ. now rewrite <- 2 add_assoc, (add_comm 1).
Qed.

(** ** Opposite is inverse for addition *)

Lemma add_opp_diag_r n : n + - n = 0.
Proof.
 destruct n; simpl; trivial; now rewrite pos_sub_diag.
Qed.

Lemma add_opp_diag_l n : - n + n = 0.
Proof.
 rewrite add_comm. apply add_opp_diag_r.
Qed.

(** ** Commutativity of multiplication *)

Lemma mul_comm n m : n * m = m * n.
Proof.
 destruct n, m; simpl; trivial; f_equal; apply Pos.mul_comm.
Qed.

(** ** Associativity of multiplication *)

Lemma mul_assoc n m p : n * (m * p) = n * m * p.
Proof.
 destruct n, m, p; simpl; trivial; f_equal; apply Pos.mul_assoc.
Qed.

(** Multiplication and constants *)

Lemma mul_1_l n : 1 * n = n.
Proof.
 now destruct n.
Qed.

Lemma mul_1_r n : n * 1 = n.
Proof.
 destruct n; simpl; now rewrite ?Pos.mul_1_r.
Qed.

(** ** Multiplication and Opposite *)

Lemma mul_opp_l n m : - n * m = - (n * m).
Proof.
 now destruct n, m.
Qed.

Lemma mul_opp_r n m : n * - m = - (n * m).
Proof.
 now destruct n, m.
Qed.

Lemma mul_opp_opp n m : - n * - m = n * m.
Proof.
 now destruct n, m.
Qed.

Lemma mul_opp_comm n m : - n * m = n * - m.
Proof.
 now destruct n, m.
Qed.

(** ** Distributivity of multiplication over addition *)

Lemma mul_add_distr_pos (p:positive) n m :
 Zpos p * (n + m) = Zpos p * n + Zpos p * m.
Proof.
 destruct n as [|n|n], m as [|m|m]; simpl; trivial;
 rewrite ?pos_sub_spec, ?Pos.mul_compare_mono_l; try case Pos.compare_spec;
 intros; now rewrite ?Pos.mul_add_distr_l, ?Pos.mul_sub_distr_l.
Qed.

Lemma mul_add_distr_l n m p : n * (m + p) = n * m + n * p.
Proof.
 destruct n as [|n|n]. trivial.
 apply mul_add_distr_pos.
 rewrite <- opp_Zpos, !mul_opp_l, <- opp_add_distr. f_equal.
 apply mul_add_distr_pos.
Qed.

Lemma mul_add_distr_r n m p : (n + m) * p = n * p + m * p.
Proof.
 rewrite !(mul_comm _ p). apply mul_add_distr_l.
Qed.

End BootStrap.

(** * Proofs of specifications *)

(** ** Specification of constants *)

Lemma one_succ : 1 = succ 0.
Proof.
reflexivity.
Qed.

Lemma two_succ : 2 = succ 1.
Proof.
reflexivity.
Qed.

(** ** Specification of addition *)

Lemma add_0_l n : 0 + n = n.
Proof.
 now destruct n.
Qed.

Lemma add_succ_l n m : succ n + m = succ (n + m).
Proof.
 unfold succ. now rewrite 2 (add_comm _ 1), add_assoc.
Qed.

(** ** Specification of opposite *)

Lemma opp_0 : -0 = 0.
Proof.
 reflexivity.
Qed.

Lemma opp_succ n : -(succ n) = pred (-n).
Proof.
 unfold succ, pred. apply opp_add_distr.
Qed.

(** ** Specification of successor and predecessor *)

Lemma succ_pred n : succ (pred n) = n.
Proof.
 unfold succ, pred. now rewrite <- add_assoc, add_opp_diag_r, add_0_r.
Qed.

Lemma pred_succ n : pred (succ n) = n.
Proof.
 unfold succ, pred. now rewrite <- add_assoc, add_opp_diag_r, add_0_r.
Qed.

(** ** Specification of subtraction *)

Lemma sub_0_r n : n - 0 = n.
Proof.
 apply add_0_r.
Qed.

Lemma sub_succ_r n m : n - succ m = pred (n - m).
Proof.
 unfold sub, succ, pred. now rewrite opp_add_distr, add_assoc.
Qed.

(** ** Specification of multiplication *)

Lemma mul_0_l n : 0 * n = 0.
Proof.
 reflexivity.
Qed.

Lemma mul_succ_l n m : succ n * m = n * m + m.
Proof.
 unfold succ. now rewrite mul_add_distr_r, mul_1_l.
Qed.

(** ** Specification of order *)

Lemma compare_refl n : (n ?= n) = Eq.
Proof.
 destruct n; simpl; trivial; now rewrite Pos.compare_refl.
Qed.

Lemma compare_eq n m : (n ?= m) = Eq -> n = m.
Proof.
destruct n, m; simpl; try easy; intros; f_equal.
now apply Pos.compare_eq.
apply Pos.compare_eq, CompOpp_inj. now rewrite H.
Qed.

Lemma compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof.
split; intros. now apply compare_eq. subst; now apply compare_refl.
Qed.

Lemma compare_antisym n m : CompOpp (n ?= m) = (m ?= n).
Proof.
destruct n, m; simpl; trivial.
symmetry. apply Pos.compare_antisym. (* TODO : quel sens ? *)
f_equal. symmetry. apply Pos.compare_antisym.
Qed.

Lemma compare_sub n m : (n ?= m) = (n - m ?= 0).
Proof.
 destruct n as [|n|n], m as [|m|m]; simpl; trivial;
 rewrite <- ? Pos.compare_antisym, ?pos_sub_spec;
 case Pos.compare_spec; trivial.
Qed.

Lemma compare_spec n m : CompareSpec (n=m) (n<m) (m<n) (n ?= m).
Proof.
 case_eq (n ?= m); intros H; constructor; trivial.
 now apply compare_eq.
 red. now rewrite <- compare_antisym, H.
Qed.

Lemma lt_irrefl n : ~ n < n.
Proof.
 unfold lt. now rewrite compare_refl.
Qed.

Lemma lt_eq_cases n m : n <= m <-> n < m \/ n = m.
Proof.
 unfold le, lt. rewrite <- compare_eq_iff.
 case compare; now intuition.
Qed.

Lemma lt_succ_r n m : n < succ m <-> n<=m.
Proof.
 unfold lt, le. rewrite compare_sub, sub_succ_r.
 rewrite (compare_sub n m).
 destruct (n-m) as [|[ | | ]|]; easy'.
Qed.

(** ** Specification of boolean comparisons *)

Lemma eqb_eq n m : (n =? m) = true <-> n = m.
Proof.
 destruct n, m; simpl; try (now split).
 rewrite inj_Zpos. apply Pos.eqb_eq.
 rewrite inj_Zneg. apply Pos.eqb_eq.
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
 unfold ltb, lt. destruct compare; easy'.
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
 unfold leb, le. destruct compare; easy'.
Qed.

Lemma leb_spec n m : BoolSpec (n<=m) (m<n) (n <=? m).
Proof.
 unfold le, lt, leb. rewrite <- (compare_antisym n m).
 case compare; now constructor.
Qed.

Lemma ltb_spec n m : BoolSpec (n<m) (m<=n) (n <? m).
Proof.
 unfold le, lt, ltb. rewrite <- (compare_antisym n m).
 case compare; now constructor.
Qed.

Lemma gtb_ltb n m : (n >? m) = (m <? n).
Proof.
 unfold gtb, ltb. rewrite <- compare_antisym. now case compare.
Qed.

Lemma geb_leb n m : (n >=? m) = (m <=? n).
Proof.
 unfold geb, leb. rewrite <- compare_antisym. now case compare.
Qed.

Lemma gtb_lt n m : (n >? m) = true <-> m < n.
Proof.
 rewrite gtb_ltb. apply ltb_lt.
Qed.

Lemma geb_le n m : (n >=? m) = true <-> m <= n.
Proof.
 rewrite geb_leb. apply leb_le.
Qed.

Lemma gtb_spec n m : BoolSpec (m<n) (n<=m) (n >? m).
Proof.
 rewrite gtb_ltb. apply ltb_spec.
Qed.

Lemma geb_spec n m : BoolSpec (m<=n) (n<m) (n >=? m).
Proof.
 rewrite geb_leb. apply leb_spec.
Qed.

(** ** Specification of minimum and maximum *)

Lemma max_l n m : m<=n -> max n m = n.
Proof.
 unfold le, max. rewrite <- (compare_antisym n m).
 case compare; intuition.
Qed.

Lemma max_r n m :  n<=m -> max n m = m.
Proof.
 unfold le, max. case compare_spec; intuition.
Qed.

Lemma min_l n m : n<=m -> min n m = n.
Proof.
 unfold le, min. case compare_spec; intuition.
Qed.

Lemma min_r n m : m<=n -> min n m = m.
Proof.
 unfold le, min.
 rewrite <- (compare_antisym n m). case compare_spec; intuition.
Qed.

(** ** Specification of absolute value *)

Lemma abs_eq n : 0 <= n -> abs n = n.
Proof.
 destruct n; trivial. now destruct 1.
Qed.

Lemma abs_neq n : n <= 0 -> abs n = - n.
Proof.
 destruct n; trivial. now destruct 1.
Qed.

(** ** Specification of sign *)

Lemma sgn_null n : n = 0 -> sgn n = 0.
Proof.
 intros. now subst.
Qed.

Lemma sgn_pos n : 0 < n -> sgn n = 1.
Proof.
 now destruct n.
Qed.

Lemma sgn_neg n : n < 0 -> sgn n = -1.
Proof.
 now destruct n.
Qed.

(** ** Specification of power *)

Lemma pow_0_r n : n^0 = 1.
Proof.
 reflexivity.
Qed.

Lemma pow_succ_r n m : 0<=m -> n^(succ m) = n * n^m.
Proof.
 destruct m as [|m|m]; (now destruct 1) || (intros _); simpl; trivial.
 unfold pow_pos. now rewrite Pos.add_comm, Pos.iter_add.
Qed.

Lemma pow_neg_r n m : m<0 -> n^m = 0.
Proof.
 now destruct m.
Qed.

(** ** Specification of square root *)

Lemma sqrtrem_spec n : 0<=n ->
 let (s,r) := sqrtrem n in n = s*s + r /\ 0 <= r <= 2*s.
Proof.
 destruct n. now repeat split.
 generalize (Pos.sqrtrem_spec p). simpl.
 destruct 1; simpl; subst; now repeat split.
 now destruct 1.
Qed.

Lemma sqrt_spec n : 0<=n ->
 let s := sqrt n in s*s <= n < (succ s)*(succ s).
Proof.
 destruct n. now repeat split. unfold sqrt.
 rewrite succ_Zpos. intros _. apply (Pos.sqrt_spec p).
 now destruct 1.
Qed.

Lemma sqrt_neg n : n<0 -> sqrt n = 0.
Proof.
 now destruct n.
Qed.

Lemma sqrtrem_sqrt n : fst (sqrtrem n) = sqrt n.
Proof.
 destruct n; try reflexivity.
 unfold sqrtrem, sqrt, Pos.sqrt.
 destruct (Pos.sqrtrem p) as (s,r). now destruct r.
Qed.

(** ** Specification of logarithm *)

Lemma log2_spec n : 0 < n -> 2^(log2 n) <= n < 2^(succ (log2 n)).
Proof.
 destruct n as [|[p|p|]|]; intros Hn; split; try easy; unfold log2;
  rewrite ?succ_Zpos, pow_Zpos.
 change (2^Pos.size p <= Pos.succ (p~0))%positive.
 apply Pos.lt_le_incl, Pos.lt_succ_r, Pos.size_le.
 apply Pos.size_gt.
 apply Pos.size_le.
 apply Pos.size_gt.
Qed.

Lemma log2_nonpos n : n<=0 -> log2 n = 0.
Proof.
 destruct n as [|p|p]; trivial; now destruct 1.
Qed.

(** Specification of parity functions *)

Lemma even_spec n : even n = true <-> Even n.
Proof.
 split.
 exists (div2 n). now destruct n as [|[ | | ]|[ | | ]].
 intros (m,->). now destruct m.
Qed.

Lemma odd_spec n : odd n = true <-> Odd n.
Proof.
 split.
 exists (div2 n). destruct n as [|[ | | ]|[ | | ]]; simpl; try easy.
 now rewrite Pos.pred_double_succ.
 intros (m,->). now destruct m as [|[ | | ]|[ | | ]].
Qed.

(** ** Multiplication and Doubling *)

Lemma double_spec n : double n = 2*n.
Proof.
 reflexivity.
Qed.

Lemma succ_double_spec n : succ_double n = 2*n + 1.
Proof.
 now destruct n.
Qed.

Lemma pred_double_spec n : pred_double n = 2*n - 1.
Proof.
 now destruct n.
Qed.

(** ** Correctness proofs for Trunc division *)

Lemma pos_div_eucl_eq a b : 0 < b ->
  let (q, r) := pos_div_eucl a b in Zpos a = q * b + r.
Proof.
 intros Hb.
 induction a; unfold pos_div_eucl; fold pos_div_eucl.
 (* ~1 *)
 destruct pos_div_eucl as (q,r).
 rewrite pos_xI, IHa, mul_add_distr_l, mul_assoc.
 destruct gtb.
 now rewrite add_assoc.
 rewrite mul_add_distr_r, mul_1_l, <- !add_assoc. f_equal.
 unfold sub. now rewrite (add_comm _ (-b)), add_assoc, add_opp_diag_r.
 (* ~0 *)
 destruct pos_div_eucl as (q,r).
 rewrite (pos_xO a), IHa, mul_add_distr_l, mul_assoc.
 destruct gtb.
 trivial.
 rewrite mul_add_distr_r, mul_1_l, <- !add_assoc. f_equal.
 unfold sub. now rewrite (add_comm _ (-b)), add_assoc, add_opp_diag_r.
 (* ~1 *)
 case geb_spec; trivial.
 intros Hb'.
 destruct b as [|b|b]; try easy; clear Hb.
 replace b with 1%positive; trivial.
 apply Pos.le_antisym. apply Pos.le_1_l. now apply Pos.lt_succ_r.
Qed.

Lemma div_eucl_eq a b : b<>0 ->
 let (q, r) := div_eucl a b in a = b * q + r.
Proof.
 destruct a as [ |a|a], b as [ |b|b]; unfold div_eucl; trivial;
  (now destruct 1) || intros _;
  generalize (pos_div_eucl_eq a (Zpos b) (eq_refl _));
  destruct pos_div_eucl as (q,r); rewrite <- ?opp_Zpos, mul_comm;
  intros ->.
 (* Zpos Zpos *)
 trivial.
 (* Zpos Zneg *)
 destruct r as [ |r|r]; rewrite !mul_opp_opp; trivial;
  rewrite mul_add_distr_l, mul_1_r, <- add_assoc; f_equal;
  now rewrite add_assoc, add_opp_diag_r.
 (* Zneg Zpos *)
 rewrite (opp_add_distr _ r), <- mul_opp_r.
 destruct r as [ |r|r]; trivial;
  rewrite opp_add_distr, mul_add_distr_l, <- add_assoc; f_equal;
  unfold sub; now rewrite add_assoc, mul_opp_r, mul_1_r, add_opp_diag_l.
 (* Zneg Zneg *)
 now rewrite opp_add_distr, <- mul_opp_l.
Qed.

Lemma div_mod a b : b<>0 -> a = b*(a/b) + (a mod b).
Proof.
 intros Hb. generalize (div_eucl_eq a b Hb).
 unfold div, modulo. now destruct div_eucl.
Qed.

Lemma pos_div_eucl_bound a b : 0<b -> 0 <= snd (pos_div_eucl a b) < b.
Proof.
 assert (AUX : forall m p, m < Zpos (p~0) -> m - Zpos p < Zpos p).
  intros m p. unfold lt.
  rewrite (compare_sub m), (compare_sub _ (Zpos _)). unfold sub.
  rewrite <- add_assoc. simpl opp; simpl (Zneg _ + _).
  now rewrite Pos.add_diag.
 intros Hb.
 destruct b as [|b|b]; discriminate Hb || clear Hb.
 induction a; unfold pos_div_eucl; fold pos_div_eucl.
 (* ~1 *)
 destruct pos_div_eucl as (q,r).
 simpl in IHa; destruct IHa as (Hr,Hr').
 case gtb_spec; intros H; unfold snd. split; trivial. now destruct r.
 split. unfold le.
  now rewrite <- compare_antisym, <- compare_sub, compare_antisym.
 apply AUX. rewrite <- succ_double_spec.
 destruct r; try easy. unfold lt in *; simpl in *.
  now rewrite Pos.compare_xI_xO, Hr'.
 (* ~0 *)
 destruct pos_div_eucl as (q,r).
 simpl in IHa; destruct IHa as (Hr,Hr').
 case gtb_spec; intros H; unfold snd. split; trivial. now destruct r.
 split. unfold le.
  now rewrite <- compare_antisym, <- compare_sub, compare_antisym.
 apply AUX. destruct r; try easy.
 (* 1 *)
 case geb_spec; intros H; simpl; split; try easy.
 red; simpl. now apply Pos.le_succ_l.
Qed.

Lemma mod_pos_bound a b : 0 < b -> 0 <= a mod b < b.
Proof.
 destruct b as [|b|b]; try easy; intros _.
 destruct a as [|a|a]; unfold modulo, div_eucl.
 now split.
 now apply pos_div_eucl_bound.
 generalize (pos_div_eucl_bound a (Zpos b) (eq_refl _)).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split. unfold le.
  now rewrite <- compare_antisym, <- compare_sub, compare_antisym, Hr'.
 unfold lt in *; simpl in *. rewrite pos_sub_gt by trivial.
 simpl. now apply Pos.sub_decr.
Qed.

Definition mod_bound_pos a b (_:0<=a) := mod_pos_bound a b.

Lemma mod_neg_bound a b : b < 0 -> b < a mod b <= 0.
Proof.
 destruct b as [|b|b]; try easy; intros _.
 destruct a as [|a|a]; unfold modulo, div_eucl.
 now split.
 generalize (pos_div_eucl_bound a (Zpos b) (eq_refl _)).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split.
 unfold lt in *; simpl in *. rewrite pos_sub_lt by trivial.
 rewrite <- Pos.compare_antisym. now apply Pos.sub_decr.
 change (Zneg b - Zneg r <= 0). unfold le, lt in *.
  rewrite <- compare_sub. simpl in *.
  now rewrite <- Pos.compare_antisym, Hr'.
 generalize (pos_div_eucl_bound a (Zpos b) (eq_refl _)).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 split; destruct r; try easy.
  red; simpl; now rewrite <- Pos.compare_antisym.
Qed.

(** ** Correctness proofs for Floor division *)

Theorem quotrem_eq a b : let (q,r) := quotrem a b in a = q * b + r.
Proof.
 destruct a as [|a|a], b as [|b|b]; simpl; trivial;
 generalize (N.pos_div_eucl_spec a (Npos b)); case N.pos_div_eucl; trivial;
  intros q r; rewrite <- ?opp_Zpos;
  change (Zpos a) with (of_N (Npos a)); intros ->; now destruct q, r.
Qed.

Lemma quot_rem' a b : a = b*(a÷b) + rem a b.
Proof.
 rewrite mul_comm. generalize (quotrem_eq a b).
 unfold quot, rem. now destruct quotrem.
Qed.

Lemma quot_rem a b : b<>0 -> a = b*(a÷b) + rem a b.
Proof. intros _. apply quot_rem'. Qed.

Lemma rem_bound_pos a b : 0<=a -> 0<b -> 0 <= rem a b < b.
Proof.
 intros Ha Hb.
 destruct b as [|b|b]; (now discriminate Hb) || clear Hb;
 destruct a as [|a|a]; (now destruct Ha) || clear Ha.
 compute. now split.
 unfold rem, quotrem.
 assert (H := N.pos_div_eucl_remainder a (Npos b)).
 destruct N.pos_div_eucl as (q,[|r]); simpl; split; try easy.
 now apply H.
Qed.

Lemma rem_opp_l' a b : rem (-a) b = - (rem a b).
Proof.
 destruct a, b; trivial; unfold rem; simpl;
  now destruct N.pos_div_eucl as (q,[|r]).
Qed.

Lemma rem_opp_r' a b : rem a (-b) = rem a b.
Proof.
 destruct a, b; trivial; unfold rem; simpl;
  now destruct N.pos_div_eucl as (q,[|r]).
Qed.

Lemma rem_opp_l a b : b<>0 -> rem (-a) b = - (rem a b).
Proof. intros _. apply rem_opp_l'. Qed.

Lemma rem_opp_r a b : b<>0 -> rem a (-b) = rem a b.
Proof. intros _. apply rem_opp_r'. Qed.

(** ** Basic properties of divisibility *)

Lemma divide_Zpos p q : (Zpos p|Zpos q) <-> (p|q)%positive.
Proof.
 split.
 intros ([ |r|r],H); simpl in *; destr_eq H. exists r; auto.
 intros (r,H). exists (Zpos r); simpl; now f_equal.
Qed.

Lemma divide_Zpos_Zneg_r n p : (n|Zpos p) <-> (n|Zneg p).
Proof.
 split; intros (m,H); exists (-m); now rewrite mul_opp_r, H.
Qed.

Lemma divide_Zpos_Zneg_l n p : (Zpos p|n) <-> (Zneg p|n).
Proof.
 split; intros (m,H); exists (-m); now rewrite mul_opp_r, <- mul_opp_l.
Qed.

(** ** Correctness proofs for gcd *)

Lemma ggcd_gcd a b : fst (ggcd a b) = gcd a b.
Proof.
 destruct a as [ |p|p], b as [ |q|q]; simpl; auto;
  generalize (Pos.ggcd_gcd p q); destruct Pos.ggcd as (g,(aa,bb));
  simpl; congruence.
Qed.

Lemma ggcd_correct_divisors a b :
  let '(g,(aa,bb)) := ggcd a b in
  a = g*aa /\ b = g*bb.
Proof.
 destruct a as [ |p|p], b as [ |q|q]; simpl; rewrite ?Pos.mul_1_r; auto;
  generalize (Pos.ggcd_correct_divisors p q);
  destruct Pos.ggcd as (g,(aa,bb)); simpl; destruct 1; now subst.
Qed.

Lemma gcd_divide_l a b : (gcd a b | a).
Proof.
 rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa; auto.
Qed.

Lemma gcd_divide_r a b : (gcd a b | b).
Proof.
 rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb; auto.
Qed.

Lemma gcd_greatest a b c : (c|a) -> (c|b) -> (c | gcd a b).
Proof.
 assert (H : forall p q r, (r|Zpos p) -> (r|Zpos q) -> (r|Zpos (Pos.gcd p q))).
  intros p q [|r|r] H H'.
  now destruct H.
  apply divide_Zpos, Pos.gcd_greatest; now apply divide_Zpos.
  apply divide_Zpos_Zneg_l, divide_Zpos, Pos.gcd_greatest;
   now apply divide_Zpos, divide_Zpos_Zneg_l.
 destruct a, b; simpl; auto; intros; try apply H; trivial;
  now apply divide_Zpos_Zneg_r.
Qed.

Lemma gcd_nonneg a b : 0 <= gcd a b.
Proof.
 now destruct a, b.
Qed.

(** ggcd and opp : an auxiliary result used in QArith *)

Theorem ggcd_opp a b :
  ggcd (-a) b = (let '(g,(aa,bb)) := ggcd a b in (g,(-aa,bb))).
Proof.
 destruct a as [|a|a], b as [|b|b]; unfold ggcd, opp; auto;
  destruct (Pos.ggcd a b) as (g,(aa,bb)); auto.
Qed.

(** ** Conversions between [Z.testbit] and [N.testbit] *)

Lemma testbit_of_N a n :
 testbit (of_N a) (of_N n) = N.testbit a n.
Proof.
 destruct a as [|a], n; simpl; trivial. now destruct a.
Qed.

Lemma testbit_of_N' a n : 0<=n ->
 testbit (of_N a) n = N.testbit a (to_N n).
Proof.
 intro Hn. rewrite <- testbit_of_N. f_equal.
 destruct n; trivial; now destruct Hn.
Qed.

Lemma testbit_Zpos a n : 0<=n ->
 testbit (Zpos a) n = N.testbit (Npos a) (to_N n).
Proof.
 intro Hn. now rewrite <- testbit_of_N'.
Qed.

Lemma testbit_Zneg a n : 0<=n ->
 testbit (Zneg a) n = negb (N.testbit (Pos.pred_N a) (to_N n)).
Proof.
 intro Hn.
 rewrite <- testbit_of_N' by trivial.
 destruct n as [ |n|n];
  [ | simpl; now destruct (Ppred_N a) | now destruct Hn].
 unfold testbit.
 now destruct a as [|[ | | ]| ].
Qed.

(** ** Proofs of specifications for bitwise operations *)

Lemma div2_spec a : div2 a = shiftr a 1.
Proof.
 reflexivity.
Qed.

Lemma testbit_0_l n : testbit 0 n = false.
Proof.
 now destruct n.
Qed.

Lemma testbit_neg_r a n : n<0 -> testbit a n = false.
Proof.
 now destruct n.
Qed.

Lemma testbit_odd_0 a : testbit (2*a+1) 0 = true.
Proof.
 now destruct a as [|a|[a|a|]].
Qed.

Lemma testbit_even_0 a : testbit (2*a) 0 = false.
Proof.
 now destruct a.
Qed.

Lemma testbit_odd_succ a n : 0<=n ->
 testbit (2*a+1) (succ n) = testbit a n.
Proof.
 destruct n as [|n|n]; (now destruct 1) || intros _.
 destruct a as [|[a|a|]|[a|a|]]; simpl; trivial. now destruct a.
 unfold testbit. rewrite succ_Zpos.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.pred_N_succ; now destruct n.
Qed.

Lemma testbit_even_succ a n : 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof.
 destruct n as [|n|n]; (now destruct 1) || intros _.
 destruct a as [|[a|a|]|[a|a|]]; simpl; trivial. now destruct a.
 unfold testbit. rewrite succ_Zpos.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.pred_N_succ; now destruct n.
Qed.

Lemma div2_of_N n : of_N (N.div2 n) = div2 (of_N n).
Proof.
 now destruct n as [|[ | | ]].
Qed.

(** Correctness proofs about [Zshiftr] and [Zshiftl] *)

Lemma shiftr_spec_aux a n m : 0<=n -> 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros Hn Hm. unfold shiftr.
 destruct n as [ |n|n]; (now destruct Hn) || clear Hn; simpl.
 now rewrite add_0_r.
 assert (forall p, to_N (m + Zpos p) = (to_N m + Npos p)%N).
  destruct m; trivial; now destruct Hm.
 assert (forall p, 0 <= m + Zpos p).
  destruct m; easy || now destruct Hm.
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (Pos.iter n div2 0) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 now rewrite 2 testbit_0_l.
 (* a > 0 *)
 change (Zpos a) with (of_N (Npos a)) at 1.
 rewrite <- (Pos.iter_swap_gen _ _ _ Ndiv2) by exact div2_of_N.
 rewrite testbit_Zpos, testbit_of_N', H; trivial.
 exact (N.shiftr_spec' (Npos a) (Npos n) (to_N m)).
 (* a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ Pdiv2_up) by trivial.
 rewrite 2 testbit_Zneg, H; trivial. f_equal.
 rewrite (Pos.iter_swap_gen _ _ _ _ Ndiv2) by exact N.pred_div2_up.
 exact (N.shiftr_spec' (Ppred_N a) (Npos n) (to_N m)).
Qed.

Lemma shiftl_spec_low a n m : m<n ->
 testbit (shiftl a n) m = false.
Proof.
 intros H. destruct n as [|n|n], m as [|m|m]; try easy; simpl shiftl.
 destruct (Pos.succ_pred_or n) as [-> | <-];
  rewrite ?Pos.iter_succ; apply testbit_even_0.
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (Pos.iter n (mul 2) 0) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 apply testbit_0_l.
 (* a > 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite testbit_Zpos by easy.
 exact (N.shiftl_spec_low (Npos a) (Npos n) (Npos m) H).
 (* a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite testbit_Zneg by easy.
 now rewrite (N.pos_pred_shiftl_low a (Npos n)).
Qed.

Lemma shiftl_spec_high a n m : 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros Hm H.
 destruct n as [ |n|n]. simpl. now rewrite sub_0_r.
 (* n > 0 *)
 destruct m as [ |m|m]; try (now destruct H).
 assert (0 <= Zpos m - Zpos n).
  red. now rewrite <- compare_antisym, <- compare_sub, compare_antisym.
 assert (EQ : to_N (Zpos m - Zpos n) = (Npos m - Npos n)%N).
  red in H. simpl in H. simpl to_N.
  rewrite pos_sub_spec, Pos.compare_antisym.
  destruct (Pos.compare_spec n m) as [H'|H'|H']; try (now destruct H).
  subst. now rewrite N.sub_diag.
  simpl. destruct (Pos.sub_mask_pos' m n H') as (p & -> & <-).
  f_equal. now rewrite Pos.add_comm, Pos.add_sub.
 destruct a; unfold shiftl.
 (* ... a = 0 *)
 replace (Pos.iter n (mul 2) 0) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 now rewrite 2 testbit_0_l.
 (* ... a > 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite 2 testbit_Zpos, EQ by easy.
 exact (N.shiftl_spec_high' (Npos p) (Npos n) (Npos m) H).
 (* ... a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite 2 testbit_Zneg, EQ by easy. f_equal.
 simpl to_N.
 rewrite <- N.shiftl_spec_high by easy.
 now apply (N.pos_pred_shiftl_high p (Npos n)).
 (* n < 0 *)
 unfold sub. simpl.
 now apply (shiftr_spec_aux a (Zpos n) m).
Qed.

Lemma shiftr_spec a n m : 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros Hm.
 destruct (leb_spec 0 n).
 now apply shiftr_spec_aux.
 destruct (leb_spec (-n) m) as [LE|GT].
 unfold shiftr.
 rewrite (shiftl_spec_high a (-n) m); trivial. now destruct n.
 unfold shiftr.
 rewrite (shiftl_spec_low a (-n) m); trivial.
 rewrite testbit_neg_r; trivial.
 red in GT. rewrite compare_sub in GT. now destruct n.
Qed.

(** Correctness proofs for bitwise operations *)

Lemma lor_spec a b n :
 testbit (lor a b) n = testbit a n || testbit b n.
Proof.
 destruct (leb_spec 0 n) as [Hn|Hn]; [|now rewrite !testbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?testbit_0_l, ?orb_false_r; trivial; unfold lor;
  rewrite ?testbit_Zpos, ?testbit_Zneg, ?N.pos_pred_succ by trivial.
 now rewrite <- N.lor_spec.
 now rewrite N.ldiff_spec, negb_andb, negb_involutive, orb_comm.
 now rewrite N.ldiff_spec, negb_andb, negb_involutive.
 now rewrite N.land_spec, negb_andb.
Qed.

Lemma land_spec a b n :
 testbit (land a b) n = testbit a n && testbit b n.
Proof.
 destruct (leb_spec 0 n) as [Hn|Hn]; [|now rewrite !testbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?testbit_0_l, ?andb_false_r; trivial; unfold land;
  rewrite ?testbit_Zpos, ?testbit_Zneg, ?testbit_of_N', ?N.pos_pred_succ
   by trivial.
 now rewrite <- N.land_spec.
 now rewrite N.ldiff_spec.
 now rewrite N.ldiff_spec, andb_comm.
 now rewrite N.lor_spec, negb_orb.
Qed.

Lemma ldiff_spec a b n :
 testbit (ldiff a b) n = testbit a n && negb (testbit b n).
Proof.
 destruct (leb_spec 0 n) as [Hn|Hn]; [|now rewrite !testbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?testbit_0_l, ?andb_true_r; trivial; unfold ldiff;
  rewrite ?testbit_Zpos, ?testbit_Zneg, ?testbit_of_N', ?N.pos_pred_succ
   by trivial.
 now rewrite <- N.ldiff_spec.
 now rewrite N.land_spec, negb_involutive.
 now rewrite N.lor_spec, negb_orb.
 now rewrite N.ldiff_spec, negb_involutive, andb_comm.
Qed.

Lemma lxor_spec a b n :
 testbit (lxor a b) n = xorb (testbit a n) (testbit b n).
Proof.
 destruct (leb_spec 0 n) as [Hn|Hn]; [|now rewrite !testbit_neg_r].
 destruct a as [ |a|a], b as [ |b|b];
  rewrite ?testbit_0_l, ?xorb_false_l, ?xorb_false_r; trivial; unfold lxor;
  rewrite ?testbit_Zpos, ?testbit_Zneg, ?testbit_of_N', ?N.pos_pred_succ
   by trivial.
 now rewrite <- N.lxor_spec.
 now rewrite N.lxor_spec, negb_xorb_r.
 now rewrite N.lxor_spec, negb_xorb_l.
 now rewrite N.lxor_spec, xorb_negb_negb.
Qed.

(** An additionnal proof concerning [Pos.shiftl_nat], used in BigN *)

Lemma pos_shiftl_nat_pow n p :
  Zpos (Pos.shiftl_nat p n) = Zpos p * 2 ^ Z.of_nat n.
Proof.
 intros.
 rewrite mul_comm.
 induction n. simpl; auto.
 transitivity (2 * (2 ^ Z.of_nat n * Zpos p)).
 rewrite <- IHn. auto.
 rewrite mul_assoc.
 replace (of_nat (S n)) with (succ (of_nat n)).
 rewrite <- pow_succ_r. trivial.
 now destruct n.
 destruct n. trivial. simpl. now rewrite Pos.add_1_r.
Qed.

(** ** Induction principles based on successor / predecessor *)

Lemma peano_ind (P : Z -> Prop) :
  P 0 ->
  (forall x, P x -> P (succ x)) ->
  (forall x, P x -> P (pred x)) ->
  forall z, P z.
Proof.
 intros H0 Hs Hp z; destruct z.
 assumption.
 induction p using Pos.peano_ind.
  now apply (Hs 0).
  rewrite <- Pos.add_1_r.
  now apply (Hs (Zpos p)).
 induction p using Pos.peano_ind.
  now apply (Hp 0).
  rewrite <- Pos.add_1_r.
  now apply (Hp (Zneg p)).
Qed.

Lemma bi_induction (P : Z -> Prop) :
  Proper (eq ==> iff) P ->
  P 0 ->
  (forall x, P x <-> P (succ x)) ->
  forall z, P z.
Proof.
 intros _ H0 Hs. induction z using peano_ind.
 assumption.
 now apply -> Hs.
 apply Hs. now rewrite succ_pred.
Qed.


(** * Proofs of morphisms, obvious since eq is Leibniz *)

Local Obligation Tactic := simpl_relation.
Program Definition succ_wd : Proper (eq==>eq) succ := _.
Program Definition pred_wd : Proper (eq==>eq) pred := _.
Program Definition opp_wd : Proper (eq==>eq) opp := _.
Program Definition add_wd : Proper (eq==>eq==>eq) add := _.
Program Definition sub_wd : Proper (eq==>eq==>eq) sub := _.
Program Definition mul_wd : Proper (eq==>eq==>eq) mul := _.
Program Definition lt_wd : Proper (eq==>eq==>iff) lt := _.
Program Definition div_wd : Proper (eq==>eq==>eq) div := _.
Program Definition mod_wd : Proper (eq==>eq==>eq) modulo := _.
Program Definition quot_wd : Proper (eq==>eq==>eq) quot := _.
Program Definition rem_wd : Proper (eq==>eq==>eq) rem := _.
Program Definition pow_wd : Proper (eq==>eq==>eq) pow := _.
Program Definition testbit_wd : Proper (eq==>eq==>Logic.eq) testbit := _.

Set Inline Level 30. (* For inlining only t eq zero one two *)

Include ZProp
 <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

(** Otherwise Z stays associated with abstract_scope : (TODO FIX) *)
Bind Scope Z_scope with Z.

(** In generic statements, the predicates [lt] and [le] have been
  favored, whereas [gt] and [ge] don't even exist in the abstract
  layers. The use of [gt] and [ge] is hence not recommended. We provide
  here the bare minimal results to related them with [lt] and [le]. *)

Lemma gt_lt n m : n > m -> m < n.
Proof.
  unfold lt, gt. intros H. now rewrite <- compare_antisym, H.
Qed.

Lemma lt_gt n m : n < m -> m > n.
Proof.
  unfold lt, gt. intros H. now rewrite <- compare_antisym, H.
Qed.

Lemma gt_lt_iff n m : n > m <-> m < n.
Proof.
  split. apply gt_lt. apply lt_gt.
Qed.

Lemma ge_le n m : n >= m -> m <= n.
Proof.
  unfold le, ge. intros H. contradict H. now apply gt_lt.
Qed.

Lemma le_ge n m : n <= m -> m >= n.
Proof.
  unfold le, ge. intros H. contradict H. now apply lt_gt.
Qed.

Lemma ge_le_iff n m : n >= m <-> m <= n.
Proof.
  split. apply ge_le. apply le_ge.
Qed.

(** TODO : to add in Numbers *)

Lemma add_shuffle3 n m p : n + (m + p) = m + (n + p).
Proof.
 now rewrite add_comm, <- add_assoc, (add_comm p).
Qed.

Lemma mul_shuffle3 n m p : n * (m * p) = m * (n * p).
Proof.
 now rewrite mul_assoc, (mul_comm n), mul_assoc.
Qed.

Lemma add_reg_l n m p : n + m = n + p -> m = p.
Proof.
 exact (proj1 (add_cancel_l m p n)).
Qed.

Lemma mul_reg_l n m p : p <> 0 -> p * n = p * m -> n = m.
Proof.
 exact (fun Hp => proj1 (mul_cancel_l n m p Hp)).
Qed.

Lemma mul_reg_r n m p : p <> 0 -> n * p = m * p -> n = m.
Proof.
 exact (fun Hp => proj1 (mul_cancel_r n m p Hp)).
Qed.

Lemma add_succ_comm n m : succ n + m = n + succ m.
Proof.
 now rewrite add_succ_r, add_succ_l.
Qed.

Lemma mul_opp_comm n m : - n * m = n * - m.
Proof.
 now destruct n, m.
Qed.

Notation mul_eq_0 := eq_mul_0.

Lemma mul_eq_0_l n m : n <> 0 -> m * n = 0 -> m = 0.
Proof.
 intros Hn H. apply eq_mul_0 in H. now destruct H.
Qed.

Notation mul_eq_1 := eq_mul_1.

Lemma opp_eq_mul_m1 n : - n = n * -1.
Proof.
 rewrite mul_comm. now destruct n.
Qed.

Lemma add_diag n : n + n = 2 * n.
Proof.
 change 2 with (1+1). now rewrite mul_add_distr_r, !mul_1_l.
Qed.

(** * Comparison and opposite *)

Lemma compare_opp n m : (- n ?= - m) = (m ?= n).
Proof.
 destruct n, m; simpl; trivial; intros; now rewrite <- Pos.compare_antisym.
Qed.

(** * Comparison and addition *)

Lemma add_compare_mono_l n m p : (n + m ?= n + p) = (m ?= p).
Proof.
 rewrite (compare_sub m p), compare_sub. f_equal.
 unfold sub. rewrite opp_add_distr, (add_comm n m), add_assoc.
 f_equal. now rewrite <- add_assoc, add_opp_diag_r, add_0_r.
Qed.

End Z.

(** Export Notations *)

Infix "+" := Z.add : Z_scope.
Notation "- x" := (Z.opp x) : Z_scope.
Infix "-" := Z.sub : Z_scope.
Infix "*" := Z.mul : Z_scope.
Infix "^" := Z.pow : Z_scope.
Infix "/" := Z.div : Z_scope.
Infix "mod" := Z.modulo (at level 40, no associativity) : Z_scope.
Infix "÷" := Z.quot (at level 40, left associativity) : Z_scope.

(* TODO : transition from Zdivide *)
Notation "( x | y )" := (Z.divide x y) (at level 0).

Infix "?=" := Z.compare (at level 70, no associativity) : Z_scope.

Infix "<=" := Z.le : Z_scope.
Infix "<" := Z.lt : Z_scope.
Infix ">=" := Z.ge : Z_scope.
Infix ">" := Z.gt : Z_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

Infix "=?" := Z.eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := Z.leb (at level 70, no associativity) : Z_scope.
Infix "<?" := Z.ltb (at level 70, no associativity) : Z_scope.
Infix ">=?" := Z.geb (at level 70, no associativity) : Z_scope.
Infix ">?" := Z.gtb (at level 70, no associativity) : Z_scope.

(** Compatibility Notations *)

Notation Zdouble_plus_one := Z.succ_double (only parsing).
Notation Zdouble_minus_one := Z.pred_double (only parsing).
Notation Zdouble := Z.double (only parsing).
Notation ZPminus := Z.pos_sub (only parsing).
Notation Zsucc' := Z.succ (only parsing).
Notation Zpred' := Z.pred (only parsing).
Notation Zplus' := Z.add (only parsing).
Notation Zplus := Z.add (only parsing). (* Slightly incompatible *)
Notation Zopp := Z.opp (only parsing).
Notation Zsucc := Z.succ (only parsing).
Notation Zpred := Z.pred (only parsing).
Notation Zminus := Z.sub (only parsing).
Notation Zmult := Z.mul (only parsing).
Notation Zcompare := Z.compare (only parsing).
Notation Zsgn := Z.sgn (only parsing).
Notation Zle := Z.le (only parsing).
Notation Zge := Z.ge (only parsing).
Notation Zlt := Z.lt (only parsing).
Notation Zgt := Z.gt (only parsing).
Notation Zmax := Z.max (only parsing).
Notation Zmin := Z.min (only parsing).
Notation Zabs := Z.abs (only parsing).
Notation Zabs_nat := Z.abs_nat (only parsing).
Notation Zabs_N := Z.abs_N (only parsing).
Notation Z_of_nat := Z.of_nat (only parsing).
Notation Z_of_N := Z.of_N (only parsing).

Notation Zind := Z.peano_ind (only parsing).
Notation Zopp_0 := Z.opp_0 (only parsing).
Notation Zopp_neg := Z.opp_Zneg (only parsing).
Notation Zopp_involutive := Z.opp_involutive (only parsing).
Notation Zopp_inj := Z.opp_inj (only parsing).
Notation Zplus_0_l := Z.add_0_l (only parsing).
Notation Zplus_0_r := Z.add_0_r (only parsing).
Notation Zplus_comm := Z.add_comm (only parsing).
Notation Zopp_plus_distr := Z.opp_add_distr (only parsing).
Notation Zopp_succ := Z.opp_succ (only parsing).
Notation Zplus_opp_r := Z.add_opp_diag_r (only parsing).
Notation Zplus_opp_l := Z.add_opp_diag_l (only parsing).
Notation Zplus_assoc := Z.add_assoc (only parsing).
Notation Zplus_permute := Z.add_shuffle3 (only parsing).
Notation Zplus_reg_l := Z.add_reg_l (only parsing).
Notation Zplus_succ_l := Z.add_succ_l (only parsing).
Notation Zplus_succ_comm := Z.add_succ_comm (only parsing).
Notation Zsucc_discr := Z.neq_succ_diag_r (only parsing).
Notation Zsucc_inj := Z.succ_inj (only parsing).
Notation Zsucc'_inj := Z.succ_inj (only parsing).
Notation Zsucc'_pred' := Z.succ_pred (only parsing).
Notation Zpred'_succ' := Z.pred_succ (only parsing).
Notation Zpred'_inj := Z.pred_inj (only parsing).
Notation Zsucc'_discr := Z.neq_succ_diag_r (only parsing).
Notation Zminus_0_r := Z.sub_0_r (only parsing).
Notation Zminus_diag := Z.sub_diag (only parsing).
Notation Zminus_plus_distr := Z.sub_add_distr (only parsing).
Notation Zminus_succ_r := Z.sub_succ_r (only parsing).
Notation Zminus_plus := Z.add_simpl_l (only parsing).
Notation Zmult_0_l := Z.mul_0_l (only parsing).
Notation Zmult_0_r := Z.mul_0_r (only parsing).
Notation Zmult_1_l := Z.mul_1_l (only parsing).
Notation Zmult_1_r := Z.mul_1_r (only parsing).
Notation Zmult_comm := Z.mul_comm (only parsing).
Notation Zmult_assoc := Z.mul_assoc (only parsing).
Notation Zmult_permute := Z.mul_shuffle3 (only parsing).
Notation Zmult_integral_l := Z.mul_eq_0_l (only parsing).
Notation Zmult_1_inversion_l := Z.mul_eq_1 (only parsing).
Notation Zdouble_mult := Z.double_spec (only parsing).
Notation Zdouble_plus_one_mult := Z.succ_double_spec (only parsing).
Notation Zopp_mult_distr_l_reverse := Z.mul_opp_l (only parsing).
Notation Zmult_opp_opp := Z.mul_opp_opp (only parsing).
Notation Zmult_opp_comm := Z.mul_opp_comm (only parsing).
Notation Zopp_eq_mult_neg_1 := Z.opp_eq_mul_m1 (only parsing).
Notation Zmult_plus_distr_r := Z.mul_add_distr_l (only parsing).
Notation Zmult_plus_distr_l := Z.mul_add_distr_r (only parsing).
Notation Zmult_minus_distr_r := Z.mul_sub_distr_r (only parsing).
Notation Zmult_reg_l := Z.mul_reg_l (only parsing).
Notation Zmult_reg_r := Z.mul_reg_r (only parsing).
Notation Zmult_succ_l := Z.mul_succ_l (only parsing).
Notation Zmult_succ_r := Z.mul_succ_r (only parsing).
Notation Zpos_xI := Z.pos_xI (only parsing).
Notation Zpos_xO := Z.pos_xO (only parsing).
Notation Zneg_xI := Z.neg_xI (only parsing).
Notation Zneg_xO := Z.neg_xO (only parsing).

Notation Z := Z (only parsing).
Notation Z_rect := Z_rect (only parsing).
Notation Z_rec := Z_rec (only parsing).
Notation Z_ind := Z_ind (only parsing).
Notation Z0 := Z0 (only parsing).
Notation Zpos := Zpos (only parsing).
Notation Zneg := Zneg (only parsing).

(** Compatibility lemmas. These could be notations,
    but scope information would be lost.
*)

Notation SYM1 lem := (fun n => eq_sym (lem n)).
Notation SYM2 lem := (fun n m => eq_sym (lem n m)).
Notation SYM3 lem := (fun n m p => eq_sym (lem n m p)).

Lemma Zplus_assoc_reverse : forall n m p, n+m+p = n+(m+p).
Proof (SYM3 Z.add_assoc).
Lemma Zplus_succ_r_reverse : forall n m, Z.succ (n+m) = n+Z.succ m.
Proof (SYM2 Z.add_succ_r).
Notation Zplus_succ_r := Zplus_succ_r_reverse (only parsing).
Lemma Zplus_0_r_reverse : forall n, n = n + 0.
Proof (SYM1 Z.add_0_r).
Lemma Zplus_eq_compat : forall n m p q, n=m -> p=q -> n+p=m+q.
Proof (f_equal2 Z.add).
Lemma Zpos_succ_morphism : forall p, Zpos (Psucc p) = Zsucc (Zpos p).
Proof (SYM1 Z.succ_Zpos).
Lemma Zsucc_pred : forall n, n = Z.succ (Z.pred n).
Proof (SYM1 Z.succ_pred).
Lemma Zpred_succ : forall n, n = Z.pred (Z.succ n).
Proof (SYM1 Z.pred_succ).
Lemma Zsucc_eq_compat : forall n m, n = m -> Z.succ n = Z.succ m.
Proof (f_equal Z.succ).
Lemma Zminus_0_l_reverse : forall n, n = n - 0.
Proof (SYM1 Z.sub_0_r).
Lemma Zminus_diag_reverse : forall n, 0 = n-n.
Proof (SYM1 Z.sub_diag).
Lemma Zminus_succ_l : forall n m, Z.succ (n - m) = Z.succ n - m.
Proof (SYM2 Z.sub_succ_l).
Lemma Zplus_minus_eq : forall n m p, n = m + p -> p = n - m.
Proof. intros. now apply Z.add_move_l. Qed.
Lemma Zplus_minus : forall n m, n + (m - n) = m.
Proof (fun n m => eq_trans (Z.add_comm n (m-n)) (Z.sub_add n m)).
Lemma Zminus_plus_simpl_l : forall n m p, p + n - (p + m) = n - m.
Proof (fun n m p => Z.add_add_simpl_l_l p n m).
Lemma Zminus_plus_simpl_l_reverse : forall n m p, n - m = p + n - (p + m).
Proof (SYM3 Zminus_plus_simpl_l).
Lemma Zminus_plus_simpl_r : forall n m p, n + p - (m + p) = n - m.
Proof (fun n m p => Z.add_add_simpl_r_r n p m).
Lemma Zpos_minus_morphism : forall a b,
 Pcompare a b Eq = Lt -> Zpos (b - a) = Zpos b - Zpos a.
Proof. intros. now rewrite Z.sub_Zpos. Qed.
Lemma Zeq_minus : forall n m, n = m -> n - m = 0.
Proof (fun n m => proj2 (Z.sub_move_0_r n m)).
Lemma Zminus_eq : forall n m, n - m = 0 -> n = m.
Proof (fun n m => proj1 (Z.sub_move_0_r n m)).
Lemma Zpos_mult_morphism : forall p q, Zpos (p * q) = Zpos p * Zpos q.
Proof (SYM2 Z.mul_Zpos).
Lemma Zmult_0_r_reverse : forall n, 0 = n * 0.
Proof (SYM1 Z.mul_0_r).
Lemma Zmult_assoc_reverse : forall n m p, n * m * p = n * (m * p).
Proof (SYM3 Z.mul_assoc).
Lemma Zmult_integral : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof (fun n m => proj1 (Z.mul_eq_0 n m)).
Lemma Zopp_mult_distr_l : forall n m, - (n * m) = - n * m.
Proof (SYM2 Z.mul_opp_l).
Lemma Zopp_mult_distr_r : forall n m, - (n * m) = n * - m.
Proof (SYM2 Z.mul_opp_r).
Lemma Zmult_minus_distr_l : forall n m p, p * (n - m) = p * n - p * m.
Proof (fun n m p => Z.mul_sub_distr_l p n m).
Lemma Zmult_succ_r_reverse : forall n m, n * m + n = n * Zsucc m.
Proof (SYM2 Z.mul_succ_r).
Lemma Zmult_succ_l_reverse : forall n m, n * m + m = Zsucc n * m.
Proof (SYM2 Z.mul_succ_l).
Lemma Zpos_eq : forall p q, p = q -> Zpos p = Zpos q.
Proof (fun p q => proj2 (Z.inj_Zpos p q)).
Lemma Zpos_eq_rev : forall p q, Zpos p = Zpos q -> p = q.
Proof (fun p q => proj1 (Z.inj_Zpos p q)).
Lemma Zpos_eq_iff : forall p q, p = q <-> Zpos p = Zpos q.
Proof (fun p q => iff_sym (Z.inj_Zpos p q)).
Lemma Zpos_plus_distr : forall p q, Zpos (p + q) = Zpos p + Zpos q.
Proof (SYM2 Z.add_Zpos).
Lemma Zneg_plus_distr : forall p q, Zneg (p + q) = Zneg p + Zneg q.
Proof (SYM2 Z.add_Zneg).

Hint Immediate Zsucc_pred: zarith.

(* Not kept :
Zplus_0_simpl_l
Zplus_0_simpl_l_reverse
Zplus_opp_expand
Zsucc_inj_contrapositive
Zsucc_succ'
Zpred_pred'
*)

(* No compat notation for :
weak_assoc (now Z.add_assoc_pos)
weak_Zmult_plus_distr_r (now Z.mul_add_distr_pos)
*)

(** Obsolete stuff *)

Definition Zne (x y:Z) := x <> y. (* TODO : to remove someday ? *)

Ltac elim_compare com1 com2 :=
  case (Dcompare (com1 ?= com2)%Z);
    [ idtac | let x := fresh "H" in
      (intro x; case x; clear x) ].

Lemma ZL0 : 2%nat = (1 + 1)%nat.
Proof.
  reflexivity.
Qed.

Lemma Zplus_diag_eq_mult_2 n : n + n = n * 2.
Proof.
 rewrite Z.mul_comm. apply Z.add_diag.
Qed.

Lemma Z_eq_mult n m : m = 0 -> m * n = 0.
Proof.
 intros; now subst.
Qed.
