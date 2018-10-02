(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export BinNums BinPos Pnat.
Require Import BinNat Bool Equalities GenericMinMax
 OrdersFacts ZAxioms ZProperties.
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

(** When including property functors, only inline t eq zero one two *)

Set Inline Level 30.

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

Definition divide x y := exists z, y = z*x.
Notation "( x | y )" := (divide x y) (at level 0).

Definition Even a := exists b, a = 2*b.
Definition Odd a := exists b, a = 2*b+1.

(** * Decidability of equality. *)

Definition eq_dec (x y : Z) : {x = y} + {x <> y}.
Proof.
 decide equality; apply Pos.eq_dec.
Defined.

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

(** * Properties of [pos_sub] *)

(** [pos_sub] can be written in term of positive comparison
    and subtraction (cf. earlier definition of addition of Z) *)

Lemma pos_sub_spec p q :
 pos_sub p q =
 match (p ?= q)%positive with
   | Eq => 0
   | Lt => neg (q - p)
   | Gt => pos (p - q)
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

Lemma pos_sub_discr p q :
  match pos_sub p q with
  | Z0 => p = q
  | pos k => p = q + k
  | neg k => q = p + k
  end%positive.
Proof.
 rewrite pos_sub_spec.
 case Pos.compare_spec; auto; intros;
  now rewrite Pos.add_comm, Pos.sub_add.
Qed.

(** Particular cases of the previous result *)

Lemma pos_sub_diag p : pos_sub p p = 0.
Proof.
 now rewrite pos_sub_spec, Pos.compare_refl.
Qed.

Lemma pos_sub_lt p q : (p < q)%positive -> pos_sub p q = neg (q - p).
Proof.
 intros H. now rewrite pos_sub_spec, H.
Qed.

Lemma pos_sub_gt p q : (q < p)%positive -> pos_sub p q = pos (p - q).
Proof.
 intros H. now rewrite pos_sub_spec, Pos.compare_antisym, H.
Qed.

(** The opposite of [pos_sub] is [pos_sub] with reversed arguments *)

Lemma pos_sub_opp p q : - pos_sub p q = pos_sub q p.
Proof.
 revert q; induction p; destruct q; simpl; trivial;
 rewrite <- IHp; now destruct pos_sub.
Qed.

(** In the following module, we group results that are needed now
  to prove specifications of operations, but will also be provided
  later by the generic functor of properties. *)

Module Import Private_BootStrap.

(** ** Operations and constants *)

Lemma add_0_r n : n + 0 = n.
Proof.
 now destruct n.
Qed.

Lemma mul_0_r n : n * 0 = 0.
Proof.
 now destruct n.
Qed.

Lemma mul_1_l n : 1 * n = n.
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
  pos_sub (p + q) r = pos p + pos_sub q r.
Proof.
 simpl. rewrite !pos_sub_spec.
 case (Pos.compare_spec q r); intros E0.
 - (* q = r *)
   subst.
   assert (H := Pos.lt_add_r r p).
   rewrite Pos.add_comm in H. apply Pos.lt_gt in H.
   now rewrite H, Pos.add_sub.
 - (* q < r *)
   rewrite pos_sub_spec.
   assert (Hr : (r = (r-q)+q)%positive) by (now rewrite Pos.sub_add).
   rewrite Hr at 1. rewrite Pos.add_compare_mono_r.
   case Pos.compare_spec; intros E1; trivial; f_equal.
   rewrite Pos.add_comm. apply Pos.sub_add_distr.
   rewrite Hr, Pos.add_comm. now apply Pos.add_lt_mono_r.
   symmetry. apply Pos.sub_sub_distr; trivial.
 - (* r < q *)
   assert (LT : (r < p + q)%positive).
   { apply Pos.lt_trans with q; trivial.
     rewrite Pos.add_comm. apply Pos.lt_add_r. }
   apply Pos.lt_gt in LT. rewrite LT. f_equal.
   symmetry. now apply Pos.add_sub_assoc.
Qed.

Local Arguments add !x !y.

Lemma add_assoc_pos p n m : pos p + (n + m) = pos p + n + m.
Proof.
 destruct n as [|n|n], m as [|m|m]; simpl; trivial.
 - now rewrite Pos.add_assoc.
 - symmetry. apply pos_sub_add.
 - symmetry. apply add_0_r.
 - now rewrite <- pos_sub_add, add_comm, <- pos_sub_add, Pos.add_comm.
 - apply opp_inj. rewrite !opp_add_distr, !pos_sub_opp.
   rewrite add_comm, Pos.add_comm. apply pos_sub_add.
Qed.

Lemma add_assoc n m p : n + (m + p) = n + m + p.
Proof.
 destruct n.
 - trivial.
 - apply add_assoc_pos.
 - apply opp_inj. rewrite !opp_add_distr. simpl. apply add_assoc_pos.
Qed.

(** ** Opposite is inverse for addition *)

Lemma add_opp_diag_r n : n + - n = 0.
Proof.
 destruct n; simpl; trivial; now rewrite pos_sub_diag.
Qed.

(** ** Multiplication and Opposite *)

Lemma mul_opp_r n m : n * - m = - (n * m).
Proof.
 now destruct n, m.
Qed.

(** ** Distributivity of multiplication over addition *)

Lemma mul_add_distr_pos (p:positive) n m :
 (n + m) * pos p = n * pos p + m * pos p.
Proof.
 destruct n as [|n|n], m as [|m|m]; simpl; trivial.
 - now rewrite Pos.mul_add_distr_r.
 - rewrite ?pos_sub_spec, ?Pos.mul_compare_mono_r; case Pos.compare_spec;
   simpl; trivial; intros; now rewrite Pos.mul_sub_distr_r.
 - rewrite ?pos_sub_spec, ?Pos.mul_compare_mono_r; case Pos.compare_spec;
   simpl; trivial; intros; now rewrite Pos.mul_sub_distr_r.
 - now rewrite Pos.mul_add_distr_r.
Qed.

Lemma mul_add_distr_r n m p : (n + m) * p = n * p + m * p.
Proof.
 destruct p as [|p|p].
 - now rewrite !mul_0_r.
 - apply mul_add_distr_pos.
 - apply opp_inj. rewrite opp_add_distr, <- !mul_opp_r.
   apply mul_add_distr_pos.
Qed.

End Private_BootStrap.

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

Local Arguments pos_sub : simpl nomatch.

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

(** ** Specification of comparisons and order *)

Lemma eqb_eq n m : (n =? m) = true <-> n = m.
Proof.
 destruct n, m; simpl; try (now split); rewrite Pos.eqb_eq;
 split; (now injection 1) || (intros; now f_equal).
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
 unfold ltb, lt. destruct compare; easy'.
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
 unfold leb, le. destruct compare; easy'.
Qed.

Lemma compare_eq_iff n m : (n ?= m) = Eq <-> n = m.
Proof.
destruct n, m; simpl; rewrite ?CompOpp_iff, ?Pos.compare_eq_iff;
 split; congruence.
Qed.

Lemma compare_sub n m : (n ?= m) = (n - m ?= 0).
Proof.
 destruct n as [|n|n], m as [|m|m]; simpl; trivial;
 rewrite <- ? Pos.compare_antisym, ?pos_sub_spec;
 case Pos.compare_spec; trivial.
Qed.

Lemma compare_antisym n m : (m ?= n) = CompOpp (n ?= m).
Proof.
destruct n, m; simpl; trivial; now rewrite <- ?Pos.compare_antisym.
Qed.

Lemma compare_lt_iff n m : (n ?= m) = Lt <-> n < m.
Proof. reflexivity. Qed.

Lemma compare_le_iff n m : (n ?= m) <> Gt <-> n <= m.
Proof. reflexivity. Qed.

(** Some more advanced properties of comparison and orders,
    including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

(** Remaining specification of [lt] and [le] *)

Lemma lt_succ_r n m : n < succ m <-> n<=m.
Proof.
 unfold lt, le. rewrite compare_sub, sub_succ_r.
 rewrite (compare_sub n m).
 destruct (n-m) as [|[ | | ]|]; easy'.
Qed.

(** ** Specification of minimum and maximum *)

Lemma max_l n m : m<=n -> max n m = n.
Proof.
 unfold le, max. rewrite (compare_antisym n m).
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
 rewrite (compare_antisym n m). case compare_spec; intuition.
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
  now apply (Hs (pos p)).
 induction p using Pos.peano_ind.
  now apply (Hp 0).
  rewrite <- Pos.add_1_r.
  now apply (Hp (neg p)).
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

(** We can now derive all properties of basic functions and orders,
    and use these properties for proving the specs of more advanced
    functions. *)

Include ZBasicProp <+ UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.


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

(** For folding back a [pow_pos] into a [pow] *)

Lemma pow_pos_fold n p : pow_pos n p = n ^ (pos p).
Proof.
 reflexivity.
Qed.

(** ** Specification of square *)

Lemma square_spec n : square n = n * n.
Proof.
 destruct n; trivial; simpl; f_equal; apply Pos.square_spec.
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
 intros _. simpl succ. rewrite Pos.add_1_r. apply (Pos.sqrt_spec p).
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
 assert (Pow : forall p q, pos (p^q) = (pos p)^(pos q)).
 { intros. now apply Pos.iter_swap_gen. }
 destruct n as [|[p|p|]|]; intros Hn; split; try easy; unfold log2;
  simpl succ; rewrite ?Pos.add_1_r, <- Pow.
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
  let (q, r) := pos_div_eucl a b in pos a = q * b + r.
Proof.
 intros Hb.
 induction a; unfold pos_div_eucl; fold pos_div_eucl.
 - (* ~1 *)
   destruct pos_div_eucl as (q,r).
   change (pos a~1) with (2*(pos a)+1).
   rewrite IHa, mul_add_distr_l, mul_assoc.
   destruct ltb.
   now rewrite add_assoc.
   rewrite mul_add_distr_r, mul_1_l, <- !add_assoc. f_equal.
   unfold sub. now rewrite (add_comm _ (-b)), add_assoc, add_opp_diag_r.
 - (* ~0 *)
   destruct pos_div_eucl as (q,r).
   change (pos a~0) with (2*pos a).
   rewrite IHa, mul_add_distr_l, mul_assoc.
   destruct ltb.
   trivial.
   rewrite mul_add_distr_r, mul_1_l, <- !add_assoc. f_equal.
   unfold sub. now rewrite (add_comm _ (-b)), add_assoc, add_opp_diag_r.
 - (* 1 *)
   case leb_spec; trivial.
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
  generalize (pos_div_eucl_eq a (pos b) Logic.eq_refl);
  destruct pos_div_eucl as (q,r); rewrite mul_comm.
 - (* pos pos *)
   trivial.
 - (* pos neg *)
   intros ->.
   destruct r as [ |r|r]; rewrite <- !mul_opp_comm; trivial;
    rewrite mul_add_distr_l, mul_1_r, <- add_assoc; f_equal;
   now rewrite add_assoc, add_opp_diag_r.
 - (* neg pos *)
   change (neg a) with (- pos a). intros ->.
   rewrite (opp_add_distr _ r), <- mul_opp_r.
   destruct r as [ |r|r]; trivial;
    rewrite opp_add_distr, mul_add_distr_l, <- add_assoc; f_equal;
    unfold sub; now rewrite add_assoc, mul_opp_r, mul_1_r, add_opp_diag_l.
 - (* neg neg *)
   change (neg a) with (- pos a). intros ->.
   now rewrite opp_add_distr, <- mul_opp_l.
Qed.

Lemma div_mod a b : b<>0 -> a = b*(a/b) + (a mod b).
Proof.
 intros Hb. generalize (div_eucl_eq a b Hb).
 unfold div, modulo. now destruct div_eucl.
Qed.

Lemma pos_div_eucl_bound a b : 0<b -> 0 <= snd (pos_div_eucl a b) < b.
Proof.
 assert (AUX : forall m p, m < pos (p~0) -> m - pos p < pos p).
  intros m p. unfold lt.
  rewrite (compare_sub m), (compare_sub _ (pos _)). unfold sub.
  rewrite <- add_assoc. simpl opp; simpl (neg _ + _).
  now rewrite Pos.add_diag.
 intros Hb.
 destruct b as [|b|b]; discriminate Hb || clear Hb.
 induction a; unfold pos_div_eucl; fold pos_div_eucl.
 (* ~1 *)
 destruct pos_div_eucl as (q,r).
 simpl in IHa; destruct IHa as (Hr,Hr').
 case ltb_spec; intros H; unfold snd. split; trivial. now destruct r.
 split. unfold le.
  now rewrite compare_antisym, <- compare_sub, <- compare_antisym.
 apply AUX. rewrite <- succ_double_spec.
 destruct r; try easy. unfold lt in *; simpl in *.
  now rewrite Pos.compare_xI_xO, Hr'.
 (* ~0 *)
 destruct pos_div_eucl as (q,r).
 simpl in IHa; destruct IHa as (Hr,Hr').
 case ltb_spec; intros H; unfold snd. split; trivial. now destruct r.
 split. unfold le.
  now rewrite compare_antisym, <- compare_sub, <- compare_antisym.
 apply AUX. destruct r; try easy.
 (* 1 *)
 case leb_spec; intros H; simpl; split; try easy.
 red; simpl. now apply Pos.le_succ_l.
Qed.

Lemma mod_pos_bound a b : 0 < b -> 0 <= a mod b < b.
Proof.
 destruct b as [|b|b]; try easy; intros _.
 destruct a as [|a|a]; unfold modulo, div_eucl.
 now split.
 now apply pos_div_eucl_bound.
 generalize (pos_div_eucl_bound a (pos b) Logic.eq_refl).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split. unfold le.
  now rewrite compare_antisym, <- compare_sub, <- compare_antisym, Hr'.
 unfold lt in *; simpl in *. rewrite pos_sub_gt by trivial.
 simpl. now apply Pos.sub_decr.
Qed.

Definition mod_bound_pos a b (_:0<=a) := mod_pos_bound a b.

Lemma mod_neg_bound a b : b < 0 -> b < a mod b <= 0.
Proof.
 destruct b as [|b|b]; try easy; intros _.
 destruct a as [|a|a]; unfold modulo, div_eucl.
 now split.
 generalize (pos_div_eucl_bound a (pos b) Logic.eq_refl).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 destruct r as [|r|r]; (now destruct Hr) || clear Hr.
 now split.
 split.
 unfold lt in *; simpl in *. rewrite pos_sub_lt by trivial.
 rewrite <- Pos.compare_antisym. now apply Pos.sub_decr.
 change (neg b - neg r <= 0). unfold le, lt in *.
  rewrite <- compare_sub. simpl in *.
  now rewrite <- Pos.compare_antisym, Hr'.
 generalize (pos_div_eucl_bound a (pos b) Logic.eq_refl).
 destruct pos_div_eucl as (q,r); unfold snd; intros (Hr,Hr').
 split; destruct r; try easy.
  red; simpl; now rewrite <- Pos.compare_antisym.
Qed.

(** ** Correctness proofs for Floor division *)

Theorem quotrem_eq a b : let (q,r) := quotrem a b in a = q * b + r.
Proof.
 destruct a as [|a|a], b as [|b|b]; simpl; trivial;
 generalize (N.pos_div_eucl_spec a (N.pos b)); case N.pos_div_eucl; trivial;
  intros q r;
  try change (neg a) with (-pos a);
  change (pos a) with (of_N (N.pos a)); intros ->; now destruct q, r.
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
 assert (H := N.pos_div_eucl_remainder a (N.pos b)).
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

(** ** Extra properties about [divide] *)

Lemma divide_Zpos p q : (pos p|pos q) <-> (p|q)%positive.
Proof.
 split.
 intros ([ |r|r],H); simpl in *; destr_eq H. exists r; auto.
 intros (r,H). exists (pos r); simpl; now f_equal.
Qed.

Lemma divide_Zpos_Zneg_r n p : (n|pos p) <-> (n|neg p).
Proof.
 split; intros (m,H); exists (-m); now rewrite mul_opp_l, <- H.
Qed.

Lemma divide_Zpos_Zneg_l n p : (pos p|n) <-> (neg p|n).
Proof.
 split; intros (m,H); exists (-m); now rewrite mul_opp_l, <- mul_opp_r.
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
 destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa.
  now rewrite mul_comm.
Qed.

Lemma gcd_divide_r a b : (gcd a b | b).
Proof.
 rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb.
  now rewrite mul_comm.
Qed.

Lemma gcd_greatest a b c : (c|a) -> (c|b) -> (c | gcd a b).
Proof.
 assert (H : forall p q r, (r|pos p) -> (r|pos q) -> (r|pos (Pos.gcd p q))).
 { intros p q [|r|r] H H'.
   destruct H; now rewrite mul_comm in *.
   apply divide_Zpos, Pos.gcd_greatest; now apply divide_Zpos.
   apply divide_Zpos_Zneg_l, divide_Zpos, Pos.gcd_greatest;
    now apply divide_Zpos, divide_Zpos_Zneg_l.
 }
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

(** ** Extra properties about [testbit] *)

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
 testbit (pos a) n = N.testbit (N.pos a) (to_N n).
Proof.
 intro Hn. now rewrite <- testbit_of_N'.
Qed.

Lemma testbit_Zneg a n : 0<=n ->
 testbit (neg a) n = negb (N.testbit (Pos.pred_N a) (to_N n)).
Proof.
 intro Hn.
 rewrite <- testbit_of_N' by trivial.
 destruct n as [ |n|n];
  [ | simpl; now destruct (Pos.pred_N a) | now destruct Hn].
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
 unfold testbit; simpl.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.add_1_r, ?Pos.pred_N_succ; now destruct n.
Qed.

Lemma testbit_even_succ a n : 0<=n ->
 testbit (2*a) (succ n) = testbit a n.
Proof.
 destruct n as [|n|n]; (now destruct 1) || intros _.
 destruct a as [|[a|a|]|[a|a|]]; simpl; trivial. now destruct a.
 unfold testbit; simpl.
 destruct a as [|a|[a|a|]]; simpl; trivial;
  rewrite ?Pos.add_1_r, ?Pos.pred_N_succ; now destruct n.
Qed.

(** Correctness proofs about [Z.shiftr] and [Z.shiftl] *)

Lemma shiftr_spec_aux a n m : 0<=n -> 0<=m ->
 testbit (shiftr a n) m = testbit a (m+n).
Proof.
 intros Hn Hm. unfold shiftr.
 destruct n as [ |n|n]; (now destruct Hn) || clear Hn; simpl.
 now rewrite add_0_r.
 assert (forall p, to_N (m + pos p) = (to_N m + N.pos p)%N).
  destruct m; trivial; now destruct Hm.
 assert (forall p, 0 <= m + pos p).
  destruct m; easy || now destruct Hm.
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (Pos.iter div2 0 n) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 now rewrite 2 testbit_0_l.
 (* a > 0 *)
 change (pos a) with (of_N (N.pos a)) at 1.
 rewrite <- (Pos.iter_swap_gen _ _ _ N.div2) by now intros [|[ | | ]].
 rewrite testbit_Zpos, testbit_of_N', H; trivial.
 exact (N.shiftr_spec' (N.pos a) (N.pos n) (to_N m)).
 (* a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ Pos.div2_up) by trivial.
 rewrite 2 testbit_Zneg, H; trivial. f_equal.
 rewrite (Pos.iter_swap_gen _ _ _ _ N.div2) by exact N.pred_div2_up.
 exact (N.shiftr_spec' (Pos.pred_N a) (N.pos n) (to_N m)).
Qed.

Lemma shiftl_spec_low a n m : m<n ->
 testbit (shiftl a n) m = false.
Proof.
 intros H. destruct n as [|n|n], m as [|m|m]; try easy; simpl shiftl.
 destruct (Pos.succ_pred_or n) as [-> | <-];
  rewrite ?Pos.iter_succ; apply testbit_even_0.
 destruct a as [ |a|a].
 (* a = 0 *)
 replace (Pos.iter (mul 2) 0 n) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 apply testbit_0_l.
 (* a > 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite testbit_Zpos by easy.
 exact (N.shiftl_spec_low (N.pos a) (N.pos n) (N.pos m) H).
 (* a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite testbit_Zneg by easy.
 now rewrite (N.pos_pred_shiftl_low a (N.pos n)).
Qed.

Lemma shiftl_spec_high a n m : 0<=m -> n<=m ->
 testbit (shiftl a n) m = testbit a (m-n).
Proof.
 intros Hm H.
 destruct n as [ |n|n]. simpl. now rewrite sub_0_r.
 (* n > 0 *)
 destruct m as [ |m|m]; try (now destruct H).
 assert (0 <= pos m - pos n).
  red. now rewrite compare_antisym, <- compare_sub, <- compare_antisym.
 assert (EQ : to_N (pos m - pos n) = (N.pos m - N.pos n)%N).
  red in H. simpl in H. simpl to_N.
  rewrite pos_sub_spec, Pos.compare_antisym.
  destruct (Pos.compare_spec n m) as [H'|H'|H']; try (now destruct H).
  subst. now rewrite N.sub_diag.
  simpl. destruct (Pos.sub_mask_pos' m n H') as (p & -> & <-).
  f_equal. now rewrite Pos.add_comm, Pos.add_sub.
 destruct a; unfold shiftl.
 (* ... a = 0 *)
 replace (Pos.iter (mul 2) 0 n) with 0
  by (apply Pos.iter_invariant; intros; subst; trivial).
 now rewrite 2 testbit_0_l.
 (* ... a > 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite 2 testbit_Zpos, EQ by easy.
 exact (N.shiftl_spec_high' (N.pos p) (N.pos n) (N.pos m) H).
 (* ... a < 0 *)
 rewrite <- (Pos.iter_swap_gen _ _ _ xO) by trivial.
 rewrite 2 testbit_Zneg, EQ by easy. f_equal.
 simpl to_N.
 rewrite <- N.shiftl_spec_high by easy.
 now apply (N.pos_pred_shiftl_high p (N.pos n)).
 (* n < 0 *)
 unfold sub. simpl.
 now apply (shiftr_spec_aux a (pos n) m).
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


(** Generic properties of advanced functions. *)

Include ZExtraProp.

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

(** We provide a tactic converting from one style to the other. *)

Ltac swap_greater := rewrite ?gt_lt_iff in *; rewrite ?ge_le_iff in *.

(** Similarly, the boolean comparisons [ltb] and [leb] are favored
  over their dual [gtb] and [geb]. We prove here the equivalence
  and a few minimal results. *)

Lemma gtb_ltb n m : (n >? m) = (m <? n).
Proof.
 unfold gtb, ltb. rewrite compare_antisym. now case compare.
Qed.

Lemma geb_leb n m : (n >=? m) = (m <=? n).
Proof.
 unfold geb, leb. rewrite compare_antisym. now case compare.
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

(** TODO : to add in Numbers ? *)

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

Bind Scope Z_scope with Z.t Z.

(** Re-export Notations *)

Numeral Notation Z Z.of_int Z.to_int : Z_scope.

Infix "+" := Z.add : Z_scope.
Notation "- x" := (Z.opp x) : Z_scope.
Infix "-" := Z.sub : Z_scope.
Infix "*" := Z.mul : Z_scope.
Infix "^" := Z.pow : Z_scope.
Infix "/" := Z.div : Z_scope.
Infix "mod" := Z.modulo (at level 40, no associativity) : Z_scope.
Infix "÷" := Z.quot (at level 40, left associativity) : Z_scope.
Infix "?=" := Z.compare (at level 70, no associativity) : Z_scope.
Infix "=?" := Z.eqb (at level 70, no associativity) : Z_scope.
Infix "<=?" := Z.leb (at level 70, no associativity) : Z_scope.
Infix "<?" := Z.ltb (at level 70, no associativity) : Z_scope.
Infix ">=?" := Z.geb (at level 70, no associativity) : Z_scope.
Infix ">?" := Z.gtb (at level 70, no associativity) : Z_scope.
Notation "( x | y )" := (Z.divide x y) (at level 0) : Z_scope.
Infix "<=" := Z.le : Z_scope.
Infix "<" := Z.lt : Z_scope.
Infix ">=" := Z.ge : Z_scope.
Infix ">" := Z.gt : Z_scope.
Notation "x <= y <= z" := (x <= y /\ y <= z) : Z_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Z_scope.
Notation "x < y < z" := (x < y /\ y < z) : Z_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Z_scope.

(** Conversions from / to positive numbers *)

Module Pos2Z.

Lemma id p : Z.to_pos (Z.pos p) = p.
Proof. reflexivity. Qed.

Lemma inj p q : Z.pos p = Z.pos q -> p = q.
Proof. now injection 1. Qed.

Lemma inj_iff p q : Z.pos p = Z.pos q <-> p = q.
Proof. split. apply inj. intros; now f_equal. Qed.

Lemma is_pos p : 0 < Z.pos p.
Proof. reflexivity. Qed.

Lemma is_nonneg p : 0 <= Z.pos p.
Proof. easy. Qed.

Lemma inj_1 : Z.pos 1 = 1.
Proof. reflexivity. Qed.

Lemma inj_xO p : Z.pos p~0 = 2 * Z.pos p.
Proof. reflexivity. Qed.

Lemma inj_xI p : Z.pos p~1 = 2 * Z.pos p + 1.
Proof. reflexivity. Qed.

Lemma inj_succ p : Z.pos (Pos.succ p) = Z.succ (Z.pos p).
Proof. simpl. now rewrite Pos.add_1_r. Qed.

Lemma inj_add p q : Z.pos (p+q) = Z.pos p + Z.pos q.
Proof. reflexivity. Qed.

Lemma inj_sub p q : (p < q)%positive ->
 Z.pos (q-p) = Z.pos q - Z.pos p.
Proof. intros. simpl. now rewrite Z.pos_sub_gt. Qed.

Lemma inj_sub_max p q : Z.pos (p - q) = Z.max 1 (Z.pos p - Z.pos q).
Proof.
  simpl. rewrite Z.pos_sub_spec. case Pos.compare_spec; intros.
  - subst; now rewrite Pos.sub_diag.
  - now rewrite Pos.sub_lt.
  - now destruct (p-q)%positive.
Qed.

Lemma inj_pred p : p <> 1%positive ->
 Z.pos (Pos.pred p) = Z.pred (Z.pos p).
Proof. destruct p; easy || now destruct 1. Qed.

Lemma inj_mul p q : Z.pos (p*q) = Z.pos p * Z.pos q.
Proof. reflexivity. Qed.

Lemma inj_pow_pos p q : Z.pos (p^q) = Z.pow_pos (Z.pos p) q.
Proof. now apply Pos.iter_swap_gen. Qed.

Lemma inj_pow p q : Z.pos (p^q) = (Z.pos p)^(Z.pos q).
Proof. apply inj_pow_pos. Qed.

Lemma inj_square p : Z.pos (Pos.square p) = Z.square (Z.pos p).
Proof. reflexivity. Qed.

Lemma inj_compare p q : (p ?= q)%positive = (Z.pos p ?= Z.pos q).
Proof. reflexivity. Qed.

Lemma inj_leb p q : (p <=? q)%positive = (Z.pos p <=? Z.pos q).
Proof. reflexivity. Qed.

Lemma inj_ltb p q : (p <? q)%positive = (Z.pos p <? Z.pos q).
Proof. reflexivity. Qed.

Lemma inj_eqb p q : (p =? q)%positive = (Z.pos p =? Z.pos q).
Proof. reflexivity. Qed.

Lemma inj_max p q : Z.pos (Pos.max p q) = Z.max (Z.pos p) (Z.pos q).
Proof.
 unfold Z.max, Pos.max. rewrite inj_compare. now case Z.compare_spec.
Qed.

Lemma inj_min p q : Z.pos (Pos.min p q) = Z.min (Z.pos p) (Z.pos q).
Proof.
 unfold Z.min, Pos.min. rewrite inj_compare. now case Z.compare_spec.
Qed.

Lemma inj_sqrt p : Z.pos (Pos.sqrt p) = Z.sqrt (Z.pos p).
Proof. reflexivity. Qed.

Lemma inj_gcd p q : Z.pos (Pos.gcd p q) = Z.gcd (Z.pos p) (Z.pos q).
Proof. reflexivity. Qed.

Definition inj_divide p q : (Z.pos p|Z.pos q) <-> (p|q)%positive.
Proof. apply Z.divide_Zpos. Qed.

Lemma inj_testbit a n : 0<=n ->
 Z.testbit (Z.pos a) n = N.testbit (N.pos a) (Z.to_N n).
Proof. apply Z.testbit_Zpos. Qed.

(** Some results concerning Z.neg and Z.pos *)

Lemma inj_neg p q : Z.neg p = Z.neg q -> p = q.
Proof. now injection 1. Qed.

Lemma inj_neg_iff p q : Z.neg p = Z.neg q <-> p = q.
Proof. split. apply inj_neg. intros; now f_equal. Qed.

Lemma inj_pos p q : Z.pos p = Z.pos q -> p = q.
Proof. now injection 1. Qed.

Lemma inj_pos_iff p q : Z.pos p = Z.pos q <-> p = q.
Proof. split. apply inj_pos. intros; now f_equal. Qed.

Lemma neg_is_neg p : Z.neg p < 0.
Proof. reflexivity. Qed.

Lemma neg_is_nonpos p : Z.neg p <= 0.
Proof. easy. Qed.

Lemma pos_is_pos p : 0 < Z.pos p.
Proof. reflexivity. Qed.

Lemma pos_is_nonneg p : 0 <= Z.pos p.
Proof. easy. Qed.

Lemma neg_le_pos p q : Zneg p <= Zpos q.
Proof. easy. Qed.

Lemma neg_lt_pos p q : Zneg p < Zpos q.
Proof. easy. Qed.

Lemma neg_le_neg p q : (q <= p)%positive -> Zneg p <= Zneg q.
Proof. intros; unfold Z.le; simpl. now rewrite <- Pos.compare_antisym. Qed.

Lemma neg_lt_neg p q : (q < p)%positive -> Zneg p < Zneg q.
Proof. intros; unfold Z.lt; simpl. now rewrite <- Pos.compare_antisym. Qed.

Lemma pos_le_pos p q : (p <= q)%positive -> Zpos p <= Zpos q.
Proof. easy. Qed.

Lemma pos_lt_pos p q : (p < q)%positive -> Zpos p < Zpos q.
Proof. easy. Qed.

Lemma neg_xO p : Z.neg p~0 = 2 * Z.neg p.
Proof. reflexivity. Qed.

Lemma neg_xI p : Z.neg p~1 = 2 * Z.neg p - 1.
Proof. reflexivity. Qed.

Lemma pos_xO p : Z.pos p~0 = 2 * Z.pos p.
Proof. reflexivity. Qed.

Lemma pos_xI p : Z.pos p~1 = 2 * Z.pos p + 1.
Proof. reflexivity. Qed.

Lemma opp_neg p : - Z.neg p = Z.pos p.
Proof. reflexivity. Qed.

Lemma opp_pos p : - Z.pos p = Z.neg p.
Proof. reflexivity. Qed.

Lemma add_neg_neg p q : Z.neg p + Z.neg q = Z.neg (p+q).
Proof. reflexivity. Qed.

Lemma add_pos_neg p q : Z.pos p + Z.neg q = Z.pos_sub p q.
Proof. reflexivity. Qed.

Lemma add_neg_pos p q : Z.neg p + Z.pos q = Z.pos_sub q p.
Proof. reflexivity. Qed.

Lemma add_pos_pos p q : Z.pos p + Z.pos q = Z.pos (p+q).
Proof. reflexivity. Qed.

Lemma divide_pos_neg_r n p : (n|Z.pos p) <-> (n|Z.neg p).
Proof. apply Z.divide_Zpos_Zneg_r. Qed.

Lemma divide_pos_neg_l n p : (Z.pos p|n) <-> (Z.neg p|n).
Proof. apply Z.divide_Zpos_Zneg_l. Qed.

Lemma testbit_neg a n : 0<=n ->
 Z.testbit (Z.neg a) n = negb (N.testbit (Pos.pred_N a) (Z.to_N n)).
Proof. apply Z.testbit_Zneg. Qed.

Lemma testbit_pos a n : 0<=n ->
 Z.testbit (Z.pos a) n = N.testbit (N.pos a) (Z.to_N n).
Proof. apply Z.testbit_Zpos. Qed.

End Pos2Z.

Module Z2Pos.

Lemma id x : 0 < x -> Z.pos (Z.to_pos x) = x.
Proof. now destruct x. Qed.

Lemma inj x y : 0 < x -> 0 < y -> Z.to_pos x = Z.to_pos y -> x = y.
Proof.
 destruct x; simpl; try easy. intros _ H ->. now apply id.
Qed.

Lemma inj_iff x y : 0 < x -> 0 < y -> (Z.to_pos x = Z.to_pos y <-> x = y).
Proof. split. now apply inj. intros; now f_equal. Qed.

Lemma to_pos_nonpos x : x <= 0 -> Z.to_pos x = 1%positive.
Proof. destruct x; trivial. now destruct 1. Qed.

Lemma inj_1 : Z.to_pos 1 = 1%positive.
Proof. reflexivity. Qed.

Lemma inj_double x : 0 < x ->
 Z.to_pos (Z.double x) = (Z.to_pos x)~0%positive.
Proof. now destruct x. Qed.

Lemma inj_succ_double x : 0 < x ->
 Z.to_pos (Z.succ_double x) = (Z.to_pos x)~1%positive.
Proof. now destruct x. Qed.

Lemma inj_succ x : 0 < x -> Z.to_pos (Z.succ x) = Pos.succ (Z.to_pos x).
Proof.
 destruct x; try easy. simpl. now rewrite Pos.add_1_r.
Qed.

Lemma inj_add x y : 0 < x -> 0 < y ->
 Z.to_pos (x+y) = (Z.to_pos x + Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_sub x y : 0 < x < y ->
 Z.to_pos (y-x) = (Z.to_pos y - Z.to_pos x)%positive.
Proof.
 destruct x; try easy. destruct y; try easy. simpl.
 intros. now rewrite Z.pos_sub_gt.
Qed.

Lemma inj_pred x : 1 < x -> Z.to_pos (Z.pred x) = Pos.pred (Z.to_pos x).
Proof. now destruct x as [|[x|x|]|]. Qed.

Lemma inj_mul x y : 0 < x -> 0 < y ->
 Z.to_pos (x*y) = (Z.to_pos x * Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_pow x y : 0 < x -> 0 < y ->
 Z.to_pos (x^y) = (Z.to_pos x ^ Z.to_pos y)%positive.
Proof.
 intros. apply Pos2Z.inj. rewrite Pos2Z.inj_pow, !id; trivial.
 apply Z.pow_pos_nonneg. trivial. now apply Z.lt_le_incl.
Qed.

Lemma inj_pow_pos x p : 0 < x ->
 Z.to_pos (Z.pow_pos x p) = ((Z.to_pos x)^p)%positive.
Proof. intros. now apply (inj_pow x (Z.pos p)). Qed.

Lemma inj_compare x y : 0 < x -> 0 < y ->
 (x ?= y) = (Z.to_pos x ?= Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_leb x y : 0 < x -> 0 < y ->
 (x <=? y) = (Z.to_pos x <=? Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_ltb x y : 0 < x -> 0 < y ->
 (x <? y) = (Z.to_pos x <? Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_eqb x y : 0 < x -> 0 < y ->
 (x =? y) = (Z.to_pos x =? Z.to_pos y)%positive.
Proof. destruct x; easy || now destruct y. Qed.

Lemma inj_max x y :
 Z.to_pos (Z.max x y) = Pos.max (Z.to_pos x) (Z.to_pos y).
Proof.
 destruct x; simpl; try rewrite Pos.max_1_l.
 - now destruct y.
 - destruct y; simpl; now rewrite ?Pos.max_1_r, <- ?Pos2Z.inj_max.
 - destruct y; simpl; rewrite ?Pos.max_1_r; trivial.
   apply to_pos_nonpos. now apply Z.max_lub.
Qed.

Lemma inj_min x y :
 Z.to_pos (Z.min x y) = Pos.min (Z.to_pos x) (Z.to_pos y).
Proof.
 destruct x; simpl; try rewrite Pos.min_1_l.
 - now destruct y.
 - destruct y; simpl; now rewrite ?Pos.min_1_r, <- ?Pos2Z.inj_min.
 - destruct y; simpl; rewrite ?Pos.min_1_r; trivial.
   apply to_pos_nonpos. apply Z.min_le_iff. now left.
Qed.

Lemma inj_sqrt x : Z.to_pos (Z.sqrt x) = Pos.sqrt (Z.to_pos x).
Proof. now destruct x. Qed.

Lemma inj_gcd x y : 0 < x -> 0 < y ->
 Z.to_pos (Z.gcd x y) = Pos.gcd (Z.to_pos x) (Z.to_pos y).
Proof. destruct x; easy || now destruct y. Qed.

End Z2Pos.

(** Compatibility Notations *)

Notation Zdouble_plus_one := Z.succ_double (only parsing).
Notation Zdouble_minus_one := Z.pred_double (only parsing).
Notation Zdouble := Z.double (compat "8.7").
Notation ZPminus := Z.pos_sub (only parsing).
Notation Zsucc' := Z.succ (compat "8.7").
Notation Zpred' := Z.pred (compat "8.7").
Notation Zplus' := Z.add (compat "8.7").
Notation Zplus := Z.add (only parsing). (* Slightly incompatible *)
Notation Zopp := Z.opp (compat "8.7").
Notation Zsucc := Z.succ (compat "8.7").
Notation Zpred := Z.pred (compat "8.7").
Notation Zminus := Z.sub (only parsing).
Notation Zmult := Z.mul (only parsing).
Notation Zcompare := Z.compare (compat "8.7").
Notation Zsgn := Z.sgn (compat "8.7").
Notation Zle := Z.le (compat "8.7").
Notation Zge := Z.ge (compat "8.7").
Notation Zlt := Z.lt (compat "8.7").
Notation Zgt := Z.gt (compat "8.7").
Notation Zmax := Z.max (compat "8.7").
Notation Zmin := Z.min (compat "8.7").
Notation Zabs := Z.abs (compat "8.7").
Notation Zabs_nat := Z.abs_nat (compat "8.7").
Notation Zabs_N := Z.abs_N (compat "8.7").
Notation Z_of_nat := Z.of_nat (only parsing).
Notation Z_of_N := Z.of_N (only parsing).

Notation Zind := Z.peano_ind (only parsing).
Notation Zopp_0 := Z.opp_0 (compat "8.7").
Notation Zopp_involutive := Z.opp_involutive (compat "8.7").
Notation Zopp_inj := Z.opp_inj (compat "8.7").
Notation Zplus_0_l := Z.add_0_l (only parsing).
Notation Zplus_0_r := Z.add_0_r (only parsing).
Notation Zplus_comm := Z.add_comm (only parsing).
Notation Zopp_plus_distr := Z.opp_add_distr (only parsing).
Notation Zopp_succ := Z.opp_succ (compat "8.7").
Notation Zplus_opp_r := Z.add_opp_diag_r (only parsing).
Notation Zplus_opp_l := Z.add_opp_diag_l (only parsing).
Notation Zplus_assoc := Z.add_assoc (only parsing).
Notation Zplus_permute := Z.add_shuffle3 (only parsing).
Notation Zplus_reg_l := Z.add_reg_l (only parsing).
Notation Zplus_succ_l := Z.add_succ_l (only parsing).
Notation Zplus_succ_comm := Z.add_succ_comm (only parsing).
Notation Zsucc_discr := Z.neq_succ_diag_r (only parsing).
Notation Zsucc_inj := Z.succ_inj (compat "8.7").
Notation Zsucc'_inj := Z.succ_inj (compat "8.7").
Notation Zsucc'_pred' := Z.succ_pred (compat "8.7").
Notation Zpred'_succ' := Z.pred_succ (compat "8.7").
Notation Zpred'_inj := Z.pred_inj (compat "8.7").
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

Notation Zpos_xI := Pos2Z.inj_xI (only parsing).
Notation Zpos_xO := Pos2Z.inj_xO (only parsing).
Notation Zneg_xI := Pos2Z.neg_xI (only parsing).
Notation Zneg_xO := Pos2Z.neg_xO (only parsing).
Notation Zopp_neg := Pos2Z.opp_neg (only parsing).
Notation Zpos_succ_morphism := Pos2Z.inj_succ (only parsing).
Notation Zpos_mult_morphism := Pos2Z.inj_mul (only parsing).
Notation Zpos_minus_morphism := Pos2Z.inj_sub (only parsing).
Notation Zpos_eq_rev := Pos2Z.inj (only parsing).
Notation Zpos_plus_distr := Pos2Z.inj_add (only parsing).
Notation Zneg_plus_distr := Pos2Z.add_neg_neg (only parsing).

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
Lemma Zeq_minus : forall n m, n = m -> n - m = 0.
Proof (fun n m => proj2 (Z.sub_move_0_r n m)).
Lemma Zminus_eq : forall n m, n - m = 0 -> n = m.
Proof (fun n m => proj1 (Z.sub_move_0_r n m)).
Lemma Zmult_0_r_reverse : forall n, 0 = n * 0.
Proof (SYM1 Z.mul_0_r).
Lemma Zmult_assoc_reverse : forall n m p, n * m * p = n * (m * p).
Proof (SYM3 Z.mul_assoc).
Lemma Zmult_integral : forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof (fun n m => proj1 (Z.mul_eq_0 n m)).
Lemma Zmult_integral_l : forall n m, n <> 0 -> m * n = 0 -> m = 0.
Proof (fun n m H H' => Z.mul_eq_0_l m n H' H).
Lemma Zopp_mult_distr_l : forall n m, - (n * m) = - n * m.
Proof (SYM2 Z.mul_opp_l).
Lemma Zopp_mult_distr_r : forall n m, - (n * m) = n * - m.
Proof (SYM2 Z.mul_opp_r).
Lemma Zmult_minus_distr_l : forall n m p, p * (n - m) = p * n - p * m.
Proof (fun n m p => Z.mul_sub_distr_l p n m).
Lemma Zmult_succ_r_reverse : forall n m, n * m + n = n * Z.succ m.
Proof (SYM2 Z.mul_succ_r).
Lemma Zmult_succ_l_reverse : forall n m, n * m + m = Z.succ n * m.
Proof (SYM2 Z.mul_succ_l).
Lemma Zpos_eq : forall p q, p = q -> Z.pos p = Z.pos q.
Proof. congruence. Qed.
Lemma Zpos_eq_iff : forall p q, p = q <-> Z.pos p = Z.pos q.
Proof (fun p q => iff_sym (Pos2Z.inj_iff p q)).

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
