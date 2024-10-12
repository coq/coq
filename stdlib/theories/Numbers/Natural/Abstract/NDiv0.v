(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub NDiv.

Module Type NDivPropPrivate (N : NAxiomsSig') (NP : NSubProp N).
Declare Module Private_NDivProp : NDivProp N NP.
End NDivPropPrivate.

(** Properties of Euclidean Division with a / 0 == 0 and a mod 0 == a *)

Module Type NDivProp0
  (Import N : NAxiomsSig')
  (Import NP : NSubProp N)
  (Import D0 : NZDivSpec0 N N N)
  (Import P : NDivPropPrivate N NP).

Import Private_NDivProp.

(** Let's now state again theorems, but without useless hypothesis. *)

Module Div0.

Lemma div_0_l : forall a, 0/a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Ha].
  - apply div_0_r.
  - now apply div_0_l.
Qed.

Lemma mod_0_l : forall a, 0 mod a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Hb].
  - apply mod_0_r.
  - now apply mod_0_l.
Qed.

#[local] Hint Rewrite div_0_l mod_0_l div_0_r mod_0_r : nz.

Lemma div_mod : forall a b, a == b*(a/b) + (a mod b).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mod.
Qed.

Lemma mod_eq : forall a b, a mod b == a - b*(a/b).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_eq.
Qed.

Lemma mod_same : forall a, a mod a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Ha].
  - now nzsimpl.
  - now apply mod_same.
Qed.

Lemma mod_mul : forall a b, (a*b) mod b == 0.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_mul.
Qed.

Lemma mod_le : forall a b, a mod b <= a.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_le.
Qed.

Lemma div_le_mono : forall a b c, a<=b -> a/c <= b/c.
Proof.
  intros a b c. destruct (eq_decidable c 0) as [->|Hc].
  - now nzsimpl.
  - now apply div_le_mono.
Qed.

Lemma mul_div_le : forall a b, b*(a/b) <= a.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. apply le_0_l.
  - now apply mul_div_le.
Qed.

Lemma div_exact : forall a b, (a == b*(a/b) <-> a mod b == 0).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_exact.
Qed.

Lemma div_lt_upper_bound : forall a b q, a < b*q -> a/b < q.
Proof.
  intros a b q. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. now intros ?%nlt_0_r.
  - now apply div_lt_upper_bound.
Qed.

Lemma div_le_upper_bound : forall a b q, a <= b*q -> a/b <= q.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. intros. apply le_0_l.
  - now apply div_le_upper_bound.
Qed.

Lemma mod_add : forall a b c, (a + b * c) mod c == a mod c.
Proof.
  intros a b c. destruct (eq_decidable c 0) as [->|Hc].
  - now nzsimpl.
  - now apply mod_add.
Qed.

Lemma div_mul_cancel_r : forall a b c, c~=0 -> (a*c)/(b*c) == a/b.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mul_cancel_r.
Qed.

Lemma div_mul_cancel_l : forall a b c, c~=0 -> (c*a)/(c*b) == a/b.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mul_cancel_l.
Qed.

Lemma mul_mod_distr_r : forall a b c, (a*c) mod (b*c) == (a mod b) * c.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - destruct (eq_decidable c 0) as [->|Hc].
    + now nzsimpl.
    + now apply mul_mod_distr_r.
Qed.

Lemma mul_mod_distr_l : forall a b c, (c*a) mod (c*b) == c * (a mod b).
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - destruct (eq_decidable c 0) as [->|Hc].
    + now nzsimpl.
    + now apply mul_mod_distr_l.
Qed.

Lemma mod_mod : forall a n, (a mod n) mod n == a mod n.
Proof.
  intros a n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply mod_mod.
Qed.

Lemma mul_mod_idemp_l : forall a b n, ((a mod n)*b) mod n == (a*b) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply mul_mod_idemp_l.
Qed.

Lemma mul_mod_idemp_r : forall a b n, (a*(b mod n)) mod n == (a*b) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply mul_mod_idemp_r.
Qed.

Lemma mul_mod : forall a b n, (a * b) mod n == ((a mod n) * (b mod n)) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply mul_mod.
Qed.

Lemma add_mod_idemp_l : forall a b n, ((a mod n)+b) mod n == (a+b) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply add_mod_idemp_l.
Qed.

Lemma add_mod_idemp_r : forall a b n, (a+(b mod n)) mod n == (a+b) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply add_mod_idemp_r.
Qed.

Lemma add_mod : forall a b n, (a+b) mod n == (a mod n + b mod n) mod n.
Proof.
  intros a b n. destruct (eq_decidable n 0) as [->|Hn].
  - now nzsimpl.
  - now apply add_mod.
Qed.

Lemma div_div : forall a b c, (a/b)/c == a/(b*c).
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - destruct (eq_decidable c 0) as [->|Hc].
    + now nzsimpl.
    + now apply div_div.
Qed.

Lemma mod_mul_r : forall a b c, a mod (b*c) == a mod b + b*((a/b) mod c).
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - destruct (eq_decidable c 0) as [->|Hc].
    + nzsimpl. rewrite add_comm. apply div_mod.
    + now apply mod_mul_r.
Qed.

Lemma add_mul_mod_distr_l : forall a b c d, d<c -> (c*a+d) mod (c*b) == c*(a mod b)+d.
Proof.
  intros a b c d ?. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - apply add_mul_mod_distr_l; intuition auto using le_0_l.
Qed.

Lemma add_mul_mod_distr_r : forall a b c d, d<c -> (a*c+d) mod (b*c) == (a mod b)*c+d.
Proof.
  intros a b c d ?. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - apply add_mul_mod_distr_r; intuition auto using le_0_l.
Qed.

Lemma div_mul_le : forall a b c, c*(a/b) <= (c*a)/b.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mul_le.
Qed.

Lemma mod_divides : forall a b, (a mod b == 0 <-> exists c, a == b*c).
Proof.
  intros a b. destruct (eq_decidable b 0) as [Hb|Hb].
  - split.
    + intros Hab. exists 0. revert Hab. rewrite Hb. now nzsimpl.
    + intros [c Hc]. revert Hc. rewrite Hb. now nzsimpl.
  - now apply mod_divides.
Qed.

End Div0.

(** Unchanged theorems. *)

Definition mod_upper_bound := mod_upper_bound.
Definition div_mod_unique := div_mod_unique.
Definition div_unique := div_unique.
Definition mod_unique := mod_unique.
Definition div_unique_exact := div_unique_exact.
Definition div_same := div_same.
Definition div_small := div_small.
Definition mod_small := mod_small.
Definition div_1_r := div_1_r.
Definition mod_1_r := mod_1_r.
Definition div_1_l := div_1_l.
Definition mod_1_l := mod_1_l.
Definition div_mul := div_mul.
Definition div_str_pos := div_str_pos.
Definition div_small_iff := div_small_iff.
Definition mod_small_iff := mod_small_iff.
Definition div_str_pos_iff := div_str_pos_iff.
Definition div_lt := div_lt.
Definition mul_succ_div_gt := mul_succ_div_gt.
Definition div_le_lower_bound := div_le_lower_bound.
Definition div_le_compat_l := div_le_compat_l.
Definition div_add := div_add.
Definition div_add_l := div_add_l.

(** Deprecation statements.
    After deprecation phase, remove statements below
    in favor of Div0 statements. *)

#[deprecated(since="8.17",note="Use Div0.mod_eq instead.")]
Notation mod_eq := mod_eq (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_same instead.")]
Notation mod_same := mod_same (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_0_l instead.")]
Notation div_0_l := div_0_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_0_l instead.")]
Notation mod_0_l := mod_0_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_mul instead.")]
Notation mod_mul := mod_mul (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_le instead.")]
Notation mod_le := mod_le (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_le_mono instead.")]
Notation div_le_mono := div_le_mono (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_div_le instead.")]
Notation mul_div_le := mul_div_le (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_exact instead.")]
Notation div_exact := div_exact (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_lt_upper_bound instead.")]
Notation div_lt_upper_bound := div_lt_upper_bound (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_le_upper_bound instead.")]
Notation div_le_upper_bound := div_le_upper_bound (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_add instead.")]
Notation mod_add := mod_add (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_mul_cancel_r instead.")]
Notation div_mul_cancel_r := div_mul_cancel_r (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_mul_cancel_l instead.")]
Notation div_mul_cancel_l := div_mul_cancel_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_mod_distr_r instead.")]
Notation mul_mod_distr_r := mul_mod_distr_r (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_mod_distr_l instead.")]
Notation mul_mod_distr_l := mul_mod_distr_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_mod instead.")]
Notation mod_mod := mod_mod (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_mod_idemp_l instead.")]
Notation mul_mod_idemp_l := mul_mod_idemp_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_mod_idemp_r instead.")]
Notation mul_mod_idemp_r := mul_mod_idemp_r (only parsing).
#[deprecated(since="8.17",note="Use Div0.mul_mod instead.")]
Notation mul_mod := mul_mod (only parsing).
#[deprecated(since="8.17",note="Use Div0.add_mod_idemp_l instead.")]
Notation add_mod_idemp_l := add_mod_idemp_l (only parsing).
#[deprecated(since="8.17",note="Use Div0.add_mod_idemp_r instead.")]
Notation add_mod_idemp_r := add_mod_idemp_r (only parsing).
#[deprecated(since="8.17",note="Use Div0.add_mod instead.")]
Notation add_mod := add_mod (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_div instead.")]
Notation div_div := div_div (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_mul_r instead.")]
Notation mod_mul_r := mod_mul_r (only parsing).
#[deprecated(since="8.17",note="Use Div0.div_mul_le instead.")]
Notation div_mul_le := div_mul_le (only parsing).
#[deprecated(since="8.17",note="Use Div0.mod_divides instead.")]
Notation mod_divides := mod_divides (only parsing).

End NDivProp0.
