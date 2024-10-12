(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub NDiv0 NGcd NLcm.

Module Type NLcmPropPrivate
  (A : NAxiomsSig') (B : NSubProp A) (C : NDivPropPrivate A B) (D : NGcdProp A B).
Declare Module Private_NLcmProp : NLcmProp A B (C.Private_NDivProp) D.
End NLcmPropPrivate.

Module Type NLcmProp0
  (Import A : NAxiomsSig')
  (Import B : NSubProp A)
  (Import A' : NZDivSpec0 A A A)
  (Import D : NGcdProp A B)
  (Import C : NDivPropPrivate A B)
  (Import C' : NDivProp0 A B A' C)
  (Import E : NLcmPropPrivate A B C D).

Import Private_NLcmProp.
Import Div0.

Definition lcm a b := a*(b/gcd a b).
#[global] Instance lcm_wd : Proper (eq==>eq==>eq) lcm := lcm_wd.

(* The types are restated to avoid [Private_NLcmProp.lcm] indirection. *)
Definition gcd_div_gcd : forall a b g, g ~= 0 -> g == gcd a b ->
  gcd (a / g) (b / g) == 1 := gcd_div_gcd.
Definition divide_lcm_l : forall a b, (a | lcm a b) := divide_lcm_l.
Definition gcd_div_swap : forall a b, a / gcd a b * b == a * (b / gcd a b) := gcd_div_swap.
Definition divide_lcm_r : forall a b, (b | lcm a b) := divide_lcm_r.
Definition lcm_least : forall a b c, (a | c) -> (b | c) -> (lcm a b | c) := lcm_least.
Definition lcm_comm : forall a b, lcm a b == lcm b a := lcm_comm.
Definition lcm_divide_iff : forall n m p, (lcm n m | p) <-> (n | p) /\ (m | p) := lcm_divide_iff.
Definition lcm_assoc : forall n m p, lcm n (lcm m p) == lcm (lcm n m) p := lcm_assoc.
Definition lcm_0_l : forall n, lcm 0 n == 0 := lcm_0_l.
Definition lcm_0_r : forall n, lcm n 0 == 0 := lcm_0_r.
Definition lcm_1_l : forall n, lcm 1 n == n := lcm_1_l.
Definition lcm_1_r : forall n, lcm n 1 == n := lcm_1_r.
Definition lcm_diag : forall n : t, lcm n n == n := lcm_diag.
Definition lcm_eq_0 : forall n m, lcm n m == 0 <-> n == 0 \/ m == 0 := lcm_eq_0.
Definition divide_lcm_eq_r : forall n m, (n | m) -> lcm n m == m := divide_lcm_eq_r.
Definition divide_lcm_iff : forall n m, (n | m) <-> lcm n m == m := divide_lcm_iff.
Definition lcm_mul_mono_l : forall n m p, lcm (p * n) (p * m) == p * lcm n m := lcm_mul_mono_l.
Definition lcm_mul_mono_r : forall n m p, lcm (n * p) (m * p) == lcm n m * p := lcm_mul_mono_r.
Definition gcd_1_lcm_mul : forall n m, n ~= 0 -> m ~= 0 ->
  gcd n m == 1 <-> lcm n m == n * m := gcd_1_lcm_mul.
Module Lcm0.

#[local] Hint Rewrite div_0_l mod_0_l div_0_r mod_0_r gcd_0_l gcd_0_r : nz.

Lemma mod_divide : forall a b, (a mod b == 0 <-> (b|a)).
Proof.
  intros a b. destruct (eq_decidable b 0) as [Hb|Hb].
  - split.
    + intros Hab. exists 0. revert Hab. rewrite Hb. now nzsimpl.
    + intros [c Hc]. revert Hc. rewrite Hb. now nzsimpl.
  - now apply mod_divide.
Qed.

Lemma divide_div_mul_exact : forall a b c, (b|a) -> (c*a)/b == c*(a/b).
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply divide_div_mul_exact.
Qed.

Lemma gcd_div_factor : forall a b c, (c|a) -> (c|b) ->
  gcd (a/c) (b/c) == (gcd a b)/c.
Proof.
  intros a b c. destruct (eq_decidable c 0) as [->|Hc].
  - now nzsimpl.
  - now apply gcd_div_factor.
Qed.

Lemma gcd_mod : forall a b, gcd (a mod b) b == gcd b a.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply gcd_mod.
Qed.

Lemma lcm_equiv1 : forall a b, a * (b / gcd a b) == (a*b)/gcd a b.
Proof.
  intros a b. destruct (eq_decidable (gcd a b) 0) as [->|?].
  - now nzsimpl.
  - now apply lcm_equiv1.
Qed.

Lemma lcm_equiv2 : forall a b, (a / gcd a b) * b == (a*b)/gcd a b.
Proof.
  intros a b. destruct (eq_decidable (gcd a b) 0) as [->|?].
  - now nzsimpl.
  - now apply lcm_equiv2.
Qed.

Lemma divide_div : forall a b c, (a|b) -> (b|c) -> (b/a|c/a).
Proof.
  intros a b c. destruct (eq_decidable a 0) as [->|Ha].
  - now nzsimpl.
  - now apply divide_div.
Qed.

Lemma lcm_unique : forall n m p,
  (n|p) -> (m|p) -> (forall q, (n|q) -> (m|q) -> (p|q)) -> lcm n m == p.
Proof. intros n m p. apply lcm_unique, le_0_l. Qed.

Lemma lcm_unique_alt : forall n m p,
  (forall q, (p|q) <-> (n|q) /\ (m|q)) -> lcm n m == p.
Proof. intros n m p. apply lcm_unique_alt, le_0_l. Qed.

End Lcm0.

(** Deprecation statements.
    After deprecation phase, remove statements below
    in favor of Lcm0 statements. *)

#[deprecated(since="8.17",note="Use Lcm0.mod_divide instead.")]
Notation mod_divide := mod_divide (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.divide_div_mul_exact instead.")]
Notation divide_div_mul_exact := divide_div_mul_exact (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.gcd_div_factor instead.")]
Notation gcd_div_factor := gcd_div_factor (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.gcd_mod instead.")]
Notation gcd_mod := gcd_mod (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.gcd_mod instead.")]
Notation lcm_equiv1 := lcm_equiv1 (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.lcm_equiv2 instead.")]
Notation lcm_equiv2 := lcm_equiv2 (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.divide_div instead.")]
Notation divide_div := divide_div (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.lcm_unique instead.")]
Notation lcm_unique := lcm_unique (only parsing).
#[deprecated(since="8.17",note="Use Lcm0.lcm_unique_alt instead.")]
Notation lcm_unique_alt := lcm_unique_alt (only parsing).

End NLcmProp0.
