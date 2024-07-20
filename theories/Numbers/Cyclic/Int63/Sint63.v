(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import ZArith.
Import Znumtheory.
Require Export Uint63 Sint63Axioms.
Require Import Lia.

Notation min_int := Sint63Axioms.min_int (only parsing).
Notation to_Z := Sint63Axioms.to_Z (only parsing).
Notation asr_spec := Sint63Axioms.asr_spec (only parsing).
Notation div_spec := Sint63Axioms.div_spec (only parsing).
Notation mod_spec := Sint63Axioms.mod_spec (only parsing).
Notation ltb_spec := Sint63Axioms.ltb_spec (only parsing).
Notation leb_spec := Sint63Axioms.leb_spec (only parsing).
Notation compare_spec := Sint63Axioms.compare_spec (only parsing).

Declare Scope sint63_scope.
Definition printer (x : int_wrapper) : pos_neg_int63 :=
  if (int_wrap x <? 4611686018427387904)%uint63 then (* 2^62 *)
    Pos (int_wrap x)
  else
    Neg ((int_wrap x) lxor max_int + 1)%uint63.
Definition parser (x : pos_neg_int63) : option int :=
  match x with
  | Pos p => if (p <? 4611686018427387904)%uint63 then Some p else None
  | Neg n => if (n <=? 4611686018427387904)%uint63
             then Some ((n - 1) lxor max_int)%uint63 else None
  end.
Number Notation int parser printer : sint63_scope.


Module Import Sint63NotationsInternalA.
Delimit Scope sint63_scope with sint63.
Bind Scope sint63_scope with int.
End Sint63NotationsInternalA.

Module Import Sint63NotationsInternalB.
Infix "<<" := PrimInt63.lsl (at level 30, no associativity) : sint63_scope.
(* TODO do we want >> to be asr or lsr? And is there a notation for the other one? *)
Infix ">>" := asr (at level 30, no associativity) : sint63_scope.
Infix "land" := PrimInt63.land (at level 40, left associativity) : sint63_scope.
Infix "lor" := PrimInt63.lor (at level 40, left associativity) : sint63_scope.
Infix "lxor" := PrimInt63.lxor (at level 40, left associativity) : sint63_scope.
Infix "+" := PrimInt63.add : sint63_scope.
Infix "-" := PrimInt63.sub : sint63_scope.
Infix "*" := PrimInt63.mul : sint63_scope.
Infix "/" := divs : sint63_scope.
Infix "mod" := mods (at level 40, no associativity) : sint63_scope.
Infix "=?" := PrimInt63.eqb (at level 70, no associativity) : sint63_scope.
Infix "<?" := ltsb (at level 70, no associativity) : sint63_scope.
Infix "<=?" := lesb (at level 70, no associativity) : sint63_scope.
Infix "≤?" := lesb (at level 70, no associativity) : sint63_scope.
Notation "- x" := (opp x) : sint63_scope.
Notation "n ?= m" := (compares n m)
  (at level 70, no associativity) : sint63_scope.
End Sint63NotationsInternalB.

Definition max_int := Eval vm_compute in (min_int - 1)%sint63.

Lemma to_Z_0 : to_Z 0 = 0.
Proof. easy. Qed.

Lemma to_Z_min : to_Z min_int = - (wB / 2).
Proof. easy. Qed.

Lemma to_Z_max : to_Z max_int = wB / 2 - 1.
Proof. easy. Qed.

Lemma to_Z_bounded : forall x, (to_Z min_int <= to_Z x <= to_Z max_int)%Z.
Proof.
  intros x; unfold to_Z.
  case ltbP; [> lia | intros _].
  case (ltbP max_int); [> intros _ | now intros H; exfalso; apply H].
  rewrite opp_spec.
  rewrite Z_mod_nz_opp_full by easy.
  rewrite Z.mod_small by apply Uint63.to_Z_bounded.
  case ltbP.
  - intros ltxmin; split.
    + now transitivity 0%Z; [>| now apply Uint63.to_Z_bounded].
    + replace (φ min_int%uint63) with (φ max_int%uint63 + 1)%Z in ltxmin.
      * lia.
      * now compute.
  - rewrite Z.nlt_ge; intros leminx.
    rewrite opp_spec.
    rewrite Z_mod_nz_opp_full.
    + rewrite Z.mod_small by apply Uint63.to_Z_bounded.
      split.
      * rewrite <- Z.opp_le_mono.
        now rewrite <- Z.sub_le_mono_l.
      * transitivity 0%Z; [>| now apply Uint63.to_Z_bounded].
        rewrite Z.opp_nonpos_nonneg.
        apply Zle_minus_le_0.
        apply Z.lt_le_incl.
        now apply Uint63.to_Z_bounded.
    + rewrite Z.mod_small by apply Uint63.to_Z_bounded.
      now intros eqx0; rewrite eqx0 in leminx.
Qed.

Lemma of_to_Z : forall x, of_Z (to_Z x) = x.
Proof.
  unfold to_Z, of_Z.
  intros x.
  generalize (Uint63.to_Z_bounded x).
  case ltbP.
  - intros ltxmin [leq0x _].
    generalize (Uint63Axioms.of_to_Z x).
    destruct (φ x%uint63).
    + now intros <-.
    + now intros <-; unfold Uint63Axioms.of_Z.
    + now intros _.
  - intros nltxmin leq0xltwB.
    fold (- x)%sint63; rewrite (opp_spec x).
    rewrite Z_mod_nz_opp_full.
    + rewrite Zmod_small by easy.
      destruct (wB - φ x%uint63) eqn: iswbmx.
      * lia.
      * simpl.
        apply to_Z_inj.
        rewrite opp_spec.
        generalize (of_Z_spec (Z.pos p)).
        simpl Uint63Axioms.of_Z; intros ->.
        rewrite <- iswbmx.
        rewrite <- Z.sub_0_l.
        rewrite <- (Zmod_0_l wB).
        rewrite <- Zminus_mod.
        replace (0 - _) with (φ x%uint63 - wB) by ring.
        rewrite <- Zminus_mod_idemp_r.
        rewrite Z_mod_same_full.
        rewrite Z.sub_0_r.
        now rewrite Z.mod_small.
      * lia.
    + rewrite Z.mod_small by easy.
      intros eqx0; revert nltxmin; rewrite eqx0.
      now compute.
Qed.

Lemma to_Z_inj (x y : int) : to_Z x = to_Z y -> x = y.
Proof. exact (fun e => can_inj of_to_Z e). Qed.

Lemma to_Z_mod_Uint63to_Z (x : int) : to_Z x mod wB = φ x%uint63.
Proof.
  unfold to_Z.
  case ltbP; [> now rewrite Z.mod_small by now apply Uint63.to_Z_bounded |].
  rewrite Z.nlt_ge; intros gexmin.
  rewrite opp_to_Z_opp; rewrite Z.mod_small by now apply Uint63.to_Z_bounded.
  - easy.
  - now intros neqx0; rewrite neqx0 in gexmin.
Qed.


(** Centered modulo *)
Definition cmod (x d : Z) : Z :=
  (x + d / 2) mod d - (d / 2).

Lemma cmod_mod (x d : Z) :
  cmod (x mod d) d = cmod x d.
Proof.
  now unfold cmod; rewrite Zplus_mod_idemp_l.
Qed.

Lemma cmod_small (x d : Z) :
  - (d / 2) <= x < d / 2 -> cmod x d = x.
Proof.
  intros bound.
  unfold cmod.
  rewrite Zmod_small; [> lia |].
  split; [> lia |].
  rewrite Z.lt_add_lt_sub_r.
  apply (Z.lt_le_trans _ (d / 2)); [> easy |].
  now rewrite <- Z.le_add_le_sub_r, Z.add_diag, Z.mul_div_le.
Qed.

Lemma to_Z_cmodwB (x : int) :
  to_Z x = cmod (φ x%uint63) wB.
Proof.
  unfold to_Z, cmod.
  case ltbP; change φ (min_int)%uint63 with (wB / 2).
  - intros ltxmin.
    rewrite Z.mod_small; [> lia |].
    split.
    + now apply Z.add_nonneg_nonneg; try apply Uint63.to_Z_bounded.
    + change wB with (wB / 2 + wB / 2) at 2; lia.
  - rewrite Z.nlt_ge; intros gexmin.
    rewrite Uint63.opp_spec.
    rewrite Z_mod_nz_opp_full.
    + rewrite Z.mod_small by apply Uint63.to_Z_bounded.
      rewrite <- (Z_mod_plus_full _ (-1)).
      change (-1 * wB) with (- (wB / 2) - wB / 2).
      rewrite <- Z.add_assoc, Zplus_minus.
      rewrite Z.mod_small.
      * change wB with (wB / 2 + wB / 2) at 1; lia.
      * split; [> lia |].
        apply Z.lt_sub_lt_add_r.
        transitivity wB; [>| easy].
        now apply Uint63.to_Z_bounded.
    + rewrite Z.mod_small by now apply Uint63.to_Z_bounded.
      now intros not0; rewrite not0 in gexmin.
Qed.

Lemma of_Z_spec (z : Z) : to_Z (of_Z z) = cmod z wB.
Proof. now rewrite to_Z_cmodwB, Uint63.of_Z_spec, cmod_mod. Qed.

Lemma of_Z_cmod (z : Z) : of_Z (cmod z wB) = of_Z z.
Proof. now rewrite <- of_Z_spec, of_to_Z. Qed.

Lemma is_int (z : Z) :
    to_Z min_int <= z <= to_Z max_int ->
  z = to_Z (of_Z z).
Proof.
  rewrite to_Z_min, to_Z_max.
  intros bound; rewrite of_Z_spec, cmod_small; lia.
Qed.

Lemma of_pos_spec (p : positive) :
  to_Z (of_pos p) = cmod (Zpos p) wB.
Proof. rewrite <- of_Z_spec; simpl; reflexivity. Qed.

(** Specification of operations that coincide on signed and unsigned ints *)

Lemma add_spec (x y : int) :
  to_Z (x + y)%sint63 = cmod (to_Z x + to_Z y) wB.
Proof.
  rewrite to_Z_cmodwB, Uint63Axioms.add_spec.
  rewrite <- 2!to_Z_mod_Uint63to_Z, <- Z.add_mod by easy.
  now rewrite cmod_mod.
Qed.

Lemma sub_spec (x y : int) :
  to_Z (x - y)%sint63 = cmod (to_Z x - to_Z y) wB.
Proof.
  rewrite to_Z_cmodwB, Uint63Axioms.sub_spec.
  rewrite <- 2!to_Z_mod_Uint63to_Z, <- Zminus_mod by easy.
  now rewrite cmod_mod.
Qed.

Lemma mul_spec (x y : int) :
  to_Z (x * y)%sint63 = cmod (to_Z x * to_Z y) wB.
Proof.
  rewrite to_Z_cmodwB, Uint63Axioms.mul_spec.
  rewrite <- 2!to_Z_mod_Uint63to_Z, <- Zmult_mod by easy.
  now rewrite cmod_mod.
Qed.

Lemma succ_spec (x : int) :
  to_Z (succ x)%sint63 = cmod (to_Z x + 1) wB.
Proof. now unfold succ; rewrite add_spec. Qed.

Lemma pred_spec (x : int) :
  to_Z (pred x)%sint63 = cmod (to_Z x - 1) wB.
Proof. now unfold pred; rewrite sub_spec. Qed.

Lemma opp_spec (x : int) :
  to_Z (- x)%sint63 = cmod (- to_Z x) wB.
Proof.
  rewrite to_Z_cmodwB, Uint63.opp_spec.
  rewrite <- Z.sub_0_l, <- to_Z_mod_Uint63to_Z, Zminus_mod_idemp_r.
  now rewrite cmod_mod.
Qed.

(** Behaviour when there is no under or overflow *)

Lemma to_Z_add (x y : int) :
    to_Z min_int <= to_Z x + to_Z y <= to_Z max_int ->
  to_Z (x + y) = to_Z x + to_Z y.
Proof.
  rewrite to_Z_min, to_Z_max; intros bound.
  now rewrite add_spec, cmod_small; [>| lia].
Qed.

Lemma to_Z_sub (x y : int) :
    to_Z min_int <= to_Z x - to_Z y <= to_Z max_int ->
  to_Z (x - y) = to_Z x - to_Z y.
Proof.
  rewrite to_Z_min, to_Z_max; intros bound.
  now rewrite sub_spec, cmod_small; [>| lia].
Qed.

Lemma to_Z_mul (x y : int) :
    to_Z min_int <= to_Z x * to_Z y <= to_Z max_int ->
  to_Z (x * y) = to_Z x * to_Z y.
Proof.
  rewrite to_Z_min, to_Z_max; intros bound.
  now rewrite mul_spec, cmod_small; [>| lia].
Qed.

Lemma to_Z_succ (x : int) :
  x <> max_int -> to_Z (succ x) = to_Z x + 1.
Proof.
  intros neq_x_max.
  rewrite succ_spec, cmod_small; [> easy |].
  assert (to_Z x <> to_Z max_int) by now intros ?; apply neq_x_max, to_Z_inj.
  rewrite <- to_Z_min; change (wB / 2) with (to_Z max_int + 1).
  generalize (to_Z_bounded x); lia.
Qed.

Lemma to_Z_pred (x : int) :
  x <> min_int -> to_Z (pred x) = to_Z x - 1.
Proof.
  intros neq_x_min.
  rewrite pred_spec, cmod_small; [> easy |].
  assert (to_Z x <> to_Z min_int) by now intros ?; apply neq_x_min, to_Z_inj.
  rewrite <- to_Z_min; change (wB / 2) with (to_Z max_int + 1).
  generalize (to_Z_bounded x); lia.
Qed.

Lemma to_Z_opp (x : int) :
  x <> min_int -> to_Z (- x) = - to_Z x.
Proof.
  intros neq_x_min.
  rewrite opp_spec, cmod_small; [> easy |].
  rewrite <- to_Z_min; change (wB / 2) with (to_Z max_int + 1).
  pose proof (to_Z_bounded x) as bound.
  split.
  - now rewrite Z.opp_le_mono, Z.opp_involutive; transitivity (to_Z max_int).
  - rewrite Z.opp_lt_mono, Z.opp_involutive.
    assert (to_Z x <> to_Z min_int) by now intros ?; apply neq_x_min, to_Z_inj.
    change (- (to_Z max_int + 1)) with (to_Z min_int); lia.
Qed.

(** Relationship with of_Z *)

Lemma add_of_Z (x y : int) :
  (x + y)%sint63 = of_Z (to_Z x + to_Z y).
Proof. now rewrite <- of_Z_cmod, <- add_spec, of_to_Z. Qed.

Lemma sub_of_Z (x y : int) :
  (x - y)%sint63 = of_Z (to_Z x - to_Z y).
Proof. now rewrite <- of_Z_cmod, <- sub_spec, of_to_Z. Qed.

Lemma mul_of_Z (x y : int) :
  (x * y)%sint63 = of_Z (to_Z x * to_Z y).
Proof. now rewrite <- of_Z_cmod, <- mul_spec, of_to_Z. Qed.

Lemma succ_of_Z (x : int) :
  (succ x)%sint63 = of_Z (to_Z x + 1).
Proof. now rewrite <- of_Z_cmod, <- succ_spec, of_to_Z. Qed.

Lemma pred_of_Z (x : int) :
  (pred x)%sint63 = of_Z (to_Z x - 1).
Proof. now rewrite <- of_Z_cmod, <- pred_spec, of_to_Z. Qed.

Lemma opp_of_Z (x : int) :
  (- x)%sint63 = of_Z (- to_Z x).
Proof. now rewrite <- of_Z_cmod, <- opp_spec, of_to_Z. Qed.

(** Comparison *)
Import Bool.

Lemma eqbP x y : reflect (to_Z x = to_Z y) (x =? y)%sint63.
Proof.
  apply iff_reflect; rewrite Uint63.eqb_spec.
  now split; [> apply to_Z_inj | apply f_equal].
Qed.

Lemma ltbP x y : reflect (to_Z x < to_Z y) (x <? y)%sint63.
Proof. now apply iff_reflect; symmetry; apply ltb_spec. Qed.

Lemma lebP x y : reflect (to_Z x <= to_Z y) (x ≤? y)%sint63.
Proof. now apply iff_reflect; symmetry; apply leb_spec. Qed.

(** Absolute value *)

Definition abs (n : int) : int := if (0 <=? n)%sint63 then n else - n.

Lemma abs_spec (x : int) :
  to_Z (abs x)%sint63 = cmod (Z.abs (to_Z x)) wB.
Proof.
  unfold abs; case lebP.
  - intro leq0x; rewrite Z.abs_eq by easy.
    now rewrite <- of_Z_spec, of_to_Z.
  - intro nleq0x; rewrite Z.abs_neq.
    + now rewrite opp_spec.
    + now apply Z.lt_le_incl; rewrite <- Z.nle_gt.
Qed.

Lemma to_Z_abs (x : int) :
  x <> min_int -> to_Z (abs x) = Z.abs (to_Z x).
Proof.
  intros neq_x_min.
  unfold abs; case lebP.
  - now intros leq_0_x; rewrite Z.abs_eq.
  - rewrite to_Z_opp by easy.
    intros nleq_0_x; rewrite Z.abs_neq; [> easy |].
    change 0 with (to_Z 0); lia.
Qed.

Remark abs_min_int : abs min_int = min_int.
Proof. easy. Qed.

Lemma abs_of_Z (x : int) :
  abs x = of_Z (Z.abs (to_Z x)).
Proof. now rewrite <- of_Z_cmod, <- abs_spec, of_to_Z. Qed.

(** ASR *)
Lemma asr_0 (i : int) : (0 >> i)%sint63 = 0%sint63.
Proof. now apply to_Z_inj; rewrite asr_spec. Qed.

Lemma asr_0_r (i : int) : (i >> 0)%sint63 = i.
Proof. now apply to_Z_inj; rewrite asr_spec, Zdiv_1_r. Qed.

Lemma asr_neg_r (i n : int) : to_Z n < 0 -> (i >> n)%sint63 = 0%sint63.
Proof.
  intros ltn0.
  apply to_Z_inj.
  rewrite asr_spec, Z.pow_neg_r by assumption.
  now rewrite Zdiv_0_r.
Qed.

Lemma asr_1 (n : int) : (1 >> n)%sint63 = (n =? 0)%sint63.
Proof.
  apply to_Z_inj; rewrite asr_spec.
  case eqbP; [> now intros -> | intros neqn0].
  case (lebP 0 n).
  - intros le0n.
    apply Z.div_1_l; apply Z.pow_gt_1; [> easy |].
    rewrite to_Z_0 in *; lia.
  - rewrite Z.nle_gt; intros ltn0.
    now rewrite Z.pow_neg_r.
Qed.


Notation asr := asr (only parsing).
Notation div := divs (only parsing).
Notation rem := mods (only parsing).
Notation ltb := ltsb (only parsing).
Notation leb := lesb (only parsing).
Notation compare := compares (only parsing).

Module Export Sint63Notations.
  Export Sint63NotationsInternalA.
  Export Sint63NotationsInternalB.
End Sint63Notations.
