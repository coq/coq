(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Arith BinInt BinNat Znat Nnat.

Local Open Scope Z_scope.

(** * [Z.div_mod_to_equations], [Z.quot_rem_to_equations], [Z.to_euclidean_division_equations]:
     the tactics for preprocessing [Z.div] and [Z.modulo], [Z.quot] and [Z.rem] *)

(** These tactics use the complete specification of [Z.div] and
    [Z.modulo] ([Z.quot] and [Z.rem], respectively) to remove these
    functions from the goal without losing information.  The
    [Z.euclidean_division_equations_cleanup] tactic removes needless
    hypotheses, which makes tactics like [nia] run faster.  The tactic
    [Z.to_euclidean_division_equations] combines the handling of both variants
    of division/quotient and modulo/remainder. *)

Module Z.
  Lemma mod_0_r_ext x y : y = 0 -> x mod y = x.
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma div_0_r_ext x y : y = 0 -> x / y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Lemma rem_0_r_ext x y : y = 0 -> Z.rem x y = x.
  Proof. intro; subst; destruct x; reflexivity. Qed.
  Lemma quot_0_r_ext x y : y = 0 -> Z.quot x y = 0.
  Proof. intro; subst; destruct x; reflexivity. Qed.

  Lemma rem_bound_pos_pos x y : 0 < y -> 0 <= x -> 0 <= Z.rem x y < y.
  Proof. intros; apply Z.rem_bound_pos; assumption. Qed.
  Lemma rem_bound_neg_pos x y : y < 0 -> 0 <= x -> 0 <= Z.rem x y < -y.
  Proof. rewrite <- Z.rem_opp_r'; intros; apply Z.rem_bound_pos; rewrite ?Z.opp_pos_neg; assumption. Qed.
  Lemma rem_bound_pos_neg x y : 0 < y -> x <= 0 -> -y < Z.rem x y <= 0.
  Proof. rewrite <- (Z.opp_involutive x), Z.rem_opp_l', <- Z.opp_lt_mono, and_comm, !Z.opp_nonpos_nonneg; apply rem_bound_pos_pos. Qed.
  Lemma rem_bound_neg_neg x y : y < 0 -> x <= 0 -> y < Z.rem x y <= 0.
  Proof. rewrite <- (Z.opp_involutive x), <- (Z.opp_involutive y), Z.rem_opp_l', <- Z.opp_lt_mono, and_comm, !Z.opp_nonpos_nonneg, Z.opp_involutive; apply rem_bound_neg_pos. Qed.

  Ltac div_mod_to_equations_generalize x y :=
    pose proof (Z.div_mod x y);
    pose proof (Z.mod_pos_bound x y);
    pose proof (Z.mod_neg_bound x y);
    pose proof (div_0_r_ext x y);
    pose proof (mod_0_r_ext x y);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y) in *;
    set (r := x mod y) in *;
    clearbody q r.
  Ltac quot_rem_to_equations_generalize x y :=
    pose proof (Z.quot_rem' x y);
    pose proof (rem_bound_pos_pos x y);
    pose proof (rem_bound_pos_neg x y);
    pose proof (rem_bound_neg_pos x y);
    pose proof (rem_bound_neg_neg x y);
    pose proof (quot_0_r_ext x y);
    pose proof (rem_0_r_ext x y);
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := Z.quot x y) in *;
    set (r := Z.rem x y) in *;
    clearbody q r.

  Ltac div_mod_to_equations_step :=
    match goal with
    | [ |- context[?x / ?y] ] => div_mod_to_equations_generalize x y
    | [ |- context[?x mod ?y] ] => div_mod_to_equations_generalize x y
    | [ H : context[?x / ?y] |- _ ] => div_mod_to_equations_generalize x y
    | [ H : context[?x mod ?y] |- _ ] => div_mod_to_equations_generalize x y
    end.
  Ltac quot_rem_to_equations_step :=
    match goal with
    | [ |- context[Z.quot ?x ?y] ] => quot_rem_to_equations_generalize x y
    | [ |- context[Z.rem ?x ?y] ] => quot_rem_to_equations_generalize x y
    | [ H : context[Z.quot ?x ?y] |- _ ] => quot_rem_to_equations_generalize x y
    | [ H : context[Z.rem ?x ?y] |- _ ] => quot_rem_to_equations_generalize x y
    end.
  Ltac div_mod_to_equations' := repeat div_mod_to_equations_step.
  Ltac quot_rem_to_equations' := repeat quot_rem_to_equations_step.
  Ltac euclidean_division_equations_cleanup :=
    repeat match goal with
           | [ H : ?x = ?x -> _ |- _ ] => specialize (H eq_refl)
           | [ H : ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?T -> _, H' : ?T |- _ ] => specialize (H H')
           | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
           | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
           | [ H : ?A -> ?x = ?x -> _ |- _ ] => specialize (fun a => H a eq_refl)
           | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
           | [ H : ?A -> ?B -> _, H' : ?B |- _ ] => specialize (fun a => H a H')
           | [ H : ?A -> ?B -> _, H' : ~?B |- _ ] => clear H
           | [ H : ?A -> ~?B -> _, H' : ?B |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x < 0 |- _ ] => clear H
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 < ?x |- _ ] => clear H
           | [ H : 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : ?A -> 0 < ?x -> _, H' : ?x <= 0 |- _ ] => clear H
           | [ H : ?A -> ?x < 0 -> _, H' : 0 <= ?x |- _ ] => clear H
           | [ H : 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?A -> 0 <= ?x -> _, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
           | [ H : ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
           | [ H : ?A -> ?x <= 0 -> _, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
           | [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
           | [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
           | [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
           end.
  Ltac div_mod_to_equations := div_mod_to_equations'; euclidean_division_equations_cleanup.
  Ltac quot_rem_to_equations := quot_rem_to_equations'; euclidean_division_equations_cleanup.
  Ltac to_euclidean_division_equations := div_mod_to_equations'; quot_rem_to_equations'; euclidean_division_equations_cleanup.
End Z.

Require Import ZifyClasses ZifyInst.
Require Zify.

Ltac Zify.zify_internal_to_euclidean_division_equations ::= Z.to_euclidean_division_equations.

Ltac zify := Zify.zify.

(* TODO #14736 for compatibility only, should be removed after deprecation *)
Require Import Max Min.
