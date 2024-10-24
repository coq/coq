(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
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
    [Z.euclidean_division_equations_find_duplicate_quotients] tactic
    poses facts of the form [q₁ = q₂ \/ q₁ <> q₂] for quotients that
    are likely to be the same, which allows tactics like [nia] to
    prove more goals, including those relating [Z.div]/[Z.mod] to
    [Z.quot]/[Z.rem].  The [Z.euclidean_division_equations_cleanup]
    tactic removes needless hypotheses, which makes tactics like [nia]
    run faster.  The tactic [Z.to_euclidean_division_equations]
    combines the handling of both variants of division/quotient and
    modulo/remainder. *)

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

  (* Make the direction of [Z.divide] line up with the rest of the Euclidean equation facts *)
  Local Lemma divide_alt x y : Z.divide x y -> exists z, y = x * z.
  Proof. intros [z H]; exists z; subst; apply Z.mul_comm. Qed.

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
  Ltac divide_to_equations_step :=
    match goal with | [ H : Z.divide _ _ |- _ ] => apply divide_alt in H; destruct H end.
  Ltac div_mod_to_equations' := repeat div_mod_to_equations_step.
  Ltac quot_rem_to_equations' := repeat quot_rem_to_equations_step.
  Ltac divide_to_equations' := repeat divide_to_equations_step.
  Ltac euclidean_division_equations_cleanup :=
    repeat
      (repeat match goal with
         | [ H : 0 <= ?x < _ |- _ ] => destruct H
         end;
       repeat match goal with
         | [ H : ?x <> ?x -> _ |- _ ] => clear H
         | [ H : ?x < ?x -> _ |- _ ] => clear H
         | [ H : ?T -> _, H' : ~?T |- _ ] => clear H
         | [ H : ~?T -> _, H' : ?T |- _ ] => clear H
         | [ H : ?A -> ?x <> ?x -> _ |- _ ] => clear H
         | [ H : ?A -> ?x < ?x -> _ |- _ ] => clear H
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
         | [ H : ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
         | [ H : ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
         | [ H : ?A -> ?x < ?y -> _, H' : ?x = ?y |- _ ] => clear H
         | [ H : ?A -> ?x < ?y -> _, H' : ?y = ?x |- _ ] => clear H
         | [ H : ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
         | [ H : ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
         | [ H : ?A -> ?x = ?y -> _, H' : ?x < ?y |- _ ] => clear H
         | [ H : ?A -> ?x = ?y -> _, H' : ?y < ?x |- _ ] => clear H
         end;
       repeat match goal with
         | [ H : ?x = ?x -> ?Q |- _ ] => specialize (H eq_refl)
         | [ H : ?T -> ?Q, H' : ?T |- _ ] => specialize (H H')
         | [ H : ?A -> ?x = ?x -> ?Q |- _ ] => specialize (fun a => H a eq_refl)
         | [ H : ?A -> ?B -> ?Q, H' : ?B |- _ ] => specialize (fun a => H a H')
         | [ H : 0 <= ?x -> ?Q, H' : ?x <= 0 |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x (eq_sym pf)))
         | [ H : ?A -> 0 <= ?x -> ?Q, H' : ?x <= 0 |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl 0 x (eq_sym pf)))
         | [ H : ?x <= 0 -> ?Q, H' : 0 <= ?x |- _ ] => specialize (fun pf => H (@Z.eq_le_incl 0 x pf))
         | [ H : ?A -> ?x <= 0 -> ?Q, H' : 0 <= ?x |- _ ] => specialize (fun a pf => H a (@Z.eq_le_incl x 0 pf))
         end).
  (** poses [x = y \/ x <> y] unless that is redundant or contradictory *)
  Ltac euclidean_division_equations_pose_eq_fact x y :=
    assert_fails constr_eq x y;
    lazymatch goal with
    | [ H : x = y |- _ ] => fail
    | [ H : y = x |- _ ] => fail
    | [ H : x = y \/ x <> y |- _ ] => fail
    | [ H : y = x \/ y <> x |- _ ] => fail
    | [ H : x < y |- _ ] => fail
    | [ H : y < x |- _ ] => fail
    | [ H : x <> y |- _ ] => fail
    | [ H : y <> x |- _ ] => fail
    | _ => pose proof (Z.eq_decidable x y : x = y \/ x <> y)
    end.

  Ltac euclidean_division_equations_find_duplicate_quotients_step :=
    let pose_eq_fact x y := euclidean_division_equations_pose_eq_fact x y in
    match goal with
    | [ H : context[?x = ?y * ?q1], H' : context[?x = ?y * ?q2] |- _ ] => pose_eq_fact q1 q2
    | [ H : context[?x = ?y * ?q1 + _], H' : context[?x = ?y * ?q2] |- _ ] => pose_eq_fact q1 q2
    | [ H : context[?x = ?y * ?q1 + _], H' : context[?x = ?y * ?q2 + _] |- _ ] => pose_eq_fact q1 q2
    | [ H : context[?y * ?q2 + _ = ?y * ?q1 + _] |- _ ] => pose_eq_fact q1 q2
    | [ H : context[?x * ?y = ?y * ?q1 + _] |- _ ] => pose_eq_fact x q1
    | [ H : context[?y * ?x = ?y * ?q1 + _] |- _ ] => pose_eq_fact x q1
    end.
  Ltac euclidean_division_equations_find_duplicate_quotients :=
    repeat euclidean_division_equations_find_duplicate_quotients_step.
  Ltac div_mod_to_equations := div_mod_to_equations'; euclidean_division_equations_cleanup.
  Ltac quot_rem_to_equations := quot_rem_to_equations'; euclidean_division_equations_cleanup.
  Ltac divide_to_equations := divide_to_equations'; euclidean_division_equations_cleanup.
  Module euclidean_division_equations_flags.
    #[local] Set Primitive Projections.
    Record t :=
      { find_duplicate_quotients : bool }.
    Ltac default_find_duplicate_quotients := constr:(true).
    Ltac default :=
      let find_duplicate_quotients_value := default_find_duplicate_quotients in
      constr:({| find_duplicate_quotients := find_duplicate_quotients_value
              |}).
    Module Import DefaultHelpers.
      Ltac try_unify_args x y :=
        tryif first [ has_evar x | has_evar y ]
        then (tryif unify x y
               then idtac
               else (lazymatch x with
                     | ?f ?x
                       => lazymatch y with
                          | ?g ?y
                            => try_unify_args f g; try_unify_args x y
                          | ?y => fail 0 "Z.euclidean_division_equations_flags: try_unify_args: cannot unify application" x "with non-application" y
                          end
                     | ?x
                       => (tryif has_evar x
                            then fail 0 "Z.euclidean_division_equations_flags: try_unify_args: cannot unify evar-containing non-application" x "with" y
                            else (tryif has_evar y
                                   then fail 0 "Z.euclidean_division_equations_flags: try_unify_args: cannot unify non-application" x "with evar-containing" y
                                   else fail 100 "Z.euclidean_division_equations_flags: try_unify_args: Impossible inconsistent state of has_evar in try_unify_args" x y))
                     end))
        else idtac.
    End DefaultHelpers.

    Ltac flags_with orig_flags proj value :=
      let flags := open_constr:(match True return t with _ => ltac:(econstructor) end) in
      let __unif := constr:(eq_refl : proj flags = value) in
      let __force := lazymatch goal with _ => try_unify_args flags orig_flags end in
      flags.

    Ltac default_with proj value := flags_with default proj value.

    Ltac guard_with proj flags tac :=
      lazymatch (eval cbv in (proj flags)) with
      | true => tac
      | false => idtac
      | ?v => let ctrue := constr:(true) in
              let cfalse := constr:(false) in
              fail 0 "Invalid flag value for" proj "in" flags "(got" v "expected" ctrue "or" cfalse ")"
      end.
  End euclidean_division_equations_flags.
  Import euclidean_division_equations_flags (find_duplicate_quotients).
  Ltac to_euclidean_division_equations_with flags :=
    divide_to_equations'; div_mod_to_equations'; quot_rem_to_equations';
    euclidean_division_equations_cleanup;
    euclidean_division_equations_flags.guard_with find_duplicate_quotients flags euclidean_division_equations_find_duplicate_quotients.
  Ltac to_euclidean_division_equations :=
    to_euclidean_division_equations_with euclidean_division_equations_flags.default.
End Z.

Require Import ZifyClasses ZifyInst.
Require Zify.

Ltac Zify.zify_internal_to_euclidean_division_equations ::= Z.to_euclidean_division_equations.

Ltac zify := Zify.zify.

(* TODO #14736 for compatibility only, should be removed after deprecation *)
