(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Arith Max Min BinInt BinNat Znat Nnat.

Local Open Scope Z_scope.

(** * [Z.div_mod_to_equations], [Z.quot_rem_to_equations], [Z.to_euclidean_division_equations]: the tactics for preprocessing [Z.div] and [Z.modulo], [Z.quot] and [Z.rem] *)

(** These tactic use the complete specification of [Z.div] and
    [Z.modulo] ([Z.quot] and [Z.rem], respectively) to remove these
    functions from the goal without losing information.  The
    [Z.euclidean_division_equations_cleanup] tactic removes needless
    hypotheses, which makes tactics like [nia] run faster.  The tactic
    [Z.to_euclidean_division_equations] combines the handling of both variants
    of division/quotient and modulo/remainder. *)

Module Z.
  Lemma mod_0_r_ext x y : y = 0 -> x mod y = 0.
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

(** * zify: the Z-ification tactic *)

(* This tactic searches for nat and N and positive elements in the goal and
   translates everything into Z. It is meant as a pre-processor for
   (r)omega; for instance a positivity hypothesis is added whenever
     - a multiplication is encountered
     - an atom is encountered (that is a variable or an unknown construct)

   Recognized relations (can be handled as deeply as allowed by setoid rewrite):
     - { eq, le, lt, ge, gt } on { Z, positive, N, nat }

   Recognized operations:
     - on Z: Z.min, Z.max, Z.abs, Z.sgn are translated in term of <= < =
     - on nat: + * - S O pred min max Pos.to_nat N.to_nat Z.abs_nat
     - on positive: Zneg Zpos xI xO xH + * - Pos.succ Pos.pred Pos.min Pos.max Pos.of_succ_nat
     - on N: N0 Npos + * - N.pred N.succ N.min N.max N.of_nat Z.abs_N
*)




(** I) translation of Z.max, Z.min, Z.abs, Z.sgn into recognized equations *)

Ltac zify_unop_core t thm a :=
 (* Let's introduce the specification theorem for t *)
 pose proof (thm a);
 (* Then we replace (t a) everywhere with a fresh variable *)
 let z := fresh "z" in set (z:=t a) in *; clearbody z.

Ltac zify_unop_var_or_term t thm a :=
 (* If a is a variable, no need for aliasing *)
 let za := fresh "z" in
 (rename a into za; rename za into a; zify_unop_core t thm a) ||
 (* Otherwise, a is a complex term: we alias it. *)
 (remember a as za; zify_unop_core t thm za).

Ltac zify_unop t thm a :=
 (* If a is a scalar, we can simply reduce the unop. *)
 (* Note that simpl wasn't enough to reduce [Z.max 0 0] (#5439) *)
 let isz := isZcst a in
 match isz with
  | true =>
    let u := eval compute in (t a) in
    change (t a) with u in *
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_unop_nored t thm a :=
 (* in this version, we don't try to reduce the unop (that can be (Z.add x)) *)
 let isz := isZcst a in
 match isz with
  | true => zify_unop_core t thm a
  | _ => zify_unop_var_or_term t thm a
 end.

Ltac zify_binop t thm a b:=
 (* works as zify_unop, except that we should be careful when
    dealing with b, since it can be equal to a *)
 let isza := isZcst a in
 match isza with
   | true => zify_unop (t a) (thm a) b
   | _ =>
       let za := fresh "z" in
       (rename a into za; rename za into a; zify_unop_nored (t a) (thm a) b) ||
       (remember a as za; match goal with
         | H : za = b |- _ => zify_unop_nored (t za) (thm za) za
         | _ => zify_unop_nored (t za) (thm za) b
        end)
 end.

Ltac zify_op_1 :=
  match goal with
   | x := ?t : Z |- _ => let h := fresh "heq_" x in pose proof (eq_refl : x = t) as h; clearbody x
   | |- context [ Z.max ?a ?b ] => zify_binop Z.max Z.max_spec a b
   | H : context [ Z.max ?a ?b ] |- _ => zify_binop Z.max Z.max_spec a b
   | |- context [ Z.min ?a ?b ] => zify_binop Z.min Z.min_spec a b
   | H : context [ Z.min ?a ?b ] |- _ => zify_binop Z.min Z.min_spec a b
   | |- context [ Z.sgn ?a ] => zify_unop Z.sgn Z.sgn_spec a
   | H : context [ Z.sgn ?a ] |- _ => zify_unop Z.sgn Z.sgn_spec a
   | |- context [ Z.abs ?a ] => zify_unop Z.abs Z.abs_spec a
   | H : context [ Z.abs ?a ] |- _ => zify_unop Z.abs Z.abs_spec a
  end.

Ltac zify_op := repeat zify_op_1.





(** II) Conversion from nat to Z *)


Definition Z_of_nat' := Z.of_nat.

Ltac hide_Z_of_nat t :=
  let z := fresh "z" in set (z:=Z.of_nat t) in *;
  change Z.of_nat with Z_of_nat' in z;
  unfold z in *; clear z.

Ltac zify_nat_rel :=
 match goal with
  (* I: equalities *)
  | x := ?t : nat |- _ => let h := fresh "heq_" x in pose proof (eq_refl : x = t) as h; clearbody x
  | |- (@eq nat ?a ?b) => apply (Nat2Z.inj a b) (* shortcut *)
  | H : context [ @eq nat ?a ?b ] |- _ => rewrite <- (Nat2Z.inj_iff a b) in H
  | |- context [ @eq nat ?a ?b ] =>       rewrite <- (Nat2Z.inj_iff a b)
  (* II: less than *)
  | H : context [ lt ?a ?b ] |- _ => rewrite (Nat2Z.inj_lt a b) in H
  | |- context [ lt ?a ?b ] =>       rewrite (Nat2Z.inj_lt a b)
  (* III: less or equal *)
  | H : context [ le ?a ?b ] |- _ => rewrite (Nat2Z.inj_le a b) in H
  | |- context [ le ?a ?b ] =>       rewrite (Nat2Z.inj_le a b)
  (* IV: greater than *)
  | H : context [ gt ?a ?b ] |- _ => rewrite (Nat2Z.inj_gt a b) in H
  | |- context [ gt ?a ?b ] =>       rewrite (Nat2Z.inj_gt a b)
  (* V: greater or equal *)
  | H : context [ ge ?a ?b ] |- _ => rewrite (Nat2Z.inj_ge a b) in H
  | |- context [ ge ?a ?b ] =>       rewrite (Nat2Z.inj_ge a b)
 end.

Ltac zify_nat_op :=
 match goal with
  (* misc type conversions: positive/N/Z to nat *)
  | H : context [ Z.of_nat (Pos.to_nat ?a) ] |- _ => rewrite (positive_nat_Z a) in H
  | |- context [ Z.of_nat (Pos.to_nat ?a) ] => rewrite (positive_nat_Z a)
  | H : context [ Z.of_nat (N.to_nat ?a) ] |- _ => rewrite (N_nat_Z a) in H
  | |- context [ Z.of_nat (N.to_nat ?a) ] => rewrite (N_nat_Z a)
  | H : context [ Z.of_nat (Z.abs_nat ?a) ] |- _ => rewrite (Zabs2Nat.id_abs a) in H
  | |- context [ Z.of_nat (Z.abs_nat ?a) ] => rewrite (Zabs2Nat.id_abs a)

  (* plus -> Z.add *)
  | H : context [ Z.of_nat (plus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_add a b) in H
  | |- context [ Z.of_nat (plus ?a ?b) ] => rewrite (Nat2Z.inj_add a b)

  (* min -> Z.min *)
  | H : context [ Z.of_nat (min ?a ?b) ] |- _ => rewrite (Nat2Z.inj_min a b) in H
  | |- context [ Z.of_nat (min ?a ?b) ] => rewrite (Nat2Z.inj_min a b)

  (* max -> Z.max *)
  | H : context [ Z.of_nat (max ?a ?b) ] |- _ => rewrite (Nat2Z.inj_max a b) in H
  | |- context [ Z.of_nat (max ?a ?b) ] => rewrite (Nat2Z.inj_max a b)

  (* minus -> Z.max (Z.sub ... ...) 0 *)
  | H : context [ Z.of_nat (minus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_sub_max a b) in H
  | |- context [ Z.of_nat (minus ?a ?b) ] => rewrite (Nat2Z.inj_sub_max a b)

  (* pred -> minus ... -1 -> Z.max (Z.sub ... -1) 0 *)
  | H : context [ Z.of_nat (pred ?a) ] |- _ => rewrite (pred_of_minus a) in H
  | |- context [ Z.of_nat (pred ?a) ] => rewrite (pred_of_minus a)

  (* mult -> Z.mul and a positivity hypothesis *)
  | H : context [ Z.of_nat (mult ?a ?b) ] |- _ =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *
  | |- context [ Z.of_nat (mult ?a ?b) ] =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *

  (* O -> Z0 *)
  | H : context [ Z.of_nat O ] |- _ => change (Z.of_nat O) with Z0 in H
  | |- context [ Z.of_nat O ] => change (Z.of_nat O) with Z0

  (* S -> number or Z.succ *)
  | H : context [ Z.of_nat (S ?a) ] |- _ =>
     let isnat := isnatcst a in
     match isnat with
      | true =>
        let t := eval compute in (Z.of_nat (S a)) in
        change (Z.of_nat (S a)) with t in H
      | _ => rewrite (Nat2Z.inj_succ a) in H
      | _ => (* if the [rewrite] fails (most likely a dependent occurrence of [Z.of_nat (S a)]),
                hide [Z.of_nat (S a)] in this one hypothesis *)
        change (Z.of_nat (S a)) with (Z_of_nat' (S a)) in H
     end
  | |- context [ Z.of_nat (S ?a) ] =>
     let isnat := isnatcst a in
     match isnat with
      | true =>
        let t := eval compute in (Z.of_nat (S a)) in
        change (Z.of_nat (S a)) with t
      | _ => rewrite (Nat2Z.inj_succ a)
      | _ => (* if the [rewrite] fails (most likely a dependent occurrence of [Z.of_nat (S a)]),
                hide [Z.of_nat (S a)] in the goal *)
        change (Z.of_nat (S a)) with (Z_of_nat' (S a))
     end

  (* atoms of type nat : we add a positivity condition (if not already there) *)
  | _ : 0 <= Z.of_nat ?a |- _ => hide_Z_of_nat a
  | _ : context [ Z.of_nat ?a ] |- _ =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
  | |- context [ Z.of_nat ?a ] =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
 end.

Ltac zify_nat := repeat zify_nat_rel; repeat zify_nat_op; unfold Z_of_nat' in *.




(* III) conversion from positive to Z *)

Definition Zpos' := Zpos.
Definition Zneg' := Zneg.

Ltac hide_Zpos t :=
  let z := fresh "z" in set (z:=Zpos t) in *;
  change Zpos with Zpos' in z;
  unfold z in *; clear z.

Ltac zify_positive_rel :=
 match goal with
  (* I: equalities *)
  | x := ?t : positive |- _ => let h := fresh "heq_" x in pose proof (eq_refl : x = t) as h; clearbody x
  | |- (@eq positive ?a ?b) => apply Pos2Z.inj
  | H : context [ @eq positive ?a ?b ] |- _ => rewrite <- (Pos2Z.inj_iff a b) in H
  | |- context [ @eq positive ?a ?b ] =>       rewrite <- (Pos2Z.inj_iff a b)
  (* II: less than *)
  | H : context [ (?a < ?b)%positive ] |- _ => change (a<b)%positive with (Zpos a<Zpos b) in H
  | |- context [ (?a < ?b)%positive ] => change (a<b)%positive with (Zpos a<Zpos b)
  (* III: less or equal *)
  | H : context [ (?a <= ?b)%positive ] |- _ => change (a<=b)%positive with (Zpos a<=Zpos b) in H
  | |- context [ (?a <= ?b)%positive ] => change (a<=b)%positive with (Zpos a<=Zpos b)
  (* IV: greater than *)
  | H : context [ (?a > ?b)%positive ] |- _ => change (a>b)%positive with (Zpos a>Zpos b) in H
  | |- context [ (?a > ?b)%positive ] => change (a>b)%positive with (Zpos a>Zpos b)
  (* V: greater or equal *)
  | H : context [ (?a >= ?b)%positive ] |- _ => change (a>=b)%positive with (Zpos a>=Zpos b) in H
  | |- context [ (?a >= ?b)%positive ] => change (a>=b)%positive with (Zpos a>=Zpos b)
 end.

Ltac zify_positive_op :=
 match goal with
 (* Z.pow_pos -> Z.pow *)
 | H : context [ Z.pow_pos ?a ?b ] |- _ => change (Z.pow_pos a b) with (Z.pow a (Z.pos b)) in H
 | |- context [ Z.pow_pos ?a ?b ]  => change (Z.pow_pos a b) with (Z.pow a (Z.pos b))
 (* Zneg -> -Zpos (except for numbers) *)
  | H : context [ Zneg ?a ] |- _ =>
     let isp := isPcst a in
     match isp with
      | true => change (Zneg a) with (Zneg' a) in H
      | _ => change (Zneg a) with (- Zpos a) in H
     end
  | |- context [ Zneg ?a ] =>
     let isp := isPcst a in
     match isp with
      | true => change (Zneg a) with (Zneg' a)
      | _ => change (Zneg a) with (- Zpos a)
     end

  (* misc type conversions: nat to positive *)
  | H : context [ Zpos (Pos.of_succ_nat ?a) ] |- _ => rewrite (Zpos_P_of_succ_nat a) in H
  | |- context [ Zpos (Pos.of_succ_nat ?a) ] => rewrite (Zpos_P_of_succ_nat a)

  (* Z.power_pos *)
  | H : context [ Zpos (Pos.of_succ_nat ?a) ] |- _ => rewrite (Zpos_P_of_succ_nat a) in H
  | |- context [ Zpos (Pos.of_succ_nat ?a) ] => rewrite (Zpos_P_of_succ_nat a)

  (* Pos.add -> Z.add *)
  | H : context [ Zpos (?a + ?b) ] |- _ => change (Zpos (a+b)) with (Zpos a + Zpos b) in H
  | |- context [ Zpos (?a + ?b) ] => change (Zpos (a+b)) with (Zpos a + Zpos b)

  (* Pos.min -> Z.min *)
  | H : context [ Zpos (Pos.min ?a ?b) ] |- _ => rewrite (Pos2Z.inj_min a b) in H
  | |- context [ Zpos (Pos.min ?a ?b) ] => rewrite (Pos2Z.inj_min a b)

  (* Pos.max -> Z.max *)
  | H : context [ Zpos (Pos.max ?a ?b) ] |- _ => rewrite (Pos2Z.inj_max a b) in H
  | |- context [ Zpos (Pos.max ?a ?b) ] => rewrite (Pos2Z.inj_max a b)

  (* Pos.sub -> Z.max 1 (Z.sub ... ...) *)
  | H : context [ Zpos (Pos.sub ?a ?b) ] |- _ => rewrite (Pos2Z.inj_sub_max a b) in H
  | |- context [ Zpos (Pos.sub ?a ?b) ] => rewrite (Pos2Z.inj_sub_max a b)

  (* Pos.succ -> Z.succ *)
  | H : context [ Zpos (Pos.succ ?a) ] |- _ => rewrite (Pos2Z.inj_succ a) in H
  | |- context [ Zpos (Pos.succ ?a) ] => rewrite (Pos2Z.inj_succ a)

  (* Pos.pred -> Pos.sub ... -1 -> Z.max 1 (Z.sub ... - 1) *)
  | H : context [ Zpos (Pos.pred ?a) ] |- _ => rewrite <- (Pos.sub_1_r a) in H
  | |- context [ Zpos (Pos.pred ?a) ] => rewrite <- (Pos.sub_1_r a)

  (* Pos.mul -> Z.mul and a positivity hypothesis *)
  | H : context [ Zpos (?a * ?b) ] |- _ =>
        pose proof (Pos2Z.is_pos (Pos.mul a b));
        change (Zpos (a*b)) with (Zpos a * Zpos b) in *
  | |- context [ Zpos (?a * ?b) ] =>
        pose proof (Pos2Z.is_pos (Pos.mul a b));
        change (Zpos (a*b)) with (Zpos a * Zpos b) in *

  (* xO *)
  | H : context [ Zpos (xO ?a) ] |- _ =>
     let isp := isPcst a in
     match isp with
      | true => change (Zpos (xO a)) with (Zpos' (xO a)) in H
      | _ => rewrite (Pos2Z.inj_xO a) in H
     end
  | |- context [ Zpos (xO ?a) ] =>
     let isp := isPcst a in
     match isp with
      | true => change (Zpos (xO a)) with (Zpos' (xO a))
      | _ => rewrite (Pos2Z.inj_xO a)
     end
  (* xI *)
  | H : context [ Zpos (xI ?a) ] |- _ =>
     let isp := isPcst a in
     match isp with
      | true => change (Zpos (xI a)) with (Zpos' (xI a)) in H
      | _ => rewrite (Pos2Z.inj_xI a) in H
     end
  | |- context [ Zpos (xI ?a) ] =>
     let isp := isPcst a in
     match isp with
      | true => change (Zpos (xI a)) with (Zpos' (xI a))
      | _ => rewrite (Pos2Z.inj_xI a)
     end

  (* xI : nothing to do, just prevent adding a useless positivity condition *)
  | H : context [ Zpos xH ] |- _ => hide_Zpos xH
  | |- context [ Zpos xH ] => hide_Zpos xH

  (* atoms of type positive : we add a positivity condition (if not already there) *)
  | _ : 0 < Zpos ?a |- _ => hide_Zpos a
  | _ : context [ Zpos ?a ] |- _ => pose proof (Pos2Z.is_pos a); hide_Zpos a
  | |- context [ Zpos ?a ] => pose proof (Pos2Z.is_pos a); hide_Zpos a
 end.

Ltac zify_positive :=
 repeat zify_positive_rel; repeat zify_positive_op; unfold Zpos',Zneg' in *.





(* IV) conversion from N to Z *)

Definition Z_of_N' := Z.of_N.

Ltac hide_Z_of_N t :=
  let z := fresh "z" in set (z:=Z.of_N t) in *;
  change Z.of_N with Z_of_N' in z;
  unfold z in *; clear z.

Ltac zify_N_rel :=
 match goal with
  (* I: equalities *)
  | x := ?t : N |- _ => let h := fresh "heq_" x in pose proof (eq_refl : x = t) as h; clearbody x
  | |- (@eq N ?a ?b) => apply (N2Z.inj a b) (* shortcut *)
  | H : context [ @eq N ?a ?b ] |- _ => rewrite <- (N2Z.inj_iff a b) in H
  | |- context [ @eq N ?a ?b ] =>       rewrite <- (N2Z.inj_iff a b)
  (* II: less than *)
  | H : context [ (?a < ?b)%N ] |- _ => rewrite (N2Z.inj_lt a b) in H
  | |- context [ (?a < ?b)%N ] =>       rewrite (N2Z.inj_lt a b)
  (* III: less or equal *)
  | H : context [ (?a <= ?b)%N ] |- _ => rewrite (N2Z.inj_le a b) in H
  | |- context [ (?a <= ?b)%N ] =>       rewrite (N2Z.inj_le a b)
  (* IV: greater than *)
  | H : context [ (?a > ?b)%N ] |- _ => rewrite (N2Z.inj_gt a b) in H
  | |- context [ (?a > ?b)%N ] =>       rewrite (N2Z.inj_gt a b)
  (* V: greater or equal *)
  | H : context [ (?a >= ?b)%N ] |- _ => rewrite (N2Z.inj_ge a b) in H
  | |- context [ (?a >= ?b)%N ] =>       rewrite (N2Z.inj_ge a b)
 end.

Ltac zify_N_op :=
 match goal with
  (* misc type conversions: nat to positive *)
  | H : context [ Z.of_N (N.of_nat ?a) ] |- _ => rewrite (nat_N_Z a) in H
  | |- context [ Z.of_N (N.of_nat ?a) ] => rewrite (nat_N_Z a)
  | H : context [ Z.of_N (Z.abs_N ?a) ] |- _ => rewrite (N2Z.inj_abs_N a) in H
  | |- context [ Z.of_N (Z.abs_N ?a) ] => rewrite (N2Z.inj_abs_N a)
  | H : context [ Z.of_N (Npos ?a) ] |- _ => rewrite (N2Z.inj_pos a) in H
  | |- context [ Z.of_N (Npos ?a) ] => rewrite (N2Z.inj_pos a)
  | H : context [ Z.of_N N0 ] |- _ => change (Z.of_N N0) with Z0 in H
  | |- context [ Z.of_N N0 ] => change (Z.of_N N0) with Z0

  (* N.add -> Z.add *)
  | H : context [ Z.of_N (N.add ?a ?b) ] |- _ => rewrite (N2Z.inj_add a b) in H
  | |- context [ Z.of_N (N.add ?a ?b) ] => rewrite (N2Z.inj_add a b)

  (* N.min -> Z.min *)
  | H : context [ Z.of_N (N.min ?a ?b) ] |- _ => rewrite (N2Z.inj_min a b) in H
  | |- context [ Z.of_N (N.min ?a ?b) ] => rewrite (N2Z.inj_min a b)

  (* N.max -> Z.max *)
  | H : context [ Z.of_N (N.max ?a ?b) ] |- _ => rewrite (N2Z.inj_max a b) in H
  | |- context [ Z.of_N (N.max ?a ?b) ] => rewrite (N2Z.inj_max a b)

  (* N.sub -> Z.max 0 (Z.sub ... ...) *)
  | H : context [ Z.of_N (N.sub ?a ?b) ] |- _ => rewrite (N2Z.inj_sub_max a b) in H
  | |- context [ Z.of_N (N.sub ?a ?b) ] => rewrite (N2Z.inj_sub_max a b)

  (* pred -> minus ... -1 -> Z.max (Z.sub ... -1) 0 *)
  | H : context [ Z.of_N (N.pred ?a) ] |- _ => rewrite (N.pred_sub a) in H
  | |- context [ Z.of_N (N.pred ?a) ] => rewrite (N.pred_sub a)

  (* N.succ -> Z.succ *)
  | H : context [ Z.of_N (N.succ ?a) ] |- _ => rewrite (N2Z.inj_succ a) in H
  | |- context [ Z.of_N (N.succ ?a) ] => rewrite (N2Z.inj_succ a)

  (* N.mul -> Z.mul and a positivity hypothesis *)
  | H : context [ Z.of_N (N.mul ?a ?b) ] |- _ =>
        pose proof (N2Z.is_nonneg (N.mul a b)); rewrite (N2Z.inj_mul a b) in *
  | |- context [ Z.of_N  (N.mul ?a ?b) ] =>
        pose proof (N2Z.is_nonneg (N.mul a b)); rewrite (N2Z.inj_mul a b) in *

  (* N.div -> Z.div and a positivity hypothesis *)
  | H : context [ Z.of_N (N.div ?a ?b) ] |- _ =>
        pose proof (N2Z.is_nonneg (N.div a b)); rewrite (N2Z.inj_div a b) in *
  | |- context [ Z.of_N  (N.div ?a ?b) ] =>
        pose proof (N2Z.is_nonneg (N.div a b)); rewrite (N2Z.inj_div a b) in *

  (* N.modulo -> Z.rem / Z.modulo and a positivity hypothesis (N.modulo agrees with Z.modulo on everything except 0; so we pose both the non-zero proof for this agreement, but also replace things with [Z.rem]) *)
  | H : context [ Z.of_N (N.modulo ?a ?b) ] |- _ =>
    pose proof (N2Z.is_nonneg (N.modulo a b));
    pose proof (@Z.quot_div_nonneg (Z.of_N a) (Z.of_N b) (N2Z.is_nonneg a));
    pose proof (@Z.rem_mod_nonneg (Z.of_N a) (Z.of_N b) (N2Z.is_nonneg a));
    rewrite (N2Z.inj_rem a b) in *
  | |- context [ Z.of_N  (N.div ?a ?b) ] =>
    pose proof (N2Z.is_nonneg (N.modulo a b));
    pose proof (@Z.quot_div_nonneg (Z.of_N a) (Z.of_N b) (N2Z.is_nonneg a));
    pose proof (@Z.rem_mod_nonneg (Z.of_N a) (Z.of_N b) (N2Z.is_nonneg a));
    rewrite (N2Z.inj_rem a b) in *

  (* atoms of type N : we add a positivity condition (if not already there) *)
  | _ : 0 <= Z.of_N ?a |- _ => hide_Z_of_N a
  | _ : context [ Z.of_N ?a ] |- _ => pose proof (N2Z.is_nonneg a); hide_Z_of_N a
  | |- context [ Z.of_N ?a ] => pose proof (N2Z.is_nonneg a); hide_Z_of_N a
 end.

Ltac zify_N := repeat zify_N_rel; repeat zify_N_op; unfold Z_of_N' in *.



(** The complete Z-ification tactic *)

Ltac zify := repeat (zify_nat; zify_positive; zify_N); zify_op.
