(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Arith Max Min BinInt BinNat Znat Nnat.

Local Open Scope Z_scope.


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

  (* atoms of type N : we add a positivity condition (if not already there) *)
  | _ : 0 <= Z.of_N ?a |- _ => hide_Z_of_N a
  | _ : context [ Z.of_N ?a ] |- _ => pose proof (N2Z.is_nonneg a); hide_Z_of_N a
  | |- context [ Z.of_N ?a ] => pose proof (N2Z.is_nonneg a); hide_Z_of_N a
 end.

Ltac zify_N := repeat zify_N_rel; repeat zify_N_op; unfold Z_of_N' in *.



(** The complete Z-ification tactic *)

Ltac zify := repeat (zify_nat; zify_positive; zify_N); zify_op.
