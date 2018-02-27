(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import Rbase.
Require Import Rfunctions.
Require Import Rtrigo1.
Require Import SeqSeries.
Require Export Ranalysis1.
Require Export Ranalysis2.
Require Export Ranalysis3.
Require Export Rtopology.
Require Export MVT.
Require Export PSeries_reg.
Require Export Exp_prop.
Require Export Rtrigo_reg.
Require Export Rsqrt_def.
Require Export R_sqrt.
Require Export Rtrigo_calc.
Require Export Rgeom.
Require Export RList.
Require Export Sqrt_reg.
Require Export Ranalysis4.
Require Export Rpower.
Local Open Scope R_scope.

Definition AppVar : R.
Proof.
exact R0.
Qed.

(**********)
Ltac intro_hyp_glob trm :=
  match constr:(trm) with
    | (?X1 + ?X2)%F =>
      match goal with
        |  |- (derivable _) => intro_hyp_glob X1; intro_hyp_glob X2
        |  |- (continuity _) => intro_hyp_glob X1; intro_hyp_glob X2
        | _ => idtac
      end
    | (?X1 - ?X2)%F =>
      match goal with
        |  |- (derivable _) => intro_hyp_glob X1; intro_hyp_glob X2
        |  |- (continuity _) => intro_hyp_glob X1; intro_hyp_glob X2
        | _ => idtac
      end
    | (?X1 * ?X2)%F =>
      match goal with
        |  |- (derivable _) => intro_hyp_glob X1; intro_hyp_glob X2
        |  |- (continuity _) => intro_hyp_glob X1; intro_hyp_glob X2
        | _ => idtac
      end
    | (?X1 / ?X2)%F =>
      let aux := constr:(X2) in
        match goal with
          | _:(forall x0:R, aux x0 <> 0) |- (derivable _) =>
            intro_hyp_glob X1; intro_hyp_glob X2
          | _:(forall x0:R, aux x0 <> 0) |- (continuity _) =>
            intro_hyp_glob X1; intro_hyp_glob X2
          |  |- (derivable _) =>
            cut (forall x0:R, aux x0 <> 0);
              [ intro; intro_hyp_glob X1; intro_hyp_glob X2 | try assumption ]
          |  |- (continuity _) =>
            cut (forall x0:R, aux x0 <> 0);
              [ intro; intro_hyp_glob X1; intro_hyp_glob X2 | try assumption ]
          | _ => idtac
        end
    | (comp ?X1 ?X2) =>
      match goal with
        |  |- (derivable _) => intro_hyp_glob X1; intro_hyp_glob X2
        |  |- (continuity _) => intro_hyp_glob X1; intro_hyp_glob X2
        | _ => idtac
      end
    | (- ?X1)%F =>
      match goal with
        |  |- (derivable _) => intro_hyp_glob X1
        |  |- (continuity _) => intro_hyp_glob X1
        | _ => idtac
      end
    | (/ ?X1)%F =>
      let aux := constr:(X1) in
        match goal with
          | _:(forall x0:R, aux x0 <> 0) |- (derivable _) =>
            intro_hyp_glob X1
          | _:(forall x0:R, aux x0 <> 0) |- (continuity _) =>
            intro_hyp_glob X1
          |  |- (derivable _) =>
            cut (forall x0:R, aux x0 <> 0);
              [ intro; intro_hyp_glob X1 | try assumption ]
          |  |- (continuity _) =>
            cut (forall x0:R, aux x0 <> 0);
              [ intro; intro_hyp_glob X1 | try assumption ]
          | _ => idtac
        end
    | cos => idtac
    | sin => idtac
    | cosh => idtac
    | sinh => idtac
    | exp => idtac
    | Rsqr => idtac
    | sqrt => idtac
    | id => idtac
    | (fct_cte _) => idtac
    | (pow_fct _) => idtac
    | Rabs => idtac
    | ?X1 =>
      let p := constr:(X1) in
      let HYPPD := fresh "HYPPD" in
        match goal with
          | _:(derivable p) |- _ => idtac
          |  |- (derivable p) => idtac
          |  |- (derivable _) =>
            cut (True -> derivable p);
              [ intro HYPPD; cut (derivable p);
                [ intro; clear HYPPD | apply HYPPD; clear HYPPD; trivial ]
                | idtac ]
          | _:(continuity p) |- _ => idtac
          |  |- (continuity p) => idtac
          |  |- (continuity _) =>
            cut (True -> continuity p);
              [ intro HYPPD; cut (continuity p);
                [ intro; clear HYPPD | apply HYPPD; clear HYPPD; trivial ]
                | idtac ]
          | _ => idtac
        end
  end.

(**********)
Ltac intro_hyp_pt trm pt :=
  match constr:(trm) with
    | (?X1 + ?X2)%F =>
      match goal with
        |  |- (derivable_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (continuity_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (derive_pt _ _ _ = _) =>
          intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        | _ => idtac
      end
    | (?X1 - ?X2)%F =>
      match goal with
        |  |- (derivable_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (continuity_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (derive_pt _ _ _ = _) =>
          intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        | _ => idtac
      end
    | (?X1 * ?X2)%F =>
      match goal with
        |  |- (derivable_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (continuity_pt _ _) => intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        |  |- (derive_pt _ _ _ = _) =>
          intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
        | _ => idtac
      end
    | (?X1 / ?X2)%F =>
      let aux := constr:(X2) in
        match goal with
          | _:(aux pt <> 0) |- (derivable_pt _ _) =>
            intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          | _:(aux pt <> 0) |- (continuity_pt _ _) =>
            intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          | _:(aux pt <> 0) |- (derive_pt _ _ _ = _) =>
            intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          | id:(forall x0:R, aux x0 <> 0) |- (derivable_pt _ _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          | id:(forall x0:R, aux x0 <> 0) |- (continuity_pt _ _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          | id:(forall x0:R, aux x0 <> 0) |- (derive_pt _ _ _ = _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt
          |  |- (derivable_pt _ _) =>
            cut (aux pt <> 0);
              [ intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt | try assumption ]
          |  |- (continuity_pt _ _) =>
            cut (aux pt <> 0);
              [ intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt | try assumption ]
          |  |- (derive_pt _ _ _ = _) =>
            cut (aux pt <> 0);
              [ intro; intro_hyp_pt X1 pt; intro_hyp_pt X2 pt | try assumption ]
          | _ => idtac
        end
    | (comp ?X1 ?X2) =>
      match goal with
        |  |- (derivable_pt _ _) =>
          let pt_f1 := eval cbv beta in (X2 pt) in
            (intro_hyp_pt X1 pt_f1; intro_hyp_pt X2 pt)
        |  |- (continuity_pt _ _) =>
          let pt_f1 := eval cbv beta in (X2 pt) in
            (intro_hyp_pt X1 pt_f1; intro_hyp_pt X2 pt)
        |  |- (derive_pt _ _ _ = _) =>
          let pt_f1 := eval cbv beta in (X2 pt) in
            (intro_hyp_pt X1 pt_f1; intro_hyp_pt X2 pt)
        | _ => idtac
      end
    | (- ?X1)%F =>
      match goal with
        |  |- (derivable_pt _ _) => intro_hyp_pt X1 pt
        |  |- (continuity_pt _ _) => intro_hyp_pt X1 pt
        |  |- (derive_pt _ _ _ = _) => intro_hyp_pt X1 pt
        | _ => idtac
      end
    | (/ ?X1)%F =>
      let aux := constr:(X1) in
        match goal with
          | _:(aux pt <> 0) |- (derivable_pt _ _) =>
            intro_hyp_pt X1 pt
          | _:(aux pt <> 0) |- (continuity_pt _ _) =>
            intro_hyp_pt X1 pt
          | _:(aux pt <> 0) |- (derive_pt _ _ _ = _) =>
            intro_hyp_pt X1 pt
          | id:(forall x0:R, aux x0 <> 0) |- (derivable_pt _ _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt
          | id:(forall x0:R, aux x0 <> 0) |- (continuity_pt _ _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt
          | id:(forall x0:R, aux x0 <> 0) |- (derive_pt _ _ _ = _) =>
            generalize (id pt); intro; intro_hyp_pt X1 pt
          |  |- (derivable_pt _ _) =>
            cut (aux pt <> 0); [ intro; intro_hyp_pt X1 pt | try assumption ]
          |  |- (continuity_pt _ _) =>
            cut (aux pt <> 0); [ intro; intro_hyp_pt X1 pt | try assumption ]
          |  |- (derive_pt _ _ _ = _) =>
            cut (aux pt <> 0); [ intro; intro_hyp_pt X1 pt | try assumption ]
          | _ => idtac
        end
    | cos => idtac
    | sin => idtac
    | cosh => idtac
    | sinh => idtac
    | exp => idtac
    | Rsqr => idtac
    | id => idtac
    | (fct_cte _) => idtac
    | (pow_fct _) => idtac
    | sqrt =>
      match goal with
        |  |- (derivable_pt _ _) => cut (0 < pt); [ intro | try assumption ]
        |  |- (continuity_pt _ _) =>
          cut (0 <= pt); [ intro | try assumption ]
        |  |- (derive_pt _ _ _ = _) =>
          cut (0 < pt); [ intro | try assumption ]
        | _ => idtac
      end
    | Rabs =>
      match goal with
        |  |- (derivable_pt _ _) =>
          cut (pt <> 0); [ intro | try assumption ]
        | _ => idtac
      end
    | ?X1 =>
      let p := constr:(X1) in
      let HYPPD := fresh "HYPPD" in
        match goal with
          | _:(derivable_pt p pt) |- _ => idtac
          |  |- (derivable_pt p pt) => idtac
          |  |- (derivable_pt _ _) =>
            cut (True -> derivable_pt p pt);
              [ intro HYPPD; cut (derivable_pt p pt);
                [ intro; clear HYPPD | apply HYPPD; clear HYPPD; trivial ]
                | idtac ]
          | _:(continuity_pt p pt) |- _ => idtac
          |  |- (continuity_pt p pt) => idtac
          |  |- (continuity_pt _ _) =>
            cut (True -> continuity_pt p pt);
              [ intro HYPPD; cut (continuity_pt p pt);
                [ intro; clear HYPPD | apply HYPPD; clear HYPPD; trivial ]
                | idtac ]
          |  |- (derive_pt _ _ _ = _) =>
            cut (True -> derivable_pt p pt);
              [ intro HYPPD; cut (derivable_pt p pt);
                [ intro; clear HYPPD | apply HYPPD; clear HYPPD; trivial ]
                | idtac ]
          | _ => idtac
        end
  end.

(**********)
Ltac is_diff_pt :=
  match goal with
    |  |- (derivable_pt Rsqr _) =>

  (* fonctions de base *)
      apply derivable_pt_Rsqr
    |  |- (derivable_pt id ?X1) => apply (derivable_pt_id X1)
    |  |- (derivable_pt (fct_cte _) _) => apply derivable_pt_const
    |  |- (derivable_pt sin _) => apply derivable_pt_sin
    |  |- (derivable_pt cos _) => apply derivable_pt_cos
    |  |- (derivable_pt sinh _) => apply derivable_pt_sinh
    |  |- (derivable_pt cosh _) => apply derivable_pt_cosh
    |  |- (derivable_pt exp _) => apply derivable_pt_exp
    |  |- (derivable_pt (pow_fct _) _) =>
      unfold pow_fct in |- *; apply derivable_pt_pow
    |  |- (derivable_pt sqrt ?X1) =>
      apply (derivable_pt_sqrt X1);
        assumption ||
          unfold plus_fct, minus_fct, opp_fct, mult_fct, div_fct, inv_fct,
            comp, id, fct_cte, pow_fct in |- *
    |  |- (derivable_pt Rabs ?X1) =>
      apply (Rderivable_pt_abs X1);
        assumption ||
          unfold plus_fct, minus_fct, opp_fct, mult_fct, div_fct, inv_fct,
            comp, id, fct_cte, pow_fct in |- *
        (* regles de differentiabilite *)
        (* PLUS *)
    |  |- (derivable_pt (?X1 + ?X2) ?X3) =>
      apply (derivable_pt_plus X1 X2 X3); is_diff_pt
       (* MOINS *)
    |  |- (derivable_pt (?X1 - ?X2) ?X3) =>
      apply (derivable_pt_minus X1 X2 X3); is_diff_pt
       (* OPPOSE *)
    |  |- (derivable_pt (- ?X1) ?X2) =>
      apply (derivable_pt_opp X1 X2);
        is_diff_pt
       (* MULTIPLICATION PAR UN SCALAIRE *)
    |  |- (derivable_pt (mult_real_fct ?X1 ?X2) ?X3) =>
      apply (derivable_pt_scal X2 X1 X3); is_diff_pt
       (* MULTIPLICATION *)
    |  |- (derivable_pt (?X1 * ?X2) ?X3) =>
      apply (derivable_pt_mult X1 X2 X3); is_diff_pt
       (* DIVISION *)
    |  |- (derivable_pt (?X1 / ?X2) ?X3) =>
      apply (derivable_pt_div X1 X2 X3);
        [ is_diff_pt
          | is_diff_pt
          | try
            assumption ||
              unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
                comp, pow_fct, id, fct_cte in |- * ]
    |  |- (derivable_pt (/ ?X1) ?X2) =>

       (* INVERSION *)
      apply (derivable_pt_inv X1 X2);
        [ assumption ||
          unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
            comp, pow_fct, id, fct_cte in |- *
          | is_diff_pt ]
    |  |- (derivable_pt (comp ?X1 ?X2) ?X3) =>

       (* COMPOSITION *)
      apply (derivable_pt_comp X2 X1 X3); is_diff_pt
    | _:(derivable_pt ?X1 ?X2) |- (derivable_pt ?X1 ?X2) =>
      assumption
    | _:(derivable ?X1) |- (derivable_pt ?X1 ?X2) =>
      let HypDDPT := fresh "HypDDPT" in
      cut (derivable X1); [ intro HypDDPT; apply HypDDPT | assumption ]
    |  |- (True -> derivable_pt _ _) =>
      let HypTruE := fresh "HypTruE" in
      intro HypTruE; clear HypTruE; is_diff_pt
    | _ =>
      try
        unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct, id,
          fct_cte, comp, pow_fct in |- *
  end.

(**********)
Ltac is_diff_glob :=
  match goal with
    |  |- (derivable Rsqr) =>
  (* fonctions de base *)
      apply derivable_Rsqr
    |  |- (derivable id) => apply derivable_id
    |  |- (derivable (fct_cte _)) => apply derivable_const
    |  |- (derivable sin) => apply derivable_sin
    |  |- (derivable cos) => apply derivable_cos
    |  |- (derivable cosh) => apply derivable_cosh
    |  |- (derivable sinh) => apply derivable_sinh
    |  |- (derivable exp) => apply derivable_exp
    |  |- (derivable (pow_fct _)) =>
      unfold pow_fct in |- *;
        apply derivable_pow
        (* regles de differentiabilite *)
        (* PLUS *)
    |  |- (derivable (?X1 + ?X2)) =>
      apply (derivable_plus X1 X2); is_diff_glob
       (* MOINS *)
    |  |- (derivable (?X1 - ?X2)) =>
      apply (derivable_minus X1 X2); is_diff_glob
       (* OPPOSE *)
    |  |- (derivable (- ?X1)) =>
      apply (derivable_opp X1);
        is_diff_glob
       (* MULTIPLICATION PAR UN SCALAIRE *)
    |  |- (derivable (mult_real_fct ?X1 ?X2)) =>
      apply (derivable_scal X2 X1); is_diff_glob
       (* MULTIPLICATION *)
    |  |- (derivable (?X1 * ?X2)) =>
      apply (derivable_mult X1 X2); is_diff_glob
       (* DIVISION *)
    |  |- (derivable (?X1 / ?X2)) =>
      apply (derivable_div X1 X2);
        [ is_diff_glob
          | is_diff_glob
          | try
            assumption ||
              unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
                id, fct_cte, comp, pow_fct in |- * ]
    |  |- (derivable (/ ?X1)) =>

       (* INVERSION *)
      apply (derivable_inv X1);
        [ try
          assumption ||
            unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
              id, fct_cte, comp, pow_fct in |- *
          | is_diff_glob ]
    |  |- (derivable (comp sqrt _)) =>

       (* COMPOSITION *)
      unfold derivable in |- *; intro; try is_diff_pt
    |  |- (derivable (comp Rabs _)) =>
      unfold derivable in |- *; intro; try is_diff_pt
    |  |- (derivable (comp ?X1 ?X2)) =>
      apply (derivable_comp X2 X1); is_diff_glob
    | _:(derivable ?X1) |- (derivable ?X1) => assumption
    |  |- (True -> derivable _) =>
      let HypTruE := fresh "HypTruE" in
      intro HypTruE; clear HypTruE; is_diff_glob
    | _ =>
      try
        unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct, id,
          fct_cte, comp, pow_fct in |- *
  end.

(**********)
Ltac is_cont_pt :=
  match goal with
    |  |- (continuity_pt Rsqr _) =>

       (* fonctions de base *)
      apply derivable_continuous_pt; apply derivable_pt_Rsqr
    |  |- (continuity_pt id ?X1) =>
      apply derivable_continuous_pt; apply (derivable_pt_id X1)
    |  |- (continuity_pt (fct_cte _) _) =>
      apply derivable_continuous_pt; apply derivable_pt_const
    |  |- (continuity_pt sin _) =>
      apply derivable_continuous_pt; apply derivable_pt_sin
    |  |- (continuity_pt cos _) =>
      apply derivable_continuous_pt; apply derivable_pt_cos
    |  |- (continuity_pt sinh _) =>
      apply derivable_continuous_pt; apply derivable_pt_sinh
    |  |- (continuity_pt cosh _) =>
      apply derivable_continuous_pt; apply derivable_pt_cosh
    |  |- (continuity_pt exp _) =>
      apply derivable_continuous_pt; apply derivable_pt_exp
    |  |- (continuity_pt (pow_fct _) _) =>
      unfold pow_fct in |- *; apply derivable_continuous_pt;
        apply derivable_pt_pow
    |  |- (continuity_pt sqrt ?X1) =>
      apply continuity_pt_sqrt;
        assumption ||
          unfold plus_fct, minus_fct, opp_fct, mult_fct, div_fct, inv_fct,
            comp, id, fct_cte, pow_fct in |- *
    |  |- (continuity_pt Rabs ?X1) =>
      apply (Rcontinuity_abs X1)
       (* regles de differentiabilite *)
       (* PLUS *)
    |  |- (continuity_pt (?X1 + ?X2) ?X3) =>
      apply (continuity_pt_plus X1 X2 X3); is_cont_pt
       (* MOINS *)
    |  |- (continuity_pt (?X1 - ?X2) ?X3) =>
      apply (continuity_pt_minus X1 X2 X3); is_cont_pt
       (* OPPOSE *)
    |  |- (continuity_pt (- ?X1) ?X2) =>
      apply (continuity_pt_opp X1 X2);
        is_cont_pt
       (* MULTIPLICATION PAR UN SCALAIRE *)
    |  |- (continuity_pt (mult_real_fct ?X1 ?X2) ?X3) =>
      apply (continuity_pt_scal X2 X1 X3); is_cont_pt
       (* MULTIPLICATION *)
    |  |- (continuity_pt (?X1 * ?X2) ?X3) =>
      apply (continuity_pt_mult X1 X2 X3); is_cont_pt
       (* DIVISION *)
    |  |- (continuity_pt (?X1 / ?X2) ?X3) =>
      apply (continuity_pt_div X1 X2 X3);
        [ is_cont_pt
          | is_cont_pt
          | try
            assumption ||
              unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
                comp, id, fct_cte, pow_fct in |- * ]
    |  |- (continuity_pt (/ ?X1) ?X2) =>

       (* INVERSION *)
      apply (continuity_pt_inv X1 X2);
        [ is_cont_pt
          | assumption ||
            unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
              comp, id, fct_cte, pow_fct in |- * ]
    |  |- (continuity_pt (comp ?X1 ?X2) ?X3) =>

       (* COMPOSITION *)
      apply (continuity_pt_comp X2 X1 X3); is_cont_pt
    | _:(continuity_pt ?X1 ?X2) |- (continuity_pt ?X1 ?X2) =>
      assumption
    | _:(continuity ?X1) |- (continuity_pt ?X1 ?X2) =>
      let HypDDPT := fresh "HypDDPT" in
      cut (continuity X1); [ intro HypDDPT; apply HypDDPT | assumption ]
    | _:(derivable_pt ?X1 ?X2) |- (continuity_pt ?X1 ?X2) =>
      apply derivable_continuous_pt; assumption
    | _:(derivable ?X1) |- (continuity_pt ?X1 ?X2) =>
      let HypDDPT := fresh "HypDDPT" in
      cut (continuity X1);
        [ intro HypDDPT; apply HypDDPT
          | apply derivable_continuous; assumption ]
    |  |- (True -> continuity_pt _ _) =>
      let HypTruE := fresh "HypTruE" in
      intro HypTruE; clear HypTruE; is_cont_pt
    | _ =>
      try
        unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct, id,
          fct_cte, comp, pow_fct in |- *
  end.

(**********)
Ltac is_cont_glob :=
  match goal with
    |  |- (continuity Rsqr) =>

       (* fonctions de base *)
      apply derivable_continuous; apply derivable_Rsqr
    |  |- (continuity id) => apply derivable_continuous; apply derivable_id
    |  |- (continuity (fct_cte _)) =>
      apply derivable_continuous; apply derivable_const
    |  |- (continuity sin) => apply derivable_continuous; apply derivable_sin
    |  |- (continuity cos) => apply derivable_continuous; apply derivable_cos
    |  |- (continuity exp) => apply derivable_continuous; apply derivable_exp
    |  |- (continuity (pow_fct _)) =>
      unfold pow_fct in |- *; apply derivable_continuous; apply derivable_pow
    |  |- (continuity sinh) =>
      apply derivable_continuous; apply derivable_sinh
    |  |- (continuity cosh) =>
      apply derivable_continuous; apply derivable_cosh
    |  |- (continuity Rabs) =>
      apply Rcontinuity_abs
       (* regles de continuite *)
       (* PLUS *)
    |  |- (continuity (?X1 + ?X2)) =>
      apply (continuity_plus X1 X2);
        try is_cont_glob || assumption
            (* MOINS *)
    |  |- (continuity (?X1 - ?X2)) =>
      apply (continuity_minus X1 X2);
        try is_cont_glob || assumption
            (* OPPOSE *)
    |  |- (continuity (- ?X1)) =>
      apply (continuity_opp X1); try is_cont_glob || assumption
                                      (* INVERSE *)
    |  |- (continuity (/ ?X1)) =>
      apply (continuity_inv X1);
        try is_cont_glob || assumption
            (* MULTIPLICATION PAR UN SCALAIRE *)
    |  |- (continuity (mult_real_fct ?X1 ?X2)) =>
      apply (continuity_scal X2 X1);
        try is_cont_glob || assumption
            (* MULTIPLICATION *)
    |  |- (continuity (?X1 * ?X2)) =>
      apply (continuity_mult X1 X2);
        try is_cont_glob || assumption
            (* DIVISION *)
    |  |- (continuity (?X1 / ?X2)) =>
      apply (continuity_div X1 X2);
        [ try is_cont_glob || assumption
          | try is_cont_glob || assumption
          | try
            assumption ||
              unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct,
                id, fct_cte, pow_fct in |- * ]
    |  |- (continuity (comp sqrt _)) =>

       (* COMPOSITION *)
      unfold continuity_pt in |- *; intro; try is_cont_pt
    |  |- (continuity (comp ?X1 ?X2)) =>
      apply (continuity_comp X2 X1); try is_cont_glob || assumption
    | _:(continuity ?X1) |- (continuity ?X1) => assumption
    |  |- (True -> continuity _) =>
      let HypTruE := fresh "HypTruE" in
      intro HypTruE; clear HypTruE; is_cont_glob
    | _:(derivable ?X1) |- (continuity ?X1) =>
      apply derivable_continuous; assumption
    | _ =>
      try
        unfold plus_fct, mult_fct, div_fct, minus_fct, opp_fct, inv_fct, id,
          fct_cte, comp, pow_fct in |- *
  end.

(**********)
Ltac rew_term trm :=
  match constr:(trm) with
    | (?X1 + ?X2) =>
      let p1 := rew_term X1 with p2 := rew_term X2 in
        match constr:(p1) with
          | (fct_cte ?X3) =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:(fct_cte (X3 + X4))
              | _ => constr:((p1 + p2)%F)
            end
          | _ => constr:((p1 + p2)%F)
        end
    | (?X1 - ?X2) =>
      let p1 := rew_term X1 with p2 := rew_term X2 in
        match constr:(p1) with
          | (fct_cte ?X3) =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:(fct_cte (X3 - X4))
              | _ => constr:((p1 - p2)%F)
            end
          | _ => constr:((p1 - p2)%F)
        end
    | (?X1 / ?X2) =>
      let p1 := rew_term X1 with p2 := rew_term X2 in
        match constr:(p1) with
          | (fct_cte ?X3) =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:(fct_cte (X3 / X4))
              | _ => constr:((p1 / p2)%F)
            end
          | _ =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:((p1 * fct_cte (/ X4))%F)
              | _ => constr:((p1 / p2)%F)
            end
        end
    | (?X1 * / ?X2) =>
      let p1 := rew_term X1 with p2 := rew_term X2 in
        match constr:(p1) with
          | (fct_cte ?X3) =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:(fct_cte (X3 / X4))
              | _ => constr:((p1 / p2)%F)
            end
          | _ =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:((p1 * fct_cte (/ X4))%F)
              | _ => constr:((p1 / p2)%F)
            end
        end
    | (?X1 * ?X2) =>
      let p1 := rew_term X1 with p2 := rew_term X2 in
        match constr:(p1) with
          | (fct_cte ?X3) =>
            match constr:(p2) with
              | (fct_cte ?X4) => constr:(fct_cte (X3 * X4))
              | _ => constr:((p1 * p2)%F)
            end
          | _ => constr:((p1 * p2)%F)
        end
    | (- ?X1) =>
      let p := rew_term X1 in
        match constr:(p) with
          | (fct_cte ?X2) => constr:(fct_cte (- X2))
          | _ => constr:((- p)%F)
        end
    | (/ ?X1) =>
      let p := rew_term X1 in
        match constr:(p) with
          | (fct_cte ?X2) => constr:(fct_cte (/ X2))
          | _ => constr:((/ p)%F)
        end
    | (?X1 AppVar) => constr:(X1)
    | (?X1 ?X2) =>
      let p := rew_term X2 in
        match constr:(p) with
          | (fct_cte ?X3) => constr:(fct_cte (X1 X3))
          | _ => constr:(comp X1 p)
        end
    | AppVar => constr:(id)
    | (AppVar ^ ?X1) => constr:(pow_fct X1)
    | (?X1 ^ ?X2) =>
      let p := rew_term X1 in
        match constr:(p) with
          | (fct_cte ?X3) => constr:(fct_cte (pow_fct X2 X3))
          | _ => constr:(comp (pow_fct X2) p)
        end
    | ?X1 => constr:(fct_cte X1)
  end.

(**********)
Ltac deriv_proof trm pt :=
  match constr:(trm) with
    | (?X1 + ?X2)%F =>
      let p1 := deriv_proof X1 pt with p2 := deriv_proof X2 pt in
        constr:(derivable_pt_plus X1 X2 pt p1 p2)
    | (?X1 - ?X2)%F =>
      let p1 := deriv_proof X1 pt with p2 := deriv_proof X2 pt in
        constr:(derivable_pt_minus X1 X2 pt p1 p2)
    | (?X1 * ?X2)%F =>
      let p1 := deriv_proof X1 pt with p2 := deriv_proof X2 pt in
        constr:(derivable_pt_mult X1 X2 pt p1 p2)
    | (?X1 / ?X2)%F =>
      match goal with
        | id:(?X2 pt <> 0) |- _ =>
          let p1 := deriv_proof X1 pt with p2 := deriv_proof X2 pt in
            constr:(derivable_pt_div X1 X2 pt p1 p2 id)
        | _ => constr:(False)
      end
    | (/ ?X1)%F =>
      match goal with
        | id:(?X1 pt <> 0) |- _ =>
          let p1 := deriv_proof X1 pt in
            constr:(derivable_pt_inv X1 pt p1 id)
        | _ => constr:(False)
      end
    | (comp ?X1 ?X2) =>
      let pt_f1 := eval cbv beta in (X2 pt) in
        let p1 := deriv_proof X1 pt_f1 with p2 := deriv_proof X2 pt in
          constr:(derivable_pt_comp X2 X1 pt p2 p1)
    | (- ?X1)%F =>
      let p1 := deriv_proof X1 pt in
        constr:(derivable_pt_opp X1 pt p1)
    | sin => constr:(derivable_pt_sin pt)
    | cos => constr:(derivable_pt_cos pt)
    | sinh => constr:(derivable_pt_sinh pt)
    | cosh => constr:(derivable_pt_cosh pt)
    | exp => constr:(derivable_pt_exp pt)
    | id => constr:(derivable_pt_id pt)
    | Rsqr => constr:(derivable_pt_Rsqr pt)
    | sqrt =>
      match goal with
        | id:(0 < pt) |- _ => constr:(derivable_pt_sqrt pt id)
        | _ => constr:(False)
      end
    | (fct_cte ?X1) => constr:(derivable_pt_const X1 pt)
    | ?X1 =>
      let aux := constr:(X1) in
        match goal with
          | id:(derivable_pt aux pt) |- _ => constr:(id)
          | id:(derivable aux) |- _ => constr:(id pt)
          | _ => constr:(False)
        end
  end.

(**********)
Ltac simplify_derive trm pt :=
  match constr:(trm) with
    | (?X1 + ?X2)%F =>
      try rewrite derive_pt_plus; simplify_derive X1 pt;
        simplify_derive X2 pt
    | (?X1 - ?X2)%F =>
      try rewrite derive_pt_minus; simplify_derive X1 pt;
        simplify_derive X2 pt
    | (?X1 * ?X2)%F =>
      try rewrite derive_pt_mult; simplify_derive X1 pt;
        simplify_derive X2 pt
    | (?X1 / ?X2)%F =>
      try rewrite derive_pt_div; simplify_derive X1 pt; simplify_derive X2 pt
    | (comp ?X1 ?X2) =>
      let pt_f1 := eval cbv beta in (X2 pt) in
        (try rewrite derive_pt_comp; simplify_derive X1 pt_f1;
          simplify_derive X2 pt)
    | (- ?X1)%F => try rewrite derive_pt_opp; simplify_derive X1 pt
    | (/ ?X1)%F =>
      try rewrite derive_pt_inv; simplify_derive X1 pt
    | (fct_cte ?X1) => try rewrite derive_pt_const
    | id => try rewrite derive_pt_id
    | sin => try rewrite derive_pt_sin
    | cos => try rewrite derive_pt_cos
    | sinh => try rewrite derive_pt_sinh
    | cosh => try rewrite derive_pt_cosh
    | exp => try rewrite derive_pt_exp
    | Rsqr => try rewrite derive_pt_Rsqr
    | sqrt => try rewrite derive_pt_sqrt
    | ?X1 =>
      let aux := constr:(X1) in
        match goal with
          | id:(derive_pt aux pt ?X2 = _),H:(derivable aux) |- _ =>
            try replace (derive_pt aux pt (H pt)) with (derive_pt aux pt X2);
              [ rewrite id | apply pr_nu ]
          | id:(derive_pt aux pt ?X2 = _),H:(derivable_pt aux pt) |- _ =>
            try replace (derive_pt aux pt H) with (derive_pt aux pt X2);
              [ rewrite id | apply pr_nu ]
          | _ => idtac
        end
    | _ => idtac
  end.

(**********)
Ltac reg :=
  match goal with
    |  |- (derivable_pt ?X1 ?X2) =>
      let trm := eval cbv beta in (X1 AppVar) in
        let aux := rew_term trm in
          (intro_hyp_pt aux X2;
            try (change (derivable_pt aux X2) in |- *; is_diff_pt) || is_diff_pt)
    |  |- (derivable ?X1) =>
      let trm := eval cbv beta in (X1 AppVar) in
        let aux := rew_term trm in
          (intro_hyp_glob aux;
            try (change (derivable aux) in |- *; is_diff_glob) || is_diff_glob)
    |  |- (continuity ?X1) =>
      let trm := eval cbv beta in (X1 AppVar) in
        let aux := rew_term trm in
          (intro_hyp_glob aux;
            try (change (continuity aux) in |- *; is_cont_glob) || is_cont_glob)
    |  |- (continuity_pt ?X1 ?X2) =>
      let trm := eval cbv beta in (X1 AppVar) in
        let aux := rew_term trm in
          (intro_hyp_pt aux X2;
            try (change (continuity_pt aux X2) in |- *; is_cont_pt) || is_cont_pt)
    |  |- (derive_pt ?X1 ?X2 ?X3 = ?X4) =>
      let trm := eval cbv beta in (X1 AppVar) in
      let aux := rew_term trm in
      intro_hyp_pt aux X2;
      (let aux2 := deriv_proof aux X2 in
       try
         (replace (derive_pt X1 X2 X3) with (derive_pt aux X2 aux2);
           [ simplify_derive aux X2;
             try unfold plus_fct, minus_fct, mult_fct, div_fct, id, fct_cte,
                        inv_fct, opp_fct in |- *; ring || ring_simplify
           | try apply pr_nu ]) || is_diff_pt)
  end.
