(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
 
(*i $Id$ i*)

Require Rbase.
Require Rfunctions.
Require Rtrigo.
Require SeqSeries.
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
V7only [Import R_scope.]. Open Local Scope R_scope.

Axiom AppVar : R.

(**********)
Recursive Tactic Definition IntroHypG trm :=
Match trm With
|[(plus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(minus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(mult_fct ?1 ?2)] ->
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(div_fct ?1 ?2)] -> Let aux = ?2 In
 (Match Context With
 |[_:(x0:R)``(aux x0)<>0``|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[_:(x0:R)``(aux x0)<>0``|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(derivable ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1; IntroHypG ?2 | Try Assumption]
 |[|-(continuity ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1; IntroHypG ?2 | Try Assumption]
 | _ -> Idtac)
|[(comp ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1; IntroHypG ?2
 |[|-(continuity ?)] -> IntroHypG ?1; IntroHypG ?2
 | _ -> Idtac)
|[(opp_fct ?1)] -> 
 (Match Context With
 |[|-(derivable ?)] -> IntroHypG ?1
 |[|-(continuity ?)] -> IntroHypG ?1
 | _ -> Idtac)
|[(inv_fct ?1)] -> Let aux = ?1 In
 (Match Context With
 |[_:(x0:R)``(aux x0)<>0``|-(derivable ?)] -> IntroHypG ?1
 |[_:(x0:R)``(aux x0)<>0``|-(continuity ?)] -> IntroHypG ?1
 |[|-(derivable ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1 | Try Assumption]
 |[|-(continuity ?)] -> Cut ((x0:R)``(aux x0)<>0``); [Intro; IntroHypG ?1| Try Assumption]
 | _ -> Idtac)
|[cos] -> Idtac
|[sin] -> Idtac
|[cosh] -> Idtac
|[sinh] -> Idtac
|[exp] -> Idtac
|[Rsqr] -> Idtac
|[sqrt] -> Idtac
|[id] -> Idtac
|[(fct_cte ?)] -> Idtac
|[(pow_fct ?)] -> Idtac
|[Rabsolu] -> Idtac
|[?1] -> Let p = ?1 In
 (Match Context With
 |[_:(derivable p)|- ?] -> Idtac
 |[|-(derivable p)] -> Idtac
 |[|-(derivable ?)] -> Cut True -> (derivable p); [Intro HYPPD; Cut (derivable p); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | [_:(continuity p)|- ?] -> Idtac
 |[|-(continuity p)] -> Idtac
 |[|-(continuity ?)] -> Cut True -> (continuity p); [Intro HYPPD; Cut (continuity p); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | _ -> Idtac).

(**********)
Recursive Tactic Definition IntroHypL trm pt :=
Match trm With
|[(plus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(minus_fct ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(mult_fct ?1 ?2)] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 | _ -> Idtac)
|[(div_fct ?1 ?2)] -> Let aux = ?2 In
 (Match Context With
 |[_:``(aux pt)<>0``|-(derivable_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[_:``(aux pt)<>0``|-(continuity_pt ? ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[_:``(aux pt)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(derivable_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(continuity_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[id:(x0:R)``(aux x0)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt; IntroHypL ?2 pt
 |[|-(derivable_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt; IntroHypL ?2 pt | Try Assumption]
 | _ -> Idtac)
|[(comp ?1 ?2)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 |[|-(continuity_pt ? ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In IntroHypL ?1 pt_f1; IntroHypL ?2 pt
 | _ -> Idtac)
|[(opp_fct ?1)] -> 
 (Match Context With
 |[|-(derivable_pt ? ?)] -> IntroHypL ?1 pt
 |[|-(continuity_pt ? ?)] -> IntroHypL ?1 pt
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt
 | _ -> Idtac)
|[(inv_fct ?1)] -> Let aux = ?1 In
 (Match Context With
 |[_:``(aux pt)<>0``|-(derivable_pt ? ?)] -> IntroHypL ?1 pt
 |[_:``(aux pt)<>0``|-(continuity_pt ? ?)] -> IntroHypL ?1 pt
 |[_:``(aux pt)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(derivable_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(continuity_pt ? ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[id:(x0:R)``(aux x0)<>0``|-(eqT ? (derive_pt ? ? ?) ?)] -> Generalize (id pt); Intro; IntroHypL ?1 pt
 |[|-(derivable_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt| Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``(aux pt)<>0``; [Intro; IntroHypL ?1 pt | Try Assumption]
 | _ -> Idtac)
|[cos] -> Idtac
|[sin] -> Idtac
|[cosh] -> Idtac
|[sinh] -> Idtac
|[exp] -> Idtac
|[Rsqr] -> Idtac
|[id] -> Idtac
|[(fct_cte ?)] -> Idtac
|[(pow_fct ?)] -> Idtac
|[sqrt] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Cut ``0<pt``; [Intro | Try Assumption]
 |[|-(continuity_pt ? ?)] -> Cut ``0<=pt``; [Intro | Try Assumption]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut ``0<pt``; [Intro | Try Assumption]
 | _ -> Idtac)
|[Rabsolu] ->
 (Match Context With
 |[|-(derivable_pt ? ?)] -> Cut ``pt<>0``; [Intro | Try Assumption]
 | _ -> Idtac)
|[?1] -> Let p = ?1 In
 (Match Context With
 |[_:(derivable_pt p pt)|- ?] -> Idtac
 |[|-(derivable_pt p pt)] -> Idtac
 |[|-(derivable_pt ? ?)] -> Cut True -> (derivable_pt p pt); [Intro HYPPD; Cut (derivable_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 |[_:(continuity_pt p pt)|- ?] -> Idtac
 |[|-(continuity_pt p pt)] -> Idtac
 |[|-(continuity_pt ? ?)] -> Cut True -> (continuity_pt p pt); [Intro HYPPD; Cut (continuity_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 |[|-(eqT ? (derive_pt ? ? ?) ?)] -> Cut True -> (derivable_pt p pt); [Intro HYPPD; Cut (derivable_pt p pt); [Intro; Clear HYPPD | Apply HYPPD; Clear HYPPD; Trivial] | Idtac]
 | _ -> Idtac).
 
(**********)
Recursive Tactic Definition IsDiff_pt :=
Match Context With
 (* fonctions de base *)
 [|-(derivable_pt Rsqr ?)] -> Apply derivable_pt_Rsqr
|[|-(derivable_pt id ?1)] -> Apply (derivable_pt_id ?1)
|[|-(derivable_pt (fct_cte ?) ?)] -> Apply derivable_pt_const
|[|-(derivable_pt sin ?)] -> Apply derivable_pt_sin
|[|-(derivable_pt cos ?)] -> Apply derivable_pt_cos
|[|-(derivable_pt sinh ?)] -> Apply derivable_pt_sinh
|[|-(derivable_pt cosh ?)] -> Apply derivable_pt_cosh
|[|-(derivable_pt exp ?)] -> Apply derivable_pt_exp
|[|-(derivable_pt (pow_fct ?) ?)] -> Unfold pow_fct; Apply derivable_pt_pow
|[|-(derivable_pt sqrt ?1)] -> Apply (derivable_pt_sqrt ?1); Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
|[|-(derivable_pt Rabsolu ?1)] -> Apply (derivable_pt_Rabsolu ?1); Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
 (* regles de differentiabilite *)
 (* PLUS *)
|[|-(derivable_pt (plus_fct ?1 ?2) ?3)] -> Apply (derivable_pt_plus ?1 ?2 ?3); IsDiff_pt
 (* MOINS *)
|[|-(derivable_pt (minus_fct ?1 ?2) ?3)] -> Apply (derivable_pt_minus ?1 ?2 ?3); IsDiff_pt
 (* OPPOSE *)
|[|-(derivable_pt (opp_fct ?1) ?2)] -> Apply (derivable_pt_opp ?1 ?2); IsDiff_pt
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(derivable_pt (mult_real_fct ?1 ?2) ?3)] -> Apply (derivable_pt_scal ?2 ?1 ?3); IsDiff_pt
 (* MULTIPLICATION *)
|[|-(derivable_pt (mult_fct ?1 ?2) ?3)] -> Apply (derivable_pt_mult ?1 ?2 ?3); IsDiff_pt
  (* DIVISION *)
 |[|-(derivable_pt (div_fct ?1 ?2) ?3)] -> Apply (derivable_pt_div ?1 ?2 ?3); [IsDiff_pt | IsDiff_pt | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp pow_fct id fct_cte]
  (* INVERSION *)
 |[|-(derivable_pt (inv_fct ?1) ?2)] -> Apply (derivable_pt_inv ?1 ?2); [Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp pow_fct id fct_cte | IsDiff_pt]
 (* COMPOSITION *)
|[|-(derivable_pt (comp ?1 ?2) ?3)] -> Apply (derivable_pt_comp ?2 ?1 ?3); IsDiff_pt
|[_:(derivable_pt ?1 ?2)|-(derivable_pt ?1 ?2)] -> Assumption
|[_:(derivable ?1) |- (derivable_pt ?1 ?2)] -> Cut (derivable ?1); [Intro HypDDPT; Apply HypDDPT | Assumption]
|[|-True->(derivable_pt ? ?)] -> Intro HypTruE; Clear HypTruE; IsDiff_pt
| _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsDiff_glob :=
Match Context With
 (* fonctions de base *)
  [|-(derivable Rsqr)] -> Apply derivable_Rsqr
 |[|-(derivable id)] -> Apply derivable_id
 |[|-(derivable (fct_cte ?))] -> Apply derivable_const
 |[|-(derivable sin)] -> Apply derivable_sin
 |[|-(derivable cos)] -> Apply derivable_cos
 |[|-(derivable cosh)] -> Apply derivable_cosh
 |[|-(derivable sinh)] -> Apply derivable_sinh
 |[|-(derivable exp)] -> Apply derivable_exp
 |[|-(derivable (pow_fct ?))] -> Unfold pow_fct; Apply derivable_pow
  (* regles de differentiabilite *)
  (* PLUS *)
 |[|-(derivable (plus_fct ?1 ?2))] -> Apply (derivable_plus ?1 ?2); IsDiff_glob
  (* MOINS *)
 |[|-(derivable (minus_fct ?1 ?2))] -> Apply (derivable_minus ?1 ?2); IsDiff_glob
  (* OPPOSE *)
 |[|-(derivable (opp_fct ?1))] -> Apply (derivable_opp ?1); IsDiff_glob
  (* MULTIPLICATION PAR UN SCALAIRE *)
 |[|-(derivable (mult_real_fct ?1 ?2))] -> Apply (derivable_scal ?2 ?1); IsDiff_glob
  (* MULTIPLICATION *)
 |[|-(derivable (mult_fct ?1 ?2))] -> Apply (derivable_mult ?1 ?2); IsDiff_glob
  (* DIVISION *)
 |[|-(derivable (div_fct ?1 ?2))] -> Apply (derivable_div ?1 ?2); [IsDiff_glob | IsDiff_glob | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct]
  (* INVERSION *)
 |[|-(derivable (inv_fct ?1))] -> Apply (derivable_inv ?1); [Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct | IsDiff_glob]
  (* COMPOSITION *)
 |[|-(derivable (comp sqrt ?))] -> Unfold derivable; Intro; Try IsDiff_pt
 |[|-(derivable (comp Rabsolu ?))] -> Unfold derivable; Intro; Try IsDiff_pt
 |[|-(derivable (comp ?1 ?2))] -> Apply (derivable_comp ?2 ?1); IsDiff_glob
 |[_:(derivable ?1)|-(derivable ?1)] -> Assumption
 |[|-True->(derivable ?)] -> Intro HypTruE; Clear HypTruE; IsDiff_glob
 | _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsCont_pt :=
Match Context With
 (* fonctions de base *)
 [|-(continuity_pt Rsqr ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_Rsqr
|[|-(continuity_pt id ?1)] -> Apply derivable_continuous_pt; Apply (derivable_pt_id ?1)
|[|-(continuity_pt (fct_cte ?) ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_const
|[|-(continuity_pt sin ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_sin
|[|-(continuity_pt cos ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_cos
|[|-(continuity_pt sinh ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_sinh
|[|-(continuity_pt cosh ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_cosh
|[|-(continuity_pt exp ?)] -> Apply derivable_continuous_pt; Apply derivable_pt_exp
|[|-(continuity_pt (pow_fct ?) ?)] -> Unfold pow_fct; Apply derivable_continuous_pt; Apply derivable_pt_pow
|[|-(continuity_pt sqrt ?1)] -> Apply continuity_pt_sqrt; Assumption Orelse Unfold plus_fct minus_fct opp_fct mult_fct div_fct inv_fct comp id fct_cte pow_fct
|[|-(continuity_pt Rabsolu ?1)] -> Apply (continuity_Rabsolu ?1)
 (* regles de differentiabilite *)
 (* PLUS *)
|[|-(continuity_pt (plus_fct ?1 ?2) ?3)] -> Apply (continuity_pt_plus ?1 ?2 ?3); IsCont_pt
 (* MOINS *)
|[|-(continuity_pt (minus_fct ?1 ?2) ?3)] -> Apply (continuity_pt_minus ?1 ?2 ?3); IsCont_pt
 (* OPPOSE *)
|[|-(continuity_pt (opp_fct ?1) ?2)] -> Apply (continuity_pt_opp ?1 ?2); IsCont_pt
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(continuity_pt (mult_real_fct ?1 ?2) ?3)] -> Apply (continuity_pt_scal ?2 ?1 ?3); IsCont_pt
 (* MULTIPLICATION *)
|[|-(continuity_pt (mult_fct ?1 ?2) ?3)] -> Apply (continuity_pt_mult ?1 ?2 ?3); IsCont_pt
  (* DIVISION *)
 |[|-(continuity_pt (div_fct ?1 ?2) ?3)] -> Apply (continuity_pt_div ?1 ?2 ?3); [IsCont_pt | IsCont_pt | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp id fct_cte pow_fct]
  (* INVERSION *)
 |[|-(continuity_pt (inv_fct ?1) ?2)] -> Apply (continuity_pt_inv ?1 ?2); [IsCont_pt | Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct comp id fct_cte pow_fct]
 (* COMPOSITION *)
|[|-(continuity_pt (comp ?1 ?2) ?3)] -> Apply (continuity_pt_comp ?2 ?1 ?3); IsCont_pt
|[_:(continuity_pt ?1 ?2)|-(continuity_pt ?1 ?2)] -> Assumption
|[_:(continuity ?1) |- (continuity_pt ?1 ?2)] -> Cut (continuity ?1); [Intro HypDDPT; Apply HypDDPT | Assumption]
|[_:(derivable_pt ?1 ?2)|-(continuity_pt ?1 ?2)] -> Apply derivable_continuous_pt; Assumption
|[_:(derivable ?1)|-(continuity_pt ?1 ?2)] -> Cut (continuity ?1); [Intro HypDDPT; Apply HypDDPT | Apply derivable_continuous; Assumption]
|[|-True->(continuity_pt ? ?)] -> Intro HypTruE; Clear HypTruE; IsCont_pt
| _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition IsCont_glob :=
Match Context With
  (* fonctions de base *)
  [|-(continuity Rsqr)] -> Apply derivable_continuous; Apply derivable_Rsqr
 |[|-(continuity id)] -> Apply derivable_continuous; Apply derivable_id
 |[|-(continuity (fct_cte ?))] -> Apply derivable_continuous; Apply derivable_const
 |[|-(continuity sin)] -> Apply derivable_continuous; Apply derivable_sin
 |[|-(continuity cos)] -> Apply derivable_continuous; Apply derivable_cos
 |[|-(continuity exp)] -> Apply derivable_continuous; Apply derivable_exp
 |[|-(continuity (pow_fct ?))] -> Unfold pow_fct; Apply derivable_continuous; Apply derivable_pow
 |[|-(continuity sinh)] -> Apply derivable_continuous; Apply derivable_sinh
 |[|-(continuity cosh)] -> Apply derivable_continuous; Apply derivable_cosh
 |[|-(continuity Rabsolu)] -> Apply continuity_Rabsolu
 (* regles de continuite *)
 (* PLUS *)
|[|-(continuity (plus_fct ?1 ?2))] -> Apply (continuity_plus ?1 ?2); Try IsCont_glob Orelse Assumption
 (* MOINS *)
|[|-(continuity (minus_fct ?1 ?2))] -> Apply (continuity_minus ?1 ?2); Try IsCont_glob Orelse Assumption
 (* OPPOSE *)
|[|-(continuity (opp_fct ?1))] -> Apply (continuity_opp ?1); Try IsCont_glob Orelse Assumption
 (* INVERSE *)
|[|-(continuity (inv_fct ?1))] -> Apply (continuity_inv ?1); Try IsCont_glob Orelse Assumption
 (* MULTIPLICATION PAR UN SCALAIRE *)
|[|-(continuity (mult_real_fct ?1 ?2))] -> Apply (continuity_scal ?2 ?1); Try IsCont_glob Orelse Assumption
 (* MULTIPLICATION *)
|[|-(continuity (mult_fct ?1 ?2))] -> Apply (continuity_mult ?1 ?2); Try IsCont_glob Orelse Assumption
  (* DIVISION *)
 |[|-(continuity (div_fct ?1 ?2))] -> Apply (continuity_div ?1 ?2); [Try IsCont_glob Orelse Assumption | Try IsCont_glob Orelse Assumption | Try Assumption Orelse Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte pow_fct]
  (* COMPOSITION *)
 |[|-(continuity (comp sqrt ?))] -> Unfold continuity_pt; Intro; Try IsCont_pt
 |[|-(continuity (comp ?1 ?2))] -> Apply (continuity_comp ?2 ?1); Try IsCont_glob Orelse Assumption
 |[_:(continuity ?1)|-(continuity ?1)] -> Assumption
 |[|-True->(continuity ?)] -> Intro HypTruE; Clear HypTruE; IsCont_glob
 |[_:(derivable ?1)|-(continuity ?1)] -> Apply derivable_continuous; Assumption
 | _ -> Try Unfold plus_fct mult_fct div_fct minus_fct opp_fct inv_fct id fct_cte comp pow_fct.

(**********)
Recursive Tactic Definition RewTerm trm :=
Match trm With
| [(Rplus ?1 ?2)] -> Let p1= (RewTerm ?1) And p2 = (RewTerm ?2) In 
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rplus ?3 ?4))
    | _ -> '(plus_fct p1 p2))
  | _ -> '(plus_fct p1 p2))
| [(Rminus ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rminus ?3 ?4))
    | _ -> '(minus_fct p1 p2))
  | _ -> '(minus_fct p1 p2))
| [(Rdiv ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rdiv ?3 ?4))
    | _ -> '(div_fct p1 p2))
  | _ -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(mult_fct p1 (fct_cte (Rinv ?4)))
    | _ -> '(div_fct p1 p2)))
| [(Rmult ?1 (Rinv ?2))] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rdiv ?3 ?4))
    | _ -> '(div_fct p1 p2))
  | _ -> 
   (Match p2 With
   | [(fct_cte ?4)] -> '(mult_fct p1 (fct_cte (Rinv ?4)))
   | _ -> '(div_fct p1 p2)))
| [(Rmult ?1 ?2)] -> Let p1 = (RewTerm ?1) And p2 = (RewTerm ?2) In
  (Match p1 With
   [(fct_cte ?3)] -> 
    (Match p2 With
    | [(fct_cte ?4)] -> '(fct_cte (Rmult ?3 ?4))
    | _ -> '(mult_fct p1 p2))
  | _ -> '(mult_fct p1 p2))
| [(Ropp ?1)] -> Let p = (RewTerm ?1) In 
  (Match p With
   [(fct_cte ?2)] -> '(fct_cte (Ropp ?2))
   | _ -> '(opp_fct p))
| [(Rinv ?1)] -> Let p = (RewTerm ?1) In 
  (Match p With
   [(fct_cte ?2)] -> '(fct_cte (Rinv ?2))
   | _ -> '(inv_fct p))
| [(?1 AppVar)] -> '?1
| [(?1 ?2)] -> Let p = (RewTerm ?2) In 
 (Match p With
 | [(fct_cte ?3)] -> '(fct_cte (?1 ?3))
 | _ -> '(comp ?1 p))
| [AppVar] -> 'id
| [(pow AppVar ?1)] -> '(pow_fct ?1)
| [(pow ?1 ?2)] -> Let p = (RewTerm ?1) In 
 (Match p With
 | [(fct_cte ?3)] -> '(fct_cte (pow_fct ?2 ?3))
 | _ -> '(comp (pow_fct ?2) p))
| [?1]-> '(fct_cte ?1).

(**********)
Recursive Tactic Definition ConsProof trm pt :=
Match trm With
| [(plus_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_plus ?1 ?2 pt p1 p2)
| [(minus_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_minus ?1 ?2 pt p1 p2)
| [(mult_fct ?1 ?2)] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_mult ?1 ?2 pt p1 p2)
| [(div_fct ?1 ?2)] ->
 (Match Context With
 |[id:~((?2 pt)==R0) |- ?] -> Let p1 = (ConsProof ?1 pt) And p2 = (ConsProof ?2 pt) In '(derivable_pt_div ?1 ?2 pt p1 p2 id)
 | _ -> 'False)
| [(inv_fct ?1)] ->
 (Match Context With
 |[id:~((?1 pt)==R0) |- ?] -> Let p1 = (ConsProof ?1 pt) In '(derivable_pt_inv ?1 pt p1 id)
 | _ -> 'False)
| [(comp ?1 ?2)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In Let p1 = (ConsProof ?1 pt_f1) And p2 = (ConsProof ?2 pt) In '(derivable_pt_comp ?2 ?1 pt p2 p1)
| [(opp_fct ?1)] -> Let p1 = (ConsProof ?1 pt) In '(derivable_pt_opp ?1 pt p1)
| [sin] -> '(derivable_pt_sin pt)
| [cos] -> '(derivable_pt_cos pt)
| [sinh] -> '(derivable_pt_sinh pt)
| [cosh] -> '(derivable_pt_cosh pt)
| [exp] -> '(derivable_pt_exp pt)
| [id] -> '(derivable_pt_id pt)
| [Rsqr] -> '(derivable_pt_Rsqr pt)
| [sqrt] ->
 (Match Context With
 |[id:(Rlt R0 pt) |- ?] -> '(derivable_pt_sqrt pt id)
 | _ -> 'False)
| [(fct_cte ?1)] -> '(derivable_pt_const ?1 pt)
| [?1] -> Let aux = ?1 In
 (Match Context With
    [ id : (derivable_pt aux pt) |- ?] -> 'id
   |[ id : (derivable aux) |- ?] -> '(id pt)
   | _ -> 'False).

(**********)
Recursive Tactic Definition SimplifyDerive trm pt :=
Match trm With
| [(plus_fct ?1 ?2)] -> Try Rewrite derive_pt_plus; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(minus_fct ?1 ?2)] -> Try Rewrite derive_pt_minus; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(mult_fct ?1 ?2)] -> Try Rewrite derive_pt_mult; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(div_fct ?1 ?2)] -> Try Rewrite derive_pt_div; SimplifyDerive ?1 pt; SimplifyDerive ?2 pt
| [(comp ?1 ?2)] -> Let pt_f1 = (Eval Cbv Beta in (?2 pt)) In Try Rewrite derive_pt_comp; SimplifyDerive ?1 pt_f1; SimplifyDerive ?2 pt
| [(opp_fct ?1)] -> Try Rewrite derive_pt_opp; SimplifyDerive ?1 pt
| [(inv_fct ?1)] -> Try Rewrite derive_pt_inv; SimplifyDerive ?1 pt
| [(fct_cte ?1)] -> Try Rewrite derive_pt_const
| [id] -> Try Rewrite derive_pt_id
| [sin] -> Try Rewrite derive_pt_sin
| [cos] -> Try Rewrite derive_pt_cos
| [sinh] -> Try Rewrite derive_pt_sinh
| [cosh] -> Try Rewrite derive_pt_cosh
| [exp] -> Try Rewrite derive_pt_exp
| [Rsqr] -> Try Rewrite derive_pt_Rsqr
| [sqrt] -> Try Rewrite derive_pt_sqrt
| [?1] -> Let aux = ?1 In
  (Match Context With
    [ id : (eqT ? (derive_pt aux pt ?2) ?); H : (derivable aux) |- ? ] -> Try Replace (derive_pt aux pt (H pt)) with (derive_pt aux pt ?2); [Rewrite id | Apply pr_nu]
    |[ id : (eqT ? (derive_pt aux pt ?2) ?); H : (derivable_pt aux pt) |- ? ] -> Try Replace (derive_pt aux pt H) with (derive_pt aux pt ?2); [Rewrite id | Apply pr_nu]
    | _ -> Idtac )
| _ -> Idtac.

(**********)
Tactic Definition Reg :=
Match Context With
| [|-(derivable_pt ?1 ?2)] -> 
Let trm = Eval Cbv Beta in (?1 AppVar) In
Let aux = (RewTerm trm) In IntroHypL aux ?2; Try (Change (derivable_pt aux ?2); IsDiff_pt) Orelse IsDiff_pt
| [|-(derivable ?1)] ->
Let trm = Eval Cbv Beta in (?1 AppVar) In
Let aux = (RewTerm trm) In IntroHypG aux; Try (Change (derivable aux); IsDiff_glob) Orelse IsDiff_glob
| [|-(continuity ?1)] ->
Let trm = Eval Cbv Beta in (?1 AppVar) In
Let aux = (RewTerm trm) In IntroHypG aux; Try (Change (continuity aux); IsCont_glob) Orelse IsCont_glob
| [|-(continuity_pt ?1 ?2)] ->
Let trm = Eval Cbv Beta in (?1 AppVar) In
Let aux = (RewTerm trm) In IntroHypL aux ?2; Try (Change (continuity_pt aux ?2); IsCont_pt) Orelse IsCont_pt
| [|-(eqT ? (derive_pt ?1 ?2 ?3) ?4)] -> 
Let trm = Eval Cbv Beta in (?1 AppVar) In
Let aux = (RewTerm trm) In
IntroHypL aux ?2; Let aux2 = (ConsProof aux ?2) In Try (Replace (derive_pt ?1 ?2 ?3) with (derive_pt aux ?2 aux2); [SimplifyDerive aux ?2; Try Unfold plus_fct minus_fct mult_fct div_fct id fct_cte inv_fct opp_fct; Try Ring | Try Apply pr_nu]) Orelse IsDiff_pt.
