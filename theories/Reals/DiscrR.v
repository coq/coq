(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i        $Id$       i*)

Require RIneq.
Require Omega.

Recursive Tactic Definition Isrealint trm:=
  Match trm With
  | [``0``] -> Idtac
  | [``1``] -> Idtac
  | [``?1+?2``] -> (Isrealint ?1);(Isrealint ?2)
  | [``?1-?2``] -> (Isrealint ?1);(Isrealint ?2)
  | [``?1*?2``] -> (Isrealint ?1);(Isrealint ?2)
  | [``-?1``] -> (Isrealint ?1)
  | _ -> Fail.

Recursive Meta Definition ToINR trm:=
  Match trm With
  | [ ``1`` ] ->  '(S O)
  | [ ``1 + ?1`` ] -> Let t=(ToINR ?1) In '(S t).

Tactic Definition DiscrR :=
  Try Match Context With
  | [ |- ~(?1==?2) ] ->
    Isrealint ?1;Isrealint ?2;
    Apply Rminus_not_eq; Ring ``?1-?2``; 
      (Match Context With
      | [ |- [``-1``] ] -> 
        Repeat Rewrite <- Ropp_distr1;Apply Ropp_neq
      | _ -> Idtac);
      (Match Context With
      | [ |- ``?1<>0``] -> Let nbr=(ToINR ?1) In
        Replace ?1 with (INR nbr);
          [Apply not_O_INR;Discriminate|Simpl;Ring]).

Lemma Rlt_R0_R2 : ``0<2``.
Replace ``2`` with (INR (2)); [Apply lt_INR_0; Apply lt_O_Sn | Reflexivity].
Qed.

Lemma Rplus_lt_pos : (x,y:R) ``0<x`` -> ``0<y`` -> ``0<x+y``.
Intros.
Apply Rlt_trans with x.
Assumption. 
Pattern 1 x; Rewrite <- Rplus_Or.
Apply Rlt_compatibility.
Assumption.
Qed.

Recursive Tactic Definition Sup0 :=
  Match Context With
  | [ |- ``0<1`` ] -> Apply Rlt_R0_R1
  | [ |- ``0<?1`` ] -> Repeat (Apply Rmult_lt_pos Orelse Apply Rplus_lt_pos; Try Apply Rlt_R0_R1 Orelse Apply Rlt_R0_R2)
  | [ |- ``?1>0`` ] -> Change ``0<?1``; Sup0.

Tactic Definition SupOmega := Replace R1 with (IZR `1`); [Repeat Rewrite <- plus_IZR Orelse Rewrite <- mult_IZR; Apply IZR_lt; Omega | Reflexivity].
  
Recursive Tactic Definition Sup :=
  Match Context With
  | [ |- (Rgt ?1 ?2) ] -> Change ``?2<?1``; Sup
  | [ |- ``0<?1`` ] -> Sup0
  | [ |- (Rlt (Ropp ?1) R0) ] -> Rewrite <- Ropp_O; Sup
  | [ |- (Rlt (Ropp ?1) (Ropp ?2)) ] -> Apply Rlt_Ropp; Sup
  | [ |- (Rlt (Ropp ?1) ?2) ] -> Apply Rlt_trans with ``0``; Sup
  | [ |- (Rlt ?1 ?2) ] -> SupOmega
  | _ -> Idtac.

Lemma IZR_eq : (z1,z2:Z) z1=z2 -> (IZR z1)==(IZR z2).
Intros; Rewrite H; Reflexivity.
Qed.

Tactic Definition RCompute := Replace R1 with (IZR `1`); [Replace R0 with (IZR `0`); [Repeat Rewrite <- plus_IZR Orelse Rewrite <- mult_IZR Orelse Rewrite <- Ropp_Ropp_IZR Orelse Rewrite Z_R_minus; Apply IZR_eq; Ring | Reflexivity] | Reflexivity].
