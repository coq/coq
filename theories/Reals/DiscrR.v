(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i        $Id$       i*)

Require RIneq.

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