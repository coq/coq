(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i        $Id$       i*)

Require Rbase.

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

Tactic Definition Sup0_lt trm:=
  Replace ``0`` with (INR O);
  [Let nbr=(ToINR trm) In
      Replace trm with (INR nbr);
      [Apply lt_INR; Apply lt_O_Sn|Simpl;Ring]|Simpl;Reflexivity].

Tactic Definition Sup0_gt trm:=
  Unfold Rgt; Sup0_lt trm.   

Tactic Definition Sup0 :=
  Match Context With
  | [ |- ``0<?1`` ] -> (Sup0_lt ?1)
  | [ |- ``?1>0`` ] -> (Sup0_gt ?1).

