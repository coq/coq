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

Recursive Tactic Definition Sup0 :=
  Match Context With
  | [ |- ``1>0`` ] -> Unfold Rgt;Apply Rlt_R0_R1
  | [ |- ``1+?1>0`` ] ->
    Apply (Rgt_trans ``1+?1`` ?1 ``0``);
    [Pattern 1 ``1+?1``;Rewrite Rplus_sym;Unfold Rgt;
     Apply Rlt_r_r_plus_R1|Sup0].

Tactic Definition DiscrR :=
  Try Match Context With
  | [ |- ~(?1==?2) ] ->
    Isrealint ?1;Isrealint ?2;
    Apply Rminus_not_eq; Ring ``?1-?2``; 
      (Match Context With
      | [ |- ``-1+?<>0`` ] -> 
        Repeat Rewrite <- Ropp_distr1;Apply Ropp_neq
      | _ -> Idtac);Apply Rgt_not_eq;Sup0.
