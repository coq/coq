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
  | [R0] -> Idtac
  | [R1] -> Idtac
  | [(Rplus ?1 ?2)] -> (Isrealint ?1);(Isrealint ?2)
  | [(Rminus ?1 ?2)] -> (Isrealint ?1);(Isrealint ?2)
  | [(Rmult ?1 ?2)] -> (Isrealint ?1);(Isrealint ?2)
  | [(Ropp ?1)] -> (Isrealint ?1)
  | _ -> Fail.


Tactic Definition Sup0 :=
  Match Context With
  | [ |- (Rgt R1 R0) ] -> Unfold Rgt;Apply Rlt_R0_R1
  | [ |- (Rgt (Rplus R1 ?1) R0) ] ->
    Apply (Rgt_trans (Rplus R1 ?1) ?1 R0);
    [Pattern 1 (Rplus R1 ?1);Rewrite Rplus_sym;Unfold Rgt;
     Apply Rlt_r_r_plus_R1
    |Sup0].

Tactic Definition DiscrR :=
  Match Context With
  | [ |- ~R1==R0 ] -> Red;Intro;Apply R1_neq_R0;Assumption
  | [ |- ~((Rplus R1 ?1)==R0) ] -> (Isrealint ?1);Apply Rgt_not_eq;Sup0
  | [ |- ~(Ropp ?1)==R0 ] -> (Isrealint ?1);Apply Ropp_neq; DiscrR
  | [ |- ~(?1==?1) ] -> ElimType False
  | [ |- ~(Rminus R0 ?1)==R0 ] -> (Isrealint ?1);Rewrite Rminus_Ropp; DiscrR
  | [ |- ~(?1==?2) ] -> ((Isrealint ?1);(Isrealint ?2);
    Apply Rminus_not_eq; Ring (Rminus ?1 ?2); 
      (Match Context With
      | [ |- ~(Rplus (Ropp R1) ?)==R0 ] -> 
        Repeat Rewrite <-Ropp_distr1; DiscrR
      | [ |- ? ] -> DiscrR)
     Orelse (Apply Rminus_not_eq_right; DiscrR)).
  


