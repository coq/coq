(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(*i      $Id$       i*)

Require Rbasic_fun.

Tactic Definition SplitAbs :=
  Match Context With
    | [ |- [(case_Rabsolu ?1)] ] -> 
         Case (case_Rabsolu ?1); Try SplitAbs.


Tactic Definition SplitAbsolu :=
  Match Context With
    | [ id:[(Rabsolu ?)] |- ? ] -> Generalize id; Clear id;Try SplitAbsolu
    | [ |- [(Rabsolu ?1)] ] ->  Unfold Rabsolu; Try SplitAbs;Intros.
