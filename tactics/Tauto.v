(***********************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team    *)
(* <O___,, *        INRIA-Rocquencourt  &  LRI-CNRS-Orsay              *)
(*   \VV/  *************************************************************)
(*    //   *      This file is distributed under the terms of the      *)
(*         *       GNU Lesser General Public License Version 2.1       *)
(***********************************************************************)

(* $Id$ *)

Declare ML Module "tauto".

Grammar tactic simple_tactic: ast :=
  tauto [ "Tauto" ] -> [(Tauto)]
| intuition [ "Intuition" ] -> [(Intuition)]
| intuition_t [ "Intuition" tactic($t) ] -> [(Intuition (TACTIC $t))]
.

Syntax tactic level 0:
  tauto [(Tauto)] -> ["Tauto"]
| intuition [(Intuition)] -> ["Intuition"]
| intuition_t [<<(Intuition (TACTIC $t))>>] -> ["Intuition " $t].
