
(* $Id$ *)

Declare ML Module "Tauto".

Grammar tactic simple_tactic: Ast :=
  tauto [ "Tauto" ] -> [(Tauto)]
| intuition [ "Intuition" ] -> [(Intuition)].

Syntax tactic level 0:
  tauto [(Tauto)] -> ["Tauto"]
| intuition [(Intuition)] -> ["Intuition"].
