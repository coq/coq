
(* $Id$ *)

Declare ML Module "tauto".

Grammar tactic simple_tactic: ast :=
  tauto [ "Tauto" ] -> [(Tauto)]
| intuition [ "Intuition" ] -> [(Intuition)].

Syntax tactic level 0:
  tauto [(Tauto)] -> ["Tauto"]
| intuition [(Intuition)] -> ["Intuition"].
