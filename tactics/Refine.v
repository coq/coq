
(* $Id$ *)

Declare ML Module "refine".

Grammar tactic simple_tactic: ast :=
  tcc [ "Refine" castedopenconstrarg($c) ] -> [(Tcc $c)].

Syntax tactic level 0:
  tcc [ (Refine $C) ] -> ["Refine " $C].
