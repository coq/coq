
(* $Id$ *)

Declare ML Module "refine".

Grammar tactic simple_tactic :=
  tcc [ "Refine" castedopenconstrarg($c) ] -> [(Tcc $c)].

Syntax tactic level 0:
  tcc [(Tcc $C)] -> ["Refine " $C].
