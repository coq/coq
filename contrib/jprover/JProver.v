Declare ML Module "opname" "jterm" "jlogic" "jtunify" "jall" "jprover".

Grammar tactic simple_tactic: ast :=
   jprover0 [ "Jp" ] -> [ (Jp) ]
 | jprover1 [ "Jp" pure_numarg($num)] -> [ (Jpn $num) ].

Syntax tactic level 0:
 | jprover0 [<<(Jp)>>] -> ["Jp"]
 | jprover1 [<<(Jp $num)>>] -> ["Jp " $num].

(*
Grammar tactic simple_tactic: ast :=
  jprover [ "Andl" identarg($id)] -> [ (Andl $id) ].
*)
