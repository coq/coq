(* -*- coq-prog-args: ("-compat" "8.4") -*- *)

Goal True.
  solve [ constructor 1 ]. Undo.
  solve [ econstructor 1 ]. Undo.
  solve [ constructor ]. Undo.
  solve [ econstructor ]. Undo.
  solve [ constructor (fail) ]. Undo.
  solve [ econstructor (fail) ]. Undo.
  split.
Qed.

Goal False \/ True.
  solve [ constructor (constructor) ]. Undo.
  solve [ econstructor (econstructor) ]. Undo.
  solve [ constructor 2; constructor ]. Undo.
  solve [ econstructor 2; econstructor ]. Undo.
  right; esplit.
Qed.
