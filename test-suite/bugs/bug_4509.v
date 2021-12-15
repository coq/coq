(* Was solved at some time, suspectingly in PR #6328 *)

Goal exists n, n > 1.
Proof.
  unshelve eexists. (*2 goals, as expected*)
  Undo.
  unshelve (eexists; instantiate (1:=ltac:(idtac))). (*only 1 goal*)
  shelve.
  Undo.
  2:unshelve instantiate (1:=_).
Abort.
