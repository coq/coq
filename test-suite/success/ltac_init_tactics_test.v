Require Import Coq.Init.Tactics.

Goal Set.
Proof.
  test idtac.
  test try fail.
  test admit.
  test match goal with |- Set => idtac end.
  test (idtac; match goal with |- Set => idtac end).
  (* test grouping *)
  first [ (test idtac; fail); fail 1 | idtac ].
  try test fail.
  try test test fail.
  test test idtac.
  test test admit.
  Fail test fail.
  test (idtac; []).
  test (assert True; [|]).
  try ((test fail 1); fail 1).
  assert True.
  all:test idtac.
  all:test admit.
  2:test admit.
  all:admit.
Defined.
