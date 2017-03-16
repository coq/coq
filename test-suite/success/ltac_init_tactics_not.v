Require Import Coq.Init.Tactics.

Goal Set.
Proof.
  not fail.
  not not idtac.
  not fail 0.
  not fail 1.
  not fail 2.
  (** Would be nice if we could get [not fail 3] to pass *)
  try ((not fail 3); fail 1).
  not not admit.
  not not test admit.
  not progress test admit.
  (* test grouping *)
  not (not idtac; fail).
  assert True.
  all:not fail.
  2:not fail.
  all:admit.
Defined.
