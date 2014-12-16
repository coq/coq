Require Import TestSuite.admit.

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) :=
  (tryif tac then fail 0 tac "succeeds" else idtac); (* error if the tactic solved all goals *) [].

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) := tryif not tac then fail 0 tac "fails" else idtac.

Goal Set.
Proof.
  not fail.
  not not idtac.
  not fail 0.
  (** Would be nice if we could get [not fail 1] to pass, maybe *)
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
  (* would be nice, perhaps, if we could catch [fail 1] and not just [fail 0] this *)
  try ((test fail); fail 1).
  assert True.
  all:test idtac.
  all:test admit.
  2:test admit.
  all:admit.
Defined.
