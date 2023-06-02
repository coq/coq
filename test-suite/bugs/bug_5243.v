Typeclasses eauto := debug.

Class Foo A := foo : A.

Hint Extern 0 (Foo _) => lazy beta delta; give_up : typeclass_instances.

Lemma t A : A.
  notypeclasses refine ((_ : Foo A)).
  typeclasses eauto.

(*
No more subgoals, but there are some goals you gave up:

A

You need to go back and solve them.
*)

Abort.

Lemma t A : A.
  refine ((_ : Foo A)).

(*
1: looking for (Foo A) without backtracking
1.1: (*external*) (lazy beta delta; give_up) on
(Foo A), 0 subgoal(s)
leaking evar 10
A

Anomaly:
File "tactics/class_tactics.ml", line 1345, characters 11-17: Assertion failed.
Please report at http://coq.inria.fr/bugs/.
 *)
  Unshelve.
  all:fail. (* no more goals *)
  Fail Qed.
Abort.
