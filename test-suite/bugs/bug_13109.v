Require Import Corelib.Program.Tactics.

Set Universe Polymorphism.
Obligation Tactic := idtac.

Program Definition foo : Type := _.
Program Definition bar : Type := _.
Admit Obligations.
(* Error: Anomaly "Uncaught exception AcyclicGraph.Make(Point).AlreadyDeclared."
Please report at http://coq.inria.fr/bugs/.
 *)
Print foo.
Print foo_obligation_1.
Print bar.
Print bar_obligation_1.

Program Definition baz : Type := _.
Admit Obligations of baz.
Print baz.
Print baz_obligation_1.

Admit Obligations.

Fail Admit Obligations of nobody.
