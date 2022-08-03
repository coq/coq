Require Import Coq.Program.Basics Coq.Program.Tactics.
Local Obligation Tactic := abstract exact I.
Program Definition foo : True := _.
Print Assumptions foo.
