(* Outside a section, Hypothesis, Variable, Axiom all obey implicit binders *)
Axiom foo1 : forall {n : nat}, True.
Parameter foo1' : forall {n : nat}, True.
Axiom foo1'' : forall {n : nat}, True.
Check foo1 (n := 1).
Check foo1' (n := 1).
Check foo1'' (n := 1).

Section bar.
(* Inside a section, Hypothesis and Variable do not, but they should *)
Hypothesis foo2 : forall {n : nat}, True.
Variable foo2' : forall {n : nat}, True.
Axiom foo2'' : forall {n : nat}, True.
Check foo2 (n := 1).
Check foo2' (n := 1).
Check foo2'' (n := 1).
End bar.
