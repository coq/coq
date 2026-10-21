Set Universe Polymorphism.
Inductive foo@{s;} : Univ@{s;0} := XX.

Fail Fixpoint bar@{s;|} (f:foo@{s;}) : True := I.
