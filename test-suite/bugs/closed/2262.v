

Generalizable Variables A.
Class Test A := { test : A }.

Lemma mylemma : forall `{Test A}, test = test.
Admitted. (* works fine *)

Definition mylemma' := forall `{Test A}, test = test.
About mylemma'.

