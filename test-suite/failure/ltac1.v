(* Check all variables are different in a Context *)
Tactic Definition X := Match Context With [ x:?; x:? |- ? ] -> Apply x.
Goal True->True->True.
Intros.
X.
