Tactic Notation "foo" hyp_list(hs) := clear hs.

Tactic Notation "bar" hyp_list(hs) := foo hs.

Goal True.
do 5 pose proof 0 as ?n0.
foo n1 n2.
bar n3 n4.
