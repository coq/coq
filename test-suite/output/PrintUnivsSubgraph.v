
Universes i j k l.

Definition foo : Type@{j} := Type@{i}.

Definition baz : Type@{k} := Type@{l}.

Print Universes Subgraph(i j).
(* should print [i < j], not [l < k] (and not prelude universes) *)
