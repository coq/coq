
Universes i j k l.

Definition foo : Type@{j} := Type@{i}.

Definition baz : Type@{k} := Type@{l}.

Print Universes Subgraph(i j).
(* should print [i < j], not [l < k] (and not prelude universes) *)

Definition connect : Type@{l} := Type@{j}.

Print Universes Subgraph (i k).

Universes u v.
Module Type T.
  Definition foo : Type@{u} := Type@{v}.
End T.

Print Universes Subgraph (u v).
(* T.foo does not exist but we don't fail *)
