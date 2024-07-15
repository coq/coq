Set Universe Polymorphism.
Primitive array@{u} : Type@{u} -> Type@{u} := #array_type.
Fail Print Universes Subgraph (Top.array.u).
(* Was: Anomaly "Uncaught exception Not_found." in coqtop *)
