Set Universe Polymorphism.

(** Check that variance subtyping is respected. The signature T is asking for
    invariance, while M provide an irrelevant implementation, which is deemed
    legit.

    There is currently no way to go the other way around, so it's not possible
    to generate a counter-example that should fail with the wrong subtyping.
*)

Module Type T.
Parameter t@{i|Set <= i} : Type@{i}.
Cumulative Inductive I@{i|Set <= i} : Type@{i} := C : t@{i} -> I.
End T.

Module M : T.
Definition t@{i|Set <= i} : Type@{i} := nat.
Cumulative Inductive I@{i|Set <= i} : Type@{i} := C : t@{i} -> I.
End M.
