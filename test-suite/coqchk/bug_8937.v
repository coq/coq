(* -*- coq-prog-args: ("-noinit"); -*- *)

Unset Elimination Schemes.
Module Type S.

Inductive foo : Prop :=.
Definition bar (x:foo) : Prop := match x with end.

End S.

Module M.

Inductive foo : Prop :=.
Definition bar (x:foo) : Prop := match x with end.

End M.

Module MS : S := M.

Module F (Z:S) := Z.
Module MS' : S := F M.
