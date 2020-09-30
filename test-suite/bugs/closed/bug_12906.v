

Set Printing Universes. Set Printing All. Set Universe Polymorphism.

Definition foo@{a b +} (X:=_) (a:(Type@{a}:X)) (b:(Type@{b}:X)) := 0.
Print foo.

(* a and b are not ordered *)
Definition foo1@{a b+| a < b +} := foo@{a b _ _}.
Definition foo2@{a b+| b < a +} := foo@{a b _ _}.

Definition bar@{a+} (X:=_) (a:(Type@{a}:X)) (b:(nat:X)) := 0.
Check bar@{Set _ _}.

Definition baz@{b+} (X:=_) (a:(nat:X)) (b:(Type@{b}:X)) := 0.
Check baz@{Set _ _}.
