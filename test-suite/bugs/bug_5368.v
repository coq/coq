Set Universe Polymorphism.

Record cantype := {T:Type; op:T -> unit}.
Canonical Structure test (P:Type) := {| T := P -> Type; op := fun _ => tt|}.

Check (op _ ((fun (_:unit) => Set):_)).
