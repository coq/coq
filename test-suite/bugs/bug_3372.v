Set Universe Polymorphism.
Definition hProp@{u} : Type@{u+1} := sigT (fun _ : Type@{u} => True).
Goal Type.
exact hProp@{0}.
Abort.
