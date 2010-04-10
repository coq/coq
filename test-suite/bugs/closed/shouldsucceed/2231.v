Inductive unit2 : Type := U : unit -> unit2.
Inductive dummy (u: unit2) : unit -> Type :=
          V: dummy u (let (tt) := u in tt).
