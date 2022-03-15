Axiom f : forall {A}, option (option A) -> list A.
Coercion f : option >-> list.
Check (Some (Some 0) : list nat).
