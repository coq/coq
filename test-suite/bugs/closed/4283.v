Require Import Hurkens.

Polymorphic Record box (X : Type) (T := Type) : Type := wrap { unwrap : T }.

Definition unwrap' := fun (X : Type) (b : box X) => let (unwrap) := b in unwrap.

Fail Definition bad : False := TypeNeqSmallType.paradox (unwrap' Type (wrap _ Type)) eq_refl.

