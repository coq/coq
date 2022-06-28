Class Inhabited (A : Type) : Type := populate { inhabitant : A }.

Definition A := 42.

#[export] Instance foo (A: Type): Inhabited (list A).
Check A.
Abort.

Fail #[export] Instance foo (A : nat) (A : Type) : Inhabited nat.
