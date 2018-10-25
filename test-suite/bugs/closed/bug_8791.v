Class Inhabited (A : Type) : Type := populate { inhabitant : A }.

Definition A := 42.

Instance foo (A: Type): Inhabited (list A).
Check A.
Abort.

Fail Instance foo (A : nat) (A : Type) : Inhabited nat.
