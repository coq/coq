(* Check cast setting scopes *)
Check nat * nat : Type.
Check 0 * 0 : nat.
Require Import BinNums IntDef.
Infix "*" := Z.mul : Z_scope.
Check Z0 * Z0 : Z.

Declare Scope b_scope.
Definition b := {x:bool|x=true}.
Notation "{ x ; y }" := (exist _ x y) : b_scope.
Fail Check fun '({x;y}:b) => x.
Bind Scope b_scope with b.
Check fun '({x;y}:b) => x.
