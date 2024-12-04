(* Check cast setting scopes *)
Check nat * nat : Type@{_}.
Check 0 * 0 : nat.
Require Import ZArith.
Check 0 * 0 : Z.

Declare Scope b_scope.
Definition b := {x:bool|x=true}.
Notation "{ x ; y }" := (exist _ x y) : b_scope.
Require Import Utf8.
Fail Check λ '({x;y}:b), x.
Bind Scope b_scope with b.
Check λ '({x;y}:b), x.
