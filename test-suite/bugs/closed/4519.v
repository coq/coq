Set Universe Polymorphism.
Section foo.
  Universe i.
  Context (foo : Type@{i}) (bar : Type@{i}).
  Definition qux@{i} (baz : Type@{i}) := foo -> bar.
End foo.
Set Printing Universes.
Print qux. (* qux@{Top.42 Top.43} =
fun foo bar _ : Type@{Top.42} => foo -> bar
     : Type@{Top.42} -> Type@{Top.42} -> Type@{Top.42} -> Type@{Top.42}
(* Top.42 Top.43 |=  *)
(* This is wrong; the first two types are equal, but the last one is not *)

qux is universe polymorphic
Argument scopes are [type_scope type_scope type_scope]
 *)
Check qux nat nat nat : Set.
Check qux nat nat Set : Set. (* Error:
The term "qux@{Top.50 Top.51} ?T ?T0 Set" has type "Type@{Top.50}" while it is 
expected to have type "Set"
(universe inconsistency: Cannot enforce Top.50 = Set because Set < Top.50). *)
