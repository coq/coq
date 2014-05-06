Record PreCategory :=  Build_PreCategory' { object :> Type }.
Class Foo (X : Type) := {}.
Class Bar := {}.
Definition functor_category `{Bar} (C D : PreCategory)  `{Foo (object D)} : PreCategory.
Admitted.
Fail Definition functor_object_of `{Bar} (C1 C2 D : PreCategory) `{Foo (object D)}
: functor_category C1 (functor_category C2 D) -> True.
(** Anomaly: File "toplevel/himsg.ml", line ..., characters ...: Assertion failed.
Please report. *)
