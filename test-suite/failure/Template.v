(*
Module TestUnsetTemplateCheck.
  Unset Template Check.

  Section Foo.

    Context (A : Type).

    Definition cstr := nat : ltac:(let ty := type of A in exact ty).

    Inductive myind :=
    | cons : A -> myind.
  End Foo.

  (* Can only succeed if no template check is performed *)
  Check myind True : Prop.

  Print Assumptions myind.
  (*
  Axioms:
  myind is template polymorphic on all its universe parameters.
   *)
  About myind.
(*
myind : Type@{Top.60} -> Type@{Top.60}

myind is assumed template universe polymorphic on Top.60
Argument scope is [type_scope]
Expands to: Inductive Top.TestUnsetTemplateCheck.myind
*)
End TestUnsetTemplateCheck.
*)
