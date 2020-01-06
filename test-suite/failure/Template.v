
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

  About myind.

  (* test discharge puts things in the right order (by using the
     checker on the result) *)
  Section S.

    Variables (A:Type) (a:A).
    Inductive bb (B:Type) := BB : forall a', a = a' -> B -> bb B.
  End S.

End TestUnsetTemplateCheck.
