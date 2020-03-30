Module NoConv.
  Class C := {}.

  Definition useC {c:C} := nat.

  Inductive foo {a b : C} := CC : useC -> foo.
  (* If TC search runs before parameter unification it will pick the
     wrong instance for the first parameter.

     useC makes sure we don't completely skip TC search.
   *)
End NoConv.

Module ForConv.

  Class Bla := { bla : Type }.

  Instance bli : Bla := { bla := nat }.

  Inductive vs := C : forall x : bla, x = 2 -> vs.
  (* here we need to resolve TC to pass the conversion problem if we
     combined with the previous example it would fail as TC resolution
     for conversion is unrestricted and so would resolve the
     conclusion too early. *)

End ForConv.
