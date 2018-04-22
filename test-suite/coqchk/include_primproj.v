(* #7329 *)
Set Primitive Projections.

Module M.
  Module Bar.
    Record Box := box { unbox : Type }.

    Axiom foo : Box.
    Axiom baz : forall _ : unbox foo, unbox foo.
  End Bar.
End M.

Include M.
