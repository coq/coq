Module Type T.
Axiom A : Type.
End T.

Module M.
  Axiom A : SProp.
End M.
Fail Module N <: T := M.
