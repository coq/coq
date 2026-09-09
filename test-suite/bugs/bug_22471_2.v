Module Type T. Parameter l : bool. End T.
Module F (X : T). Module Sub. Include X. End Sub. End F.
Module N.
  Definition l := true.
  Include F.      (* Include Self: X := N, so N.Sub.l ↦ N.l *)
  Fail Include Sub.    (* ground include: kn_to = N.l = kn_canonical *)
End N.
