Module Type T.
  Parameter bad : False.
End T.

Module M : T.
  Axiom x : False. (* x was not reported *)
  Inductive TT :Prop := tt (y:=x).

  Definition bad := match tt with tt y => y end.
End M.
