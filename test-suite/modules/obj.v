Implicit Arguments On.

Mod M. 
  Definition a:=[s:Set]s.
  Print a.
EndM M.

Print M.a.

Mod K.
  Definition app:=[A,B:Set; f:(A->B); x:A](f x).
  Mod N.
    Definition apap:=[A,B:Set](app (app 1!A 2!B)).
    Print app.
    Print apap.
  EndM N.
  Print N.apap.
EndM K.

Print K.app.
Print K.N.apap.

Mod W:=K.N.

Print W.apap.

