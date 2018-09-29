(* Bug #2169 *)

Module FOO.

Module M.
 Definition T := nat.
End M.

Module Type S.
 Parameter T : Set.
End S.

Module N : S with Definition T := nat := M.

Print Module N.

Set Short Module Printing.
Print Module N.
Unset Short Module Printing.

End FOO.

Module BAR.

Module K. End K.
Module Type KS. End KS.

Module M.
 Module T := K.
End M.

Module Type S.
 Declare Module T : KS.
End S.

Module N : S with Module T := K := M.

Print Module N.

Set Short Module Printing.
Print Module N.
Unset Short Module Printing.

End BAR.

(* Bug #4661 *)

Module QUX.

Module Type Test.
  Parameter t : Type.
End Test.

Module Type Func (T:Test).
  Parameter x : T.t.
End Func.

Module Shortest_path (T : Test).
Print Func.
End Shortest_path.

End QUX.
