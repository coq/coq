Module Type SIG.
  Definition A:Set. (*error*)
  Axiom A:Set.
End SIG.

Module M0.
  Definition A:Set.
  Exact nat.
  Save.
End M0.

Module M1:SIG.
  Definition A:=nat.
End M1.

Module M2<:SIG.
  Definition A:=nat.
End M2.

Module M3:=M0.

Module M4:SIG:=M0.

Module M5<:SIG:=M0.


Module F[X:SIG]:=X.


Declare Module M6.


Module Type T.

  Declare Module M0.
    Lemma A:Set (*error*).
    Axiom A:Set.
  End M0.
  
  Declare Module M1:SIG.
  
  Declare Module M2<:SIG.
    Definition A:=nat.
  End M2.
  
  Declare Module M3:=M0.
  
  Declare Module M4:SIG:=M0.  (* error *)
  
  Declare Module M5<:SIG:=M0.

  Declare Module M6:=F M0. (* error *)

  Module M7.
End T.