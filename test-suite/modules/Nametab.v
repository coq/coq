Module Q.
Module N.
Module K.
Definition id:=Set.
End K.
End N.
End Q.

Locate id.
Locate K.id.
Locate N.K.id.
Locate Q.N.K.id.
Locate Top.Q.N.K.id.
Locate K.
Locate N.K.
Locate Q.N.K.
Locate Top.Q.N.K.
Locate N.
Locate Q.N.
Locate Top.Q.N.
Locate Q.
Locate Top.Q.


Module Type SIG.
End SIG.

Module Type FSIG[X:SIG].
End FSIG.

Module F[X:SIG].
End F.

(*
#trace Nametab.push;;
#trace Nametab.push_short_name;;
#trace Nametab.freeze;;
#trace Nametab.unfreeze;;
#trace Nametab.exists_cci;;
*)

Module M.
Reset M.
Module M[X:SIG].
Reset M.
Module M[X,Y:SIG].
Reset M.
Module M[X:SIG;Y:SIG].
Reset M.
Module M[X,Y:SIG;Z1,Z:SIG].
Reset M.
Module M[X:SIG][Y:SIG].
Reset M.
Module M[X,Y:SIG][Z1,Z:SIG].
Reset M.
Module M:SIG.
Reset M.
Module M[X:SIG]:SIG.
Reset M.
Module M[X,Y:SIG]:SIG.
Reset M.
Module M[X:SIG;Y:SIG]:SIG.
Reset M.
Module M[X,Y:SIG;Z1,Z:SIG]:SIG.
Reset M.
Module M[X:SIG][Y:SIG]:SIG.
Reset M.
Module M[X,Y:SIG][Z1,Z:SIG]:SIG.
Reset M.
Module M:=(F Q).
Reset M.
Module M[X:FSIG]:=(X Q).
Reset M.
Module M[X,Y:FSIG]:=(X Q).
Reset M.
Module M[X:FSIG;Y:SIG]:=(X Y).
Reset M.
Module M[X,Y:FSIG;Z1,Z:SIG]:=(X Z).
Reset M.
Module M[X:FSIG][Y:SIG]:=(X Y).
Reset M.
Module M[X,Y:FSIG][Z1,Z:SIG]:=(X Z).
Reset M.
Module M:SIG:=(F Q).
Reset M.
Module M[X:FSIG]:SIG:=(X Q).
Reset M.
Module M[X,Y:FSIG]:SIG:=(X Q).
Reset M.
Module M[X:FSIG;Y:SIG]:SIG:=(X Y).
Reset M.
Module M[X,Y:FSIG;Z1,Z:SIG]:SIG:=(X Z).
Reset M.
Module M[X:FSIG][Y:SIG]:SIG:=(X Y).
Reset M.
Module M[X,Y:FSIG][Z1,Z:SIG]:SIG:=(X Z).
Reset M.


Module Type ELEM.
  Parameter A:Set.
  Parameter x:A.
End ELEM.

Module Nat.
    Definition A:=nat.
    Definition x:=O.
End Nat. 

Module List[X:ELEM].
  Inductive list : Set := nil : list 
		       | cons : X.A -> list -> list.
 
  Definition head := 
     [l:list]Cases l of 
	  nil => X.x 
	| (cons x _) => x
     end.

  Definition singl := [x:X.A] (cons x nil).
  
  Lemma head_singl : (x:X.A)(head (singl x))=x.
  Auto.
  Qed.

End List.

Module N:=(List Nat).
