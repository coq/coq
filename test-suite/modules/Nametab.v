Module M.
  Definition id:=[x:Set]x.
  Module M.
    Definition zero:(id nat):= O.
    Definition id:=Set.
    Definition nacik:id:=nat.
  End M.
End M.

Module M.
Module N.
Module K.
Definition id:=Set.
End K.
End N.
End M.


Locate id.
Locate K.id.
Locate N.K.id.
Locate M.N.K.id.
Locate Top.M.N.K.id.
Locate K.
Locate N.K.
Locate M.N.K.
Locate Scratch.M.N.K.
Locate N.
Locate M.N.
Locate Scratch.M.N.
Locate M.
Locate Scratch.M.

(*
#trace Nametab.push;;
#trace Nametab.push_short_name;;
#trace Nametab.freeze;;
#trace Nametab.unfreeze;;
#trace Nametab.exists_cci;;
*)

Module M.
Module M[X:SIG].
Module M[X,Y:SIG].
Module M[X:SIG;Y:SIG].
Module M[X,Y:SIG;X,Z:SIG].
Module M[X:SIG][Y:SIG].
Module M[X,Y:SIG][X,Z:SIG].
Module M:SIG.
Module M[X:SIG]:SIG.
Module M[X,Y:SIG]:SIG.
Module M[X:SIG;Y:SIG]:SIG.
Module M[X,Y:SIG;X,Z:SIG]:SIG.
Module M[X:SIG][Y:SIG]:SIG.
Module M[X,Y:SIG][X,Z:SIG]:SIG.
Module M:=(M N).
Module M[X:SIG]:=(M N).
Module M[X,Y:SIG]:=(M N).
Module M[X:SIG;Y:SIG]:=(M N).
Module M[X,Y:SIG;X,Z:SIG]:=(M N).
Module M[X:SIG][Y:SIG]:=(M N).
Module M[X,Y:SIG][X,Z:SIG]:=(M N).
Module M:SIG:=(M N).
Module M[X:SIG]:SIG:=(M N).
Module M[X,Y:SIG]:SIG:=(M N).
Module M[X:SIG;Y:SIG]:SIG:=(M N).
Module M[X,Y:SIG;X,Z:SIG]:SIG:=(M N).
Module M[X:SIG][Y:SIG]:SIG:=(M N).
Module M[X,Y:SIG][X,Z:SIG]:SIG:=(M N).


Moduletype SIG.
  Parameter A:Set.
  Parameter x:A.
EndT SIG.

Module Nat.
    Definition A:=nat.
    Definition x:=O.
End Nat. 

Module List[X:SIG].
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
