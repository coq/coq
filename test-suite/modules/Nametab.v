Mod M.
  Definition id:=[x:Set]x.
  Mod M.
    Definition zero:(id nat):= O.
    Definition id:=Set.
    Definition nacik:id:=nat.
  EndM M.
EndM M.

Mod M.
Mod N.
Mod K.
Definition id:=Set.
EndM K.
EndM N.
EndM M.


Locate id.
Locate K.id.
Locate N.K.id.
Locate M.N.K.id.
Locate Scratch.M.N.K.id.
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

Mod M.
Mod M[X:SIG].
Mod M[X,Y:SIG].
Mod M[X:SIG;Y:SIG].
Mod M[X,Y:SIG;X,Z:SIG].
Mod M[X:SIG][Y:SIG].
Mod M[X,Y:SIG][X,Z:SIG].
Mod M:SIG.
Mod M[X:SIG]:SIG.
Mod M[X,Y:SIG]:SIG.
Mod M[X:SIG;Y:SIG]:SIG.
Mod M[X,Y:SIG;X,Z:SIG]:SIG.
Mod M[X:SIG][Y:SIG]:SIG.
Mod M[X,Y:SIG][X,Z:SIG]:SIG.
Mod M:=(M N).
Mod M[X:SIG]:=(M N).
Mod M[X,Y:SIG]:=(M N).
Mod M[X:SIG;Y:SIG]:=(M N).
Mod M[X,Y:SIG;X,Z:SIG]:=(M N).
Mod M[X:SIG][Y:SIG]:=(M N).
Mod M[X,Y:SIG][X,Z:SIG]:=(M N).
Mod M:SIG:=(M N).
Mod M[X:SIG]:SIG:=(M N).
Mod M[X,Y:SIG]:SIG:=(M N).
Mod M[X:SIG;Y:SIG]:SIG:=(M N).
Mod M[X,Y:SIG;X,Z:SIG]:SIG:=(M N).
Mod M[X:SIG][Y:SIG]:SIG:=(M N).
Mod M[X,Y:SIG][X,Z:SIG]:SIG:=(M N).


Modtype SIG.
  Parameter A:Set.
  Parameter x:A.
EndT SIG.

Mod Nat.
    Definition A:=nat.
    Definition x:=O.
EndM Nat. 

Mod List[X:SIG].
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

EndM List.

Mod N:=(List Nat).
