
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
