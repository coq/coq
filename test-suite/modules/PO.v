Implicit Arguments On.

Implicits fst.
Implicits snd.

Module Type PO.
  Parameter T:Set.
  Parameter le:T->T->Prop.
  
  Axiom le_refl : (x:T)(le x x).
  Axiom le_trans : (x,y,z:T)(le x y) -> (le y z) -> (le x z).
  Axiom le_antis : (x,y:T)(le x y) -> (le y x) -> (x=y).
  
  Hints Resolve le_refl le_trans le_antis.
End PO.


Module Pair[X:PO][Y:PO].
  Definition T:=X.T*Y.T.
  Definition le:=[p1,p2]
    (X.le (fst p1) (fst p2)) /\ (Y.le (snd p1) (snd p2)).

  Hints Unfold le.

  Lemma le_refl : (p:T)(le p p).
  Auto.
  Save.

  Lemma le_trans : (p1,p2,p3:T)(le p1 p2) -> (le p2 p3) -> (le p1 p3).
    Unfold le.
    Intuition; EAuto.
  Save.    

  Lemma le_antis : (p1,p2:T)(le p1 p2) -> (le p2 p1) -> (p1=p2).
    NewDestruct p1.  
    NewDestruct p2.
    Unfold le.
    Intuition.
    Cut t=t1;Auto.
    Cut t0=t2;Auto.
    Intros.
    Rewrite H0.
    Rewrite H4.
    Reflexivity.
  Save.

  Hints Resolve le_refl le_trans le_antis.

End Pair.

Module Check_Pair [X:PO][Y:PO] : PO := (Pair X Y).


Module Type Fmono.
  Module X:PO.
  Module Y:PO.

  Parameter f : X.T -> Y.T.
  
  Axiom f_mono : (x1,x2:X.T)(X.le x1 x2) -> (Y.le (f x1) (f x2)).
End Fmono.


Read Module Nat.


Module PlusMono:Fmono.
  Module Y:=Nat.
  Module X:=Pair Nat Nat.
  
  Definition f:=[p] (plus (fst p) (snd p)).

  Lemma f_mono : (p1,p2:nat*nat)(X.le p1 p2) -> (le (f p1) (f p2)).
    NewDestruct p1;NewDestruct p2.
    Unfold X.le Nat.le f.
    Simpl.
    NewDestruct 1.
    Induction H.
  
    Induction n.
    Auto.
    Simpl.
    Apply Nat.le_mono_S.
    Auto.

    Simpl.
    Auto.
  Save.
End PlusMono.
