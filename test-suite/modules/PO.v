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


Module Pair[X:PO][Y:PO] <: PO.
  Definition T:=X.T*Y.T.
  Definition le:=[p1,p2]
    (X.le (fst p1) (fst p2)) /\ (Y.le (snd p1) (snd p2)).

  Hints Unfold le.

  Lemma le_refl : (p:T)(le p p).
    Info Auto.
  Qed.

  Lemma le_trans : (p1,p2,p3:T)(le p1 p2) -> (le p2 p3) -> (le p1 p3).
    Unfold le; Intuition; Info EAuto.
  Qed.    

  Lemma le_antis : (p1,p2:T)(le p1 p2) -> (le p2 p1) -> (p1=p2).
    NewDestruct p1.  
    NewDestruct p2.
    Unfold le.
    Intuition.
    CutRewrite t=t1.
    CutRewrite t0=t2.
    Reflexivity.

    Info Auto.

    Info Auto.
  Qed.

End Pair.



Read Module Nat.

Module NN := Pair Nat Nat.

Lemma zz_min : (p:NN.T)(NN.le (O,O) p).
  Info Auto with arith.
Qed.
