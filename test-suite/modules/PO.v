

Implicits fst.
Implicits snd.

Modtype PO.
  Parameter T:Set.
  Parameter le:T->T->Prop.
  
  Axiom le_refl : (x:T)(le x x).
  Axiom le_trans : (x,y,z:T)(le x y) -> (le y z) -> (le x z).
  Axiom le_antis : (x,y:T)(le x y) -> (le y x) -> (x=y).
  
  Hints Resolve le_refl le_trans le_antis.
EndT PO.


Mod Pair[X:PO][Y:PO].

  Check X.T.
  Definition T:=X.T*Y.T.
  Definition le:=[p1,p2]
    (X.le (fst p1) (fst p2)) /\ (Y.le (snd p1) (snd p2)).

  Hints Unfold le.

  Lemma le_refl : (p:T)(le p p).
    Auto.
  Save.

  Lemma le_trans : (p1,p2,p3:T)(le p1 p2) -> (le p2 p3) -> (le p1 p3).
    NewDestruct p1; NewDestruct p2; NewDestruct p3.
    Unfold le.
    Unfold fst snd.
    Intros (H1,H2).
    Intros (H3,H4). 
    Constructor.   
    EAuto.
    EAuto.

    (* Intuition;EAuto *)
  Save.    

  Lemma le_antis : (p1,p2:T)(le p1 p2) -> (le p2 p1) -> (p1=p2).
    NewDestruct p1.  
    NewDestruct p2.
    Intuition.
    Cut t=t1.
    Cut t0=t2.
    Intros.
    Rewrite H0.
    Rewrite H4.
    Reflexivity.

    Auto.

    Auto.
  Save.

  Hints Resolve le_refl le_trans le_antis.

EndM Pair.

Mod Check_Pair [X:PO][Y:PO] : PO := (Pair X Y).


Modtype Fmono.
  DMod X:PO.
  DMod Y:PO.

  Parameter f : X.T -> Y.T.
  
  Axiom f_mono : (x1,x2:X.T)(X.le x1 x2) -> (Y.le (f x1) (f x2)).
EndT Fmono.


Mod PlusMono.

  Read Module Nat.

  Mod Y:=Nat.
  Mod X:=Pair Nat Nat.
  
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
EndM PlusMono.

Mod CheckPlus : Fmono := PlusMono.
