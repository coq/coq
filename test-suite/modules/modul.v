Mod M.
  Parameter rel:nat -> nat -> Prop.

  Axiom w : (n:nat)(rel O (S n)).

  Hints Resolve w.

  Grammar constr constr8 := 
     not_eq [ constr7($a) "#" constr7($b) ] -> [ (rel $a $b) ].
  
  Print Hint *.

  Lemma w1 : (O#(S O)).
  Auto.
  Save.

EndM M.

(*Lemma w1 : (M.rel O (S O)).
Auto.
*)

Imp M.

Print Hint *.
Lemma w1 : (O#(S O)).
Print Hint.
Print Hint *.

Auto.
Save.

Check (O#O).
Locate rel.

Locate M.

Mod N:=Scratch.M.

