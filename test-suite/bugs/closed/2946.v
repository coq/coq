Lemma toto (E : nat -> nat -> Prop) (x y : nat)  
  (Ex_ : forall z, E x z) (E_y : forall z, E z y) : True.

(* OK *)                                                                     
assert (pairE1 := let Exy := _ in (Ex_ y, E_y _) : Exy * Exy).               

(* FAIL *)                                                                   
assert (pairE2 := let Exy := _ in (Ex_ _, E_y x) : Exy * Exy).
