(* Teste des definitions inductives imbriquees *)

Require PolyList.

Inductive X : Set := 
    cons1 : (list X)->X.

Inductive Y : Set := 
    cons2 : (list Y*Y)->Y.

