Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).


Type <(List nat)>Cases (Nil nat) of 
                NIL   => NIL
              | (CONS _ _)  => NIL

              end.

