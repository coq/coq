Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).

Definition NIL := (Nil nat).
Type <(List nat)>Cases (Nil nat) of 
                NIL   => NIL
              |  _    => NIL
              end.
