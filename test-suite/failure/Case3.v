Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).

Type [l:(List nat)]<nat>Cases l of 
                         (Nil nat) =>O
                      | (Cons  a l) => (S a)
                      end.
