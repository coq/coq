Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).

Type <nat>Cases (Nil nat) of 
                             ((Nil_) as b) =>b
                            |((Cons _ _ _) as d) => d
                      end.

