Inductive List [A:Set] :Set := 
 Nil:(List A) | Cons:A->(List A)->(List A).

Inductive Empty [A:Set] : (List A)-> Prop := 
  intro_Empty: (Empty A (Nil A)).

Parameter inv_Empty : (A:Set)(a:A)(x:(List A)) ~(Empty A (Cons A a x)).


Type
[A:Set] 
[l:(List A)]
  <[l:(List A)](Empty A l) \/ ~(Empty A l)>Cases l of 
        Nil  =>  (or_introl ? ~(Empty A (Nil A)) (intro_Empty A))
   |  ((Cons a y) as b) =>  (or_intror (Empty A b) ? (inv_Empty A a y))
  end.
