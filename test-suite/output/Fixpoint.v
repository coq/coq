Require PolyList.

Check Fix F { F/4 : (A,B:Set)(A->B)->(list A)->(list B) :=
 [_,_,f,l]Cases l of
   nil => (nil ?)
 | (cons a l) => (cons (f a) (F ? ? f l))
 end}.
