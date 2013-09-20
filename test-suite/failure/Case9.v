Parameter compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Fail Type
  match compare 0 0 return nat with

      (* k<i *) | left _ (left _ _) => 0
   (* k=i *) | left _ _ => 0
   (* k>i *) | right _ _ => 0
  end.
