Parameter compare : forall n m : nat, {n < m} + {n = m} + {n > m}.
Type
  match compare 0 0 return nat with

      (* k<i *) | left _ _ (left _ _ _) => 0
   (* k=i *) | left _ _ _ => 0
   (* k>i *) | right _ _ _ => 0
  end.
