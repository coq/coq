
Set Implicit Arguments.
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.
Goal forall x y : prod Set Set, fst x = fst y.
  intros.
  lazymatch goal with
    | [ |- context[@fst ?A ?B] ] => pose (@fst A B) as fst';
                                   progress change (@fst Set Set) with fst'
end.
Abort.
