Set Implicit Arguments.
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.

Fail Goal forall x y : prod Set Set, x.(@fst) = y.(@fst).
(*  intros.
    apply f_equal. *)
