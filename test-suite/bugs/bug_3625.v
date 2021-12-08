Require Import TestSuite.admit.
Set Implicit Arguments.
Set Primitive Projections.
Record prod A B := pair { fst : A ; snd : B }.

Goal forall x y : prod Set Set, x.(@fst _ _) = y.(@fst _ _).
 intros.
 refine (f_equal _ _).
 Undo.
 apply f_equal.
 admit.
Qed.
