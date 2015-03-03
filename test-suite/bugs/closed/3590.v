(* Set Primitive Projections. *)
Set Implicit Arguments.
Record prod A B := pair { fst : A ; snd : B }.
Definition idS := Set.
Goal forall x y : prod Set Set, fst x = fst y.
  intros.
  change (@fst _ _ ?z) with (@fst Set idS z) at 2.
  Unshelve.
  admit.
Qed.
  
(* Toplevel input, characters 20-58:
Error: Failed to get enough information from the left-hand side to type the
right-hand side. *)