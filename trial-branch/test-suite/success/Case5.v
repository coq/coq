
Parameter ff : forall n m : nat, n <> m -> S n <> S m.
Parameter discr_r : forall n : nat, 0 <> S n.
Parameter discr_l : forall n : nat, S n <> 0.


Type
  (fun n : nat =>
   match n return (n = 0 \/ n <> 0) with
   | O => or_introl (0 <> 0) (refl_equal 0)
   | S O => or_intror (1 = 0) (discr_l 0)
   | S (S x) => or_intror (S (S x) = 0) (discr_l (S x))
   end).
