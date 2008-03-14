Parameter ff : forall n m : nat, n <> m -> S n <> S m.
Parameter discr_r : forall n : nat, 0 <> S n.
Parameter discr_l : forall n : nat, S n <> 0.

Fixpoint eqdec (n m : nat) {struct n} : n = m \/ n <> m :=
  match n, m return (n = m \/ n <> m) with
  | O, O => or_introl (0 <> 0) (refl_equal 0)
  | O, S x => or_intror (0 = S x) (discr_r x)
  | S x, O => or_intror _ (discr_l x)
  | S x as N, S y as M =>
      match eqdec x y return (N = M \/ N <> M) with
      | or_introl h => or_introl (N <> M) (f_equal S h)
      | or_intror h => or_intror (N = M) (ff x y h)
      end
  end.
