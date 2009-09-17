Require Import Peano_dec.

Definition fact_F :
  forall (n:nat),
  (forall m, m<n -> nat) ->
  nat.
refine
  (fun n fact_rec =>
     if eq_nat_dec n 0 then
        1
     else
        let fn := fact_rec (n-1) _ in
        n * fn).
Admitted.

