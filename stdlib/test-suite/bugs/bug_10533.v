
From Stdlib Require Import Eqdep Setoid.
Goal forall (t : unit) (pf : tt = t),
  if (match pf with eq_refl => false end) then True else False.
Proof.
  intros.
  try setoid_rewrite <-Eqdep.Eq_rect_eq.eq_rect_eq.
Abort.
