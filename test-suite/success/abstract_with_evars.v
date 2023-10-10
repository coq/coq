
Goal unit.
  let x := open_constr:(_) in
  let _ := open_constr:(eq_refl : x = tt) in
  abstract (exact x).
Qed.

Goal unit.
  let x := open_constr:(_) in
  let tac := exact x in (* <- this is a closure *)
  let _ := open_constr:(eq_refl : x = tt) in
  abstract tac.
Qed.

Goal unit.
  Fail let x := open_constr:(_) in
       abstract exact x.
Abort.

Require Import Ltac2.Ltac2.

Goal unit.
  let x := '_ in
  let _ := '(eq_refl : $x = tt) in
  abstract (exact $x).
Qed.

Goal unit.
  let x := '_ in
  let tac () := exact $x in
  let _ := '(eq_refl : $x = tt) in
  abstract (tac ()).
Qed.
