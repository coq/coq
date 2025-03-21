Require Import PrimArray.
Require Import PrimInt63.
Goal True.
  let x := open_constr:(get (@make (unit * unit) 1%uint63 (tt,?[u])) 0) in
  let result := eval lazy in x in
  assert_succeeds (idtac; unify x result);
  assert_succeeds (idtac; unify x (tt,tt));
  assert_succeeds (idtac; let t := open_constr:(eq_refl : (x = result)) in idtac);
  assert_succeeds (idtac; let t := open_constr:(eq_refl : (x = (tt,tt))) in idtac).
Abort.
