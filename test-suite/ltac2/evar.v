Require Import Ltac2.Ltac2.

Goal exists (a: nat), a = 1.
Proof.
  match! goal with
  | [ |- ?g ] => Control.assert_false (Constr.has_evar g)
  end.
  eexists.
  match! goal with
  | [ |- ?g ] => Control.assert_true (Constr.has_evar g)
  end.
  match! goal with
  | [ |- ?x = ?y ] =>
    Control.assert_true (Constr.is_evar x);
    Control.assert_false (Constr.is_evar y)
  end.
Abort.
