Ltac foo :=
  let x := open_constr:(ltac:(exact 0)) in
  idtac x.

Print foo.

Require Import Ltac2.Ltac2.

Ltac2 bar () :=
  let _ := open_constr:(ltac2:(exact 0)) in
  ().

Print bar.
