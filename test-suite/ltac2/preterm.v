Require Import Ltac2.Ltac2.

Ltac2 Eval preterm:(notbound).

Ltac2 Notation "pretermize" t(preterm) := t.

Ltac2 Eval pretermize notbound.

(* this check is intern time *)
Fail Ltac2 Eval pretermize (fun x y : x => x).

Ltac2 Eval Constr.pretype preterm:(nat).

Fail Ltac2 Eval Constr.pretype preterm:(notbound).
Fail Ltac2 Eval Constr.pretype preterm:(nat = 0).

(* strict check *)
Fail Ltac2 baz () := preterm:(notbound).

(* variable capture *)
Ltac2 Eval
  let x := preterm:(n = n) in
  constr:(forall n:nat, ltac2:(Control.refine (fun () => Constr.pretype x))).
