Require Import Ltac2.Ltac2.

(** Test for quotations *)

Ltac2 ref0 () := reference:(&x).
Ltac2 ref1 () := reference:(nat).
Ltac2 ref2 () := reference:(Datatypes.nat).
Fail Ltac2 ref () := reference:(i_certainly_dont_exist).
Fail Ltac2 ref () := reference:(And.Me.neither).

Goal True.
Proof.
let x := constr:(I) in
let y := constr:((fun z => z) $x) in
Control.refine (fun _ => y).
Qed.
