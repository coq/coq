(* Slightly improving interpretation of Ltac subterms in notations *)

Notation "'var2' x .. y = z ; e" := (ltac:(exact z), (fun x => .. (fun y => e)
..)) (at level 200, x binder, y binder, e at level 220).
Check (var2 a = 1; a).

Require Import Ltac2.Ltac2.

Notation "'var3' x .. y = z ; e" := (ltac2:(exact $preterm:z), (fun x => .. (fun y => e)
..)) (at level 200, x binder, y binder, e at level 220).
Check (var3 a = 1; a).

Fail Notation "'var4' x .. y = z ; e" := (ltac2:(let _ := x in exact 0), (fun x => .. (fun y => e)
..)) (at level 200, x binder, y binder, e at level 220).
