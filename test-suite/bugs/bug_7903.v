(* Slightly improving interpretation of Ltac subterms in notations *)

Module Ltac1.

(* x is only binding, absent in ltac *)
Notation bar x f := (let z := ltac:(exact 1) in (fun x : nat => f)).
Check fun x => bar x (x + x).
Check bar x (x + x).
Notation usebar v := (bar v (v + v)) (only parsing).
Check usebar a.

(* x is binding and bound, absent in ltac expression *)
Notation bar' x f := (let z := ltac:(exact 1) in (x, fun x : nat => f)).
Check fun x => bar' x (x + x).
Notation usebar' v := (bar' v (v + v)) (only parsing).
Check fun a => usebar' a.

(* x is only binding *)
Notation bar'' x f := (let z := ltac:(exact (fun x : nat => f)) in fun x : nat => f).
Check fun x => bar'' x (x + x).
Notation usebar'' v := (bar'' v (v + v)) (only parsing).
Check usebar'' a.

(* x is binding and bound *)
Notation bar''' x f := (let z := ltac:(exact (x, fun x : nat => f)) in (x, fun x : nat => f)).
Check fun x : bool => bar''' x (x + x).

(* x is only bound in ltac *)
Notation bar'''' x f := (let z := ltac:(exact x) in (x, fun x : nat => f)).
Check fun x => bar'''' x (x + x).

(* f is only bound in ltac *)
Notation bar''''' x f := (let z := ltac:(exact f) in (fun x : nat => f)) (only parsing).
Check fun p => bar''''' p (p + p).
Notation usebar''''' v := (bar''''' v (v + v)) (only parsing).
Check fun p => usebar''''' p.

End Ltac1.

Require Import Ltac2.Ltac2.

Module Ltac2.

(* x is binding and bound, absent in ltac2 expression *)
Notation bar' x f := (let z := ltac2:(exact 1) in (x, fun x : nat => f)).
Check fun x => bar' x (x + x).
Notation usebar' v := (bar' v (v + v)) (only parsing).
Check fun a => usebar' a.

(* x is only bound in ltac2 *)
Notation bar'''' x f := (let z := ltac2:(exact x) in (x, fun x : nat => f)).
Check fun x => bar'''' x (x + x).

End Ltac2.
