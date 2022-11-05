From Ltac2 Require Import Ltac2.

(* The "p" comes from Tac2intern.fresh_var *)
Fail Ltac2 foo (a, b) := p.
Fail Ltac2 foo x := let (a, b) := x in p.
Fail Ltac2 foo x := let (a, b) := p in x.
Fail Ltac2 foo (a, b) := let (c, d) := p in c.
Fail Ltac2 foo (a, b) := let (c, d) := (a, b) in p.
Fail Ltac2 foo (a, b) := if a then p else p.
Fail Ltac2 foo (a, b) := p; a.
Ltac2 Type 'a ref := { mutable contents : 'a }.
Ltac2 snd (a, b) := b.
Fail Ltac2 foo (a, b) := a.(contents) := snd p.
