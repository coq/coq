Require Import BinNat.
Fixpoint T n := match n with O => nat | S n => nat -> T n end.
Fixpoint app n : T n -> nat :=
  match n with O => fun x => x | S n => fun f => app n (f 0) end.
Definition n := N.to_nat 5000.
Axiom f : T n.
Eval vm_compute in let t := (app n f, 0) in snd t.
