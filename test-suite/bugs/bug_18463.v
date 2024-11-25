From Corelib Require Import Setoid.

Module Type Nop. End Nop.
Module nop. End nop.

Module RewriteStratSubstTestF (Nop : Nop).
  Axiom X : Set.

  Axiom f : X -> X.
  Axiom g : X -> X -> X.
  Axiom h : nat -> X -> X.

  Axiom lem0 : forall x, f (f x) = f x.
  Axiom lem1 : forall x, g x x = f x.
  Axiom lem2 : forall n x, h (S n) x = g (h n x) (h n x).
  Axiom lem3 : forall x, h 0 x = x.
  Definition idnat := @id nat.

  Ltac rs1 := rewrite_strat topdown lem2.
  Ltac rs2 := rewrite_strat try fold idnat.
  Ltac rs3 := rewrite_strat try subterms lem2.
  Ltac rs4 := rewrite_strat eval cbv delta [idnat].
End RewriteStratSubstTestF.

Module RewriteStratSubstTest := RewriteStratSubstTestF nop.

Goal forall x, RewriteStratSubstTest.h 6 x = RewriteStratSubstTest.f x /\ RewriteStratSubstTest.idnat 5 = id 5.
  intros.
  Print Ltac RewriteStratSubstTest.rs1. (* Ltac RewriteStratSubstTest.rs1 := Stdlib.Init.Ltac.rewrite_strat_#_521927FC _ (* Generic printer *) *)
  RewriteStratSubstTest.rs1. (* Error: Anomaly "Constant rewrite_strat.RewriteStratSubstTestF.lem2 does not appear in the environment."
Please report at http://coq.inria.fr/bugs/. *)
Undo 1.
  RewriteStratSubstTest.rs2.
Undo 1.
  RewriteStratSubstTest.rs3.
Undo 1.
  RewriteStratSubstTest.rs4.
Admitted.
