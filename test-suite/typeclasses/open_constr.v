Tactic Notation "opose" open_constr(foo) := pose foo.
Class Foo := Build_Foo : Set.
Axiom f : forall `{Foo}, Set.
Set Printing Implicit.
Goal forall `{Foo}, True.
Proof.
  intro H.
  pose f.
  opose f.
  Fail let x := (eval hnf in P) in has_evar x.
  let x := (eval hnf in P0) in has_evar x.

