Inductive True : Prop := I.
Class Lift (T : Type).
Axiom closed_increment : forall {T} {H : Lift T}, True.
Create HintDb core.
Lemma closed_monotonic T (H : Lift T) : True.
Proof.
  Set Printing Universes.
  auto using closed_increment. Show Universes.
Qed.
(* also fails with -nois, so the content of the hint database does not matter
*)
