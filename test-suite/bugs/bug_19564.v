Structure myType := MyType { myType_X :> Type }.

Canonical Structure myType_CS X := MyType X.

Require Import ssreflect.

Axiom A1 : (unit * myType) -> Prop.

Lemma dummy (s' : (MyType (unit * unit))) : True.
Proof.
  move:s' => [? ?]; exact I.
Qed.

Axiom f : myType -> unit -> Prop.
Axiom ax : forall x, (fun '(M, t) => f M t) x.
