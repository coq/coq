Polymorphic Axiom inhabited@{u} : Type@{u} -> Prop.

Polymorphic Axiom unit@{u} : Type@{u}.
Polymorphic Axiom tt@{u} : inhabited unit@{u}.

Polymorphic Hint Resolve tt : the_lemmas.
Set Printing All.
Set Printing Universes.
Goal inhabited unit.
Proof.
  eauto with the_lemmas.
Qed.

Universe u.
Axiom f : Type@{u} -> Prop.
Lemma fapp (X : Type) : f X -> False.
Admitted.
Polymorphic Axiom funi@{i} : f unit@{i}.

Goal (forall U, f U) -> (*(f unit -> False) ->  *)False /\ False.
  eauto using (fapp unit funi). (* The two fapp's have different universes *)
Qed.

Hint Resolve (fapp unit funi) : mylems.

Goal (forall U, f U) -> (*(f unit -> False) ->  *)False /\ False.
  eauto with mylems. (* Forces the two fapps at the same level *)
Qed.

Goal (forall U, f U) -> (f unit -> False) -> False /\ False.
  eauto. (* Forces the two fapps at the same level *)
Qed.

Polymorphic Definition MyType@{i} := Type@{i}.
Universes l m n.
Constraint l < m.
Polymorphic Axiom maketype@{i} : MyType@{i}.

Goal MyType@{l}.
Proof.
  Fail solve [ eauto using maketype@{m} ].
  eauto using maketype.
  Undo.
  eauto using maketype@{n}.
Qed.

Axiom foo : forall (A : Type), list A.
Polymorphic Axiom foop@{i} : forall (A : Type@{i}), list A.

Universe x y.
Goal list Type@{x}.
Proof.
  eauto using (foo Type). (* Refreshes the term *)
  Undo.
  eauto using foo. Show Universes.
  Undo.
  eauto using foop. Show Proof. Show Universes.
Qed.
