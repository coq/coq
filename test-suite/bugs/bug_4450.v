Polymorphic Axiom inhabited@{u} : Type@{u} -> Prop.

Polymorphic Axiom unit@{u} : Type@{u}.
Polymorphic Axiom tt@{u} : inhabited unit@{u}.

#[export] Polymorphic Hint Resolve tt : the_lemmas.
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
  pose (H := fapp unit funi).
  eauto using H. (* The two fapp's have different universes *)
Qed.

Definition fapp0 := fapp unit funi.
#[export] Hint Resolve fapp0 : mylems.

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
  Fail solve [ pose (mk := maketype@{m}); eauto using mk ].
  eauto using maketype.
  Undo.
  pose (mk := maketype@{n}); eauto using mk.
Qed.

Axiom foo : forall (A : Type), list A.
Polymorphic Axiom foop@{i} : forall (A : Type@{i}), list A.

Universe x y.
Goal list Type@{x}.
Proof.
  pose (H := foo Type); eauto using H. (* Refreshes the term *)
  Undo.
  eauto using foo. Show Universes.
  Undo.
  eauto using foop. Show Proof. Show Universes.
Qed.
