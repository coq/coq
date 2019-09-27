

Section Foo.

  Variable X : Type.

  Polymorphic Section Bar.

  Variable A : Type.

  Definition id (a:A) := a.

End Bar.
Check id@{_}.
End Foo.
Check id@{_}.

Polymorphic Section Foo.
Variable A : Type.
Section Bar.
  Variable B : Type.

  Inductive prod := Prod : A -> B -> prod.
End Bar.
Check prod@{_}.
End Foo.
Check prod@{_ _}.

Section Foo.

  Universe K.
  Inductive bla := Bla : Type@{K} -> bla.

  Polymorphic Definition bli@{j} := Type@{j} -> bla.

  Definition bloo := bli@{_}.

  Polymorphic Universe i.

  Fail Definition x := Type.
  Fail Inductive x : Type := .
  Polymorphic Definition x := Type.
  Polymorphic Inductive y : x := .

  Variable A : Type. (* adds a mono univ for the Type, which is unrelated to the others *)

  Fail Variable B : (y : Type@{i}).
  (* not allowed: mono constraint (about a fresh univ for y) regarding
  poly univ i *)

  Polymorphic Variable B : Type. (* new polymorphic stuff always OK *)

  Variable C : Type@{i}. (* no new univs so no problems *)

  Polymorphic Definition thing := bloo -> y -> A -> B.

End Foo.
Check bli@{_}.
Check bloo@{}.

Check thing@{_ _ _}.

Section Foo.

  Polymorphic Universes i k.
  Universe j.
  Fail Constraint i < j.
  Fail Constraint i < k.

  (* referring to mono univs in poly constraints is OK. *)
  Polymorphic Constraint i < j. Polymorphic Constraint j < k.

  Polymorphic Definition foo := Type@{j}.
End Foo.
