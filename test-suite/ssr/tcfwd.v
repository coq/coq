Require Import ssreflect.

Axioms A B D : Type.
Class C := {}.
Axiom f : C -> A -> B.
Axiom g : D -> C.

Local Hint Extern 0 C => apply g;shelve : typeclass_instances.

Lemma foo : A -> Type.
Proof.
  move=> /f. (* Not_found *)
  intro;exact nat.
Qed.
