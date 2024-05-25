Require Import Derive.

Derive foo : nat SuchThat (foo = foo) As bar.
Proof.
reflexivity.
Unshelve.
exact 0.
Qed.

Derive id : (forall {A}, A -> A) SuchThat (forall {A} (a:A), id a = a) As spec.
Proof.
unfold id.
reflexivity.
Qed.
About id.
Check id 0.

Set Universe Polymorphism.

Derive id' : (forall {A}, A -> A) SuchThat (forall {A} (a:A), id' a = a) As spec'.
Proof.
unfold id.
Unshelve.
2: exact (fun A a => a).
reflexivity. (* Polymorphism breaks unification? *)
Qed.

Check id'@{Set} 0.
