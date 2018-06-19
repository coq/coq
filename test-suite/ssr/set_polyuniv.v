From Coq Require Import ssreflect.
Set Default Proof Using "Type".

Local Set Universe Polymorphism.

Axiom foo : Type -> Prop.

Lemma test : foo nat.
Proof.
set x := foo _. (* key @foo{i} matches @foo{j} *)
Abort.
