Require Export NumPrelude.
Require Export NZAxioms.

Set Implicit Arguments.

Module Type ZAxiomsSig.
Declare Module Export NZOrdAxiomsMod : NZOrdAxiomsSig.
Open Local Scope NatIntScope.

Notation Z := NZ (only parsing).
Notation E := NZE (only parsing).

Parameter Zopp : Z -> Z.

Add Morphism Zopp with signature E ==> E as Zopp_wd.

Notation "- x" := (Zopp x) (at level 35, right associativity) : NatIntScope.

(* Integers are obtained by postulating that every number has a predecessor *)
Axiom Zsucc_pred : forall n : Z, S (P n) == n.

Axiom Zopp_0 : - 0 == 0.
Axiom Zopp_succ : forall n : Z, - (S n) == P (- n).

End ZAxiomsSig.

