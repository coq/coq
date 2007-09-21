Require Export NZAxioms.
Require Import NZTimes.

Module Type NZOrdAxiomsSig.
Declare Module Export NZAxiomsMod : NZAxiomsSig.
Open Local Scope NatIntScope.

Parameter Inline NZlt : NZ -> NZ -> Prop.
Parameter Inline NZle : NZ -> NZ -> Prop.

Add Morphism NZlt with signature NZE ==> NZE ==> iff as NZlt_wd.
Add Morphism NZle with signature NZE ==> NZE ==> iff as NZle_wd.

Notation "x < y" := (NZlt x y) : NatIntScope.
Notation "x <= y" := (NZle x y) : NatIntScope.

Axiom NZle_lt_or_eq : forall n m : NZ, n <= m <-> n < m \/ n == m.
Axiom NZlt_irrefl : forall n : NZ, ~ (n < n).
Axiom NZlt_succ_le : forall n m : NZ, n < S m <-> n <= m.
End NZOrdAxiomsSig.

(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
