Require Export NumPrelude.
Require Export NZAxioms.

Set Implicit Arguments.

Module Type ZAxiomsSig.
Declare Module Export NZOrdAxiomsMod : NZOrdAxiomsSig.
Open Local Scope NatIntScope.

Notation Z := NZ (only parsing).
Notation E := NZE (only parsing).

(** Integers are obtained by postulating that every number has a predecessor *)
Axiom S_P : forall n : Z, S (P n) == n.

End ZAxiomsSig.


(*
 Local Variables:
 tags-file-name: "~/coq/trunk/theories/Numbers/TAGS"
 End:
*)
