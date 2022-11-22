Require Import ssreflect.

Axioms (P : Prop) (p : P).

Goal (P -> P) -> P.
Proof.
  (* If I uncomment this line the bug disappears.
  have := I.*)
  have := p. (* Tactic failure: Incorrect number of goals (expected 1 tactic). *)
Abort.
