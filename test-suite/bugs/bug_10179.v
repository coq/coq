From Stdlib Require Import ssreflect ssrbool.
From Stdlib Require Import ListDef.

Fixpoint contains {X: Type} (eqt: X -> X -> bool) (l: list X) (x: X): bool := true.

Fixpoint deduplicate {X: Type} (eqt: X -> X -> bool) (l: list X): list X := match l with
| nil => nil
| x :: xs => let deduplicatedRest := deduplicate eqt xs in
  if (contains eqt deduplicatedRest x) then deduplicatedRest
  else x :: deduplicatedRest
end.

Theorem deduplicate_idempotent: forall {X: Type} (eqt: X -> X -> bool) (l: list X), deduplicate eqt (deduplicate eqt l) = deduplicate eqt l.
Proof.
move => ? eqt.
elim => [|x xs IHxs] => //.
simpl.

case H: eqt.
Abort.
