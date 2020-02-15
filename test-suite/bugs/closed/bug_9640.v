(* Similar to #9521 (was an anomaly unknown level 150 *)

Module A.

Declare Custom Entry expr.
Notation "p" := (p) (in custom expr at level 150, p constr, right associativity).
Notation "** X" := (X) (at level 200, X custom expr at level 150).
Lemma t : ** True.
Abort.

End A.

(* Similar to #9517, #9519, #11331 *)

Module B.

Declare Custom Entry expr.
Notation "p" := (p) (in custom expr at level 100, p constr (* at level 200 *)).
Notation "** X" := (X) (at level 200, X custom expr at level 150).
Lemma t : ** True.
Abort.

End B.
