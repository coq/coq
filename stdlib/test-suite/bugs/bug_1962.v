(* Bug 1962.v

Bonjour,

J'ai un exemple de lemme que j'arrivais à prouver avec fsetdec avec la 8.2beta3
avec la beta4 et la version svn 11447 branche 8.2 çà diverge.

Voici l'exemple en question, l'exmple test2 marche bien dans les deux version,
test en revanche pose probleme:

*)

Require Export FSets.

(** This module takes a decidable type and
build finite sets of this type, tactics and defs *)

Module BuildFSets (DecPoints: UsualDecidableType).

Module Export FiniteSetsOfPoints := FSetWeakList.Make DecPoints.
Module Export FiniteSetsOfPointsProperties :=
 WProperties FiniteSetsOfPoints.
Module Export Dec := WDecide FiniteSetsOfPoints.
Module Export FM := Dec.F.

Definition set_of_points := t.
Definition Point := DecPoints.t.

Definition couple(x y :Point) : set_of_points :=
add x (add y empty).

Definition triple(x y t :Point): set_of_points :=
add x (add y (add t empty)).

Lemma test : forall P A B C A' B' C',
Equal
(union (singleton P) (union (triple A B C) (triple A' B' C')))
(union (triple P B B') (union (couple P A) (triple C A' C'))).
Proof.
intros.
unfold triple, couple.
Time fsetdec. (* works in 8.2 beta 3, not in beta 4 and final 8.2 *)
              (* appears to works again in 8.3 and trunk, take 4-6 seconds *)
Qed.

Lemma test2 : forall A B C,
Equal
 (union (singleton C) (couple A B)) (triple A B C).
Proof.
intros.
unfold triple, couple.
Time fsetdec.
Qed.

End BuildFSets.
