(** ROmega is now aware of the bodies of context variables
    (of type Z or nat).
    See also #148 for the corresponding improvement in Omega.
*)

Require Import ZArith ROmega.
Open Scope Z.

Goal let x := 3 in x = 3.
intros.
romega.
Qed.

(** Example seen in #4132
    (actually solvable even if b isn't known to be 5) *)

Lemma foo
  (x y x' zxy zxy' z : Z)
  (b := 5)
  (Ry : - b <= y < b)
  (Bx : x' <= b)
  (H : - zxy' <= zxy)
  (H' : zxy' <= x') : - b <= zxy.
Proof.
romega.
Qed.
