
Require Import ZArith Omega.
Open Scope Z_scope.

(** bug 4132: omega was using "simpl" either on whole equations, or on
   delimited but wrong spots. This was leading to unexpected reductions
   when one atom (here [b]) is an evaluable reference instead of a variable. *)

Lemma foo
  (x y x' zxy zxy' z : Z)
  (b := 5)
  (Ry : - b <= y < b)
  (Bx : x' <= b)
  (H : - zxy' <= zxy)
  (H' : zxy' <= x') : - b <= zxy.
Proof.
omega. (* was: Uncaught exception Invalid_argument("index out of bounds"). *)
Qed.

Lemma foo2 x y (b := 5) (H1 : x <= y) (H2 : y <= b) : x <= b.
omega. (* Pierre L: according to a comment of bug report #4132,
          this might have triggered "index out of bounds" in the past,
          but I never managed to reproduce that in any version,
          even before my fix. *)
Qed.

Lemma foo3 x y (b := 0) (H1 : x <= y) (H2 : y <= b) : x <= b.
omega. (* Pierre L: according to a comment of bug report #4132,
          this might have triggered "Failure(occurrence 2)" in the past,
          but I never managed to reproduce that. *)
Qed.
