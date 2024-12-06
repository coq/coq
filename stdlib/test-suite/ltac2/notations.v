From Ltac2 Require Import Ltac2.
From Stdlib Require Import ZArith String List.

(** * Test cases for the notation system itself *)

Open Scope Z_scope.

Check 1 + 1 : Z.

Ltac2 Notation "ex" arg(constr(nat,Z)) := arg.

Check (1 + 1)%nat%Z = 1%nat.

Lemma two : nat.
  refine (ex (1 + 1)).
Qed.

Import ListNotations.
Close Scope list_scope.

Ltac2 Notation "sl" arg(constr(string,list)) := arg.

Lemma maybe : list bool.
Proof.
  refine (sl ["left" =? "right"]).
Qed.

Lemma Z_add_bounds {amin a amax bmin b bmax : Z}:
  amin <= a <= amax ->
  bmin <= b <= bmax ->
  amin + bmin <= a + b <= amax + bmax.
Admitted.

Lemma apply l1 l2 v1 v2 u1 u2 : l1 + l2 <= v1 + v2 <= u1 + u2.
Proof.
  apply Z_add_bounds.
Admitted.

(** * Test cases for specific notations with special contexts *)

(** ** Test eval ... in / reduction tactics *)

(** Moved to test-suite/output/ltac2_notations_eval_in.v so that the output can be checked s*)
