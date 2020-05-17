From Ltac2 Require Import Ltac2.
From Coq Require Import ZArith String List.

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

(** * Test cases for specific notations with special contexts *)

(** ** Test eval ... in / reduction tactics *)

(** Moved to test-suite/output/ltac2_notations_eval_in.v so that the output can be checked s*)
