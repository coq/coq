(** Omega is now aware of the bodies of context variables
    (of type Z or nat). *)

From Stdlib Require Import ZArith Lia.
Open Scope Z.

Goal let x := 3 in x = 3.
intros.
lia.
Qed.

Open Scope nat.

Goal let x := 2 in x = 2.
intros.
lia.
Qed.
