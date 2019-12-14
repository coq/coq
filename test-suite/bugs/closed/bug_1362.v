(** Omega is now aware of the bodies of context variables
    (of type Z or nat). *)

Require Import ZArith Omega.
Open Scope Z.

Goal let x := 3 in x = 3.
intros.
omega.
Qed.

Open Scope nat.

Goal let x := 2 in x = 2.
intros.
omega.
Qed.

(** NB: this could be disabled for compatibility reasons *)

(* after replacement by lia, omega will always use local hypotheses

Unset Omega UseLocalDefs.

Goal let x := 4 in x = 4.
intros.
Fail omega.
Abort.

*)
