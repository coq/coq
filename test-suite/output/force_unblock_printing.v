Require Import Corelib.Force.

Set Printing Width 1000.

Axiom f : bool -> Blocked (nat -> Prop).
Axiom g : nat -> Blocked nat.
Axiom nested : Blocked (Blocked nat).
Axiom stuck : Blocked nat.

Definition unblock_under_binders : Blocked Prop :=
  __block Prop (forall x z : bool, __unblock (f x) 0).

Definition unblock_under_local_def : Blocked (nat -> nat) :=
  __block _ (fun x : nat => let y := S x in __unblock (g y)).

Definition repeated_unblocks : Blocked nat :=
  __block nat (__unblock stuck + __unblock stuck).

Definition nested_unblocks : Blocked nat :=
  __block nat (__unblock (__unblock nested)).

Definition ordinary_identity_run : Blocked nat :=
  __block nat (__run nat nat stuck (fun x => x)).

Print unblock_under_binders.
Print unblock_under_local_def.
Print repeated_unblocks.
Print nested_unblocks.
Print ordinary_identity_run.
