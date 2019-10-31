Require Import Ltac2.Ltac2.

(* Preterms are not terms *)
Fail Notation "[ x ]" := $x.

Section Foo.

Notation "[ x ]" := ltac2:(Control.refine (fun _ => Constr.pretype x)).

Goal [ True ].
Proof.
constructor.
Qed.

End Foo.

Section Bar.

(* Have fun with context capture *)
Notation "[ x ]" := ltac2:(
  let c () := Constr.pretype x in
  refine constr:(forall n : nat, n = ltac2:(Notations.exact0 true c))
).

Goal forall n : nat, [ n ].
Proof.
reflexivity.
Qed.

(* This fails currently, which is arguably a bug *)
Fail Goal [ n ].

End Bar.
