From Stdlib Require Import PrimInt63 PrimArray.

Class pointed T := point : T.

Inductive PROOF_OF A := the (x : A).

Definition foo : PROOF_OF (@make (pointed nat) 0 0 = @make nat 0 0).
  constructor.
  cbv. (* @eq (array@{pointed.u0} nat) [| | O : nat |]@{pointed.u0} [| | O : nat |]@{Set} *)
  reflexivity.
Defined.

Notation barv
  := (@exist (array@{Set} nat) (fun x => x = @make nat 0 0) _ (eq_refl (@make nat 0 0)))
       (only parsing).

Definition bar1 : { x | x = @make (pointed nat) 0 0 }
  := Eval cbv in barv.

Definition bar0 : { x | x = @make (pointed nat) 0 0 }
  := Eval vm_compute in barv.

Definition bar := Eval cbv in foo.
