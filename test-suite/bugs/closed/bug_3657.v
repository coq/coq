(* Check typing of replaced objects in change - even though the failure
   was already a proper error message (but with a helpless content) *)

Class foo {A} {a : A} := { bar := a; baz : bar = bar }.
Arguments bar {_} _ {_}.
Instance: forall A a, @foo A a.
intros; constructor.
abstract reflexivity.
Defined.
Goal @bar _ Set _ = (@bar _ (fun _ : Set => Set) _) nat.
Proof.
  Fail change (bar (fun _ : Set => Set)) with (bar Set).
