(* Set Primitive Projections. *)
Class foo {A} {a : A} := { bar := a; baz : bar = bar }.
Arguments bar {_} _ {_}.
Instance: forall A a, @foo A a.
intros; constructor.
abstract reflexivity.
Defined.
Goal @bar _ Set _ = (@bar _ (fun _ : Set => Set) _) nat.
Proof.
  Check (bar Set).
  Check (bar (fun _ : Set => Set)).
  Fail change (bar (fun _ : Set => Set)) with (bar Set). (* Error: Conversion test raised an anomaly *)

Abort.


Module A.
Universes i j.
Constraint i < j.
Variable  foo : Type@{i}.
Goal Type@{i}.
  Fail let t := constr:(Type@{j}) in
  change Type with t.
Abort.

Goal Type@{j}.
  Fail let t := constr:(Type@{i}) in
  change Type with t.
  let t := constr:(Type@{i}) in
  change t. exact foo.
Defined.

End A.
