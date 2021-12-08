Fixpoint arrow (n: nat) :=
  match n with
  | S n => bool -> arrow n
  | O => bool
  end.

Fixpoint apply (n : nat) : arrow n -> bool :=
  match n return arrow n -> bool with
  | S n => fun f => apply _ (f true)
  | O => fun x => x
  end.

Axiom f : arrow 10000.
Definition v : bool := Eval compute in apply _ f.
Definition w : bool := Eval vm_compute in v.
