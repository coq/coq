Require Extraction.

Set Universe Polymorphism.
Definition foo@{s| |} := tt.

Definition bar := foo@{Prop|}.

Fail Extraction bar.

(* the actual problem only appears once we have inductives with sort poly output: *)

Inductive Pair@{s|u|} (A:Type@{s|u}) : Type@{s|u} := pair : A -> A -> Pair A.

Definition use_pair@{s|+|} A (k:A->nat) (x:Pair@{s|_} A) :=
  k (match x with pair _ x _ => x end).

Definition make_pair := pair@{Prop|_} _ I I.

Definition hell := use_pair True (fun _ => 0) make_pair.

Fail Recursive Extraction hell.
