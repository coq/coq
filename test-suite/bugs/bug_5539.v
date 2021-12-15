Set Universe Polymorphism.

Inductive D : nat -> Type :=
| DO : D O
| DS n : D n -> D (S n).

Fixpoint follow (n : nat) : D n -> Prop :=
  match n with
  | O => fun d => let 'DO := d in True
  | S n' => fun d => (let 'DS _ d' := d in fun f => f d') (follow n')
  end.

Definition step (n : nat) (d : D n) (H : follow n d) :
  follow (S n) (DS n d)
  := H.
