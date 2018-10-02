Ltac ret_and_left f :=
  let tac := ret_and_left in
  let T := type of f in
  lazymatch eval hnf in T with
    | ?T' -> _ =>
      let ret := constr:(fun x' : T' => ltac:(tac (f x'))) in
      exact ret
    | ?T' => exact f
  end.

Goal forall A B : Prop, forall x y : A, True.
Proof.
  intros A B x y.
  pose (f := fun (x y : A) => conj x y).
  pose (a := ltac:(ret_and_left f)).
  Fail unify (a x y) (conj x y).
Abort.
