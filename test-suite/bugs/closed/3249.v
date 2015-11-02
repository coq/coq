Set Implicit Arguments.

Ltac ret_and_left T :=
  let t := type of T in
  lazymatch eval hnf in t with
    | ?a /\ ?b => constr:(proj1 T)
    | forall x : ?T', @?f x =>
      constr:(fun x : T' => ltac:(let fx := constr:(T x) in
                              let t := ret_and_left fx in
                              exact t))
  end.
