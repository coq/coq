Section S.

Variable x : nat.

Definition y := x.

Lemma foo : nat.
Proof.
  let c := open_constr:(id _:Set) in
  change_no_check c in x;
  unify c nat;
  apply y.
Qed.
End S.
