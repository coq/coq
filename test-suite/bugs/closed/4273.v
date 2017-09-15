
  
Set Primitive Projections.
Record total2 (P : nat -> Prop) := tpair { pr1 : nat; pr2 : P pr1 }.
Theorem onefiber' (q : total2 (fun y => y = 0)) : True.
Proof. assert (foo:=pr2 _ q). simpl in foo.
       destruct foo. (* Error: q is used in conclusion. *) exact I. Qed.

Print onefiber'.
