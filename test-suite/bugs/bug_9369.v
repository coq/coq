Goal exists n, n + 0 = n.
Proof.
evar (x:nat).
let y := eval unfold x in x in unify y 3.
exists x. vm_compute.
match goal with [ |- 3 = 3 ] => idtac end. (* expect 3 = 3 *)
Abort.
