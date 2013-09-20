Set Printing Existential Instances.
Set Printing All.
Goal forall y, let z := S y in exists x, x = 0.
intros.
eexists.
unfold z.
clear y z.
(* should fail because the evar should no longer be allowed to depend on z *)
Fail instantiate (1:=z).

