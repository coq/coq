Set Printing Existential Instances.
Set Printing All.
Goal let y:=0 in exists x:y=y, x = x.
intros.
eexists.
rename y into z.
unfold z at 1 2.
(* should fail because the evar type depends on z *)
Fail clear z.
