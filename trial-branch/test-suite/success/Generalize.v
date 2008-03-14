(* Check Generalize Dependent *)

Lemma l1 :
 let a := 0 in let b := a in forall (c : b = b) (d : True -> b = b), d = d.
intros.
generalize dependent a.
intros a b c d.
Abort.
