(* Check Generalize Dependent *)

Lemma l1 : [a:=O;b:=a](c:b=b;d:(True->b=b))d=d.
Intros.
Generalize Dependent a.
Intros a b c d.
Abort.
