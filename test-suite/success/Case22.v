(* Check typing in the presence of let-in in inductive arity *)

Inductive I : let a := 1 in a=a -> let b := 2 in Type := C : I (eq_refl).
Lemma a : forall x:I eq_refl, match x in I a b c return b = b with C => eq_refl end = eq_refl.
intro.
match goal with |- ?c => let x := eval cbv in c in change x end.
Abort.
