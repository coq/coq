(* subst with section variables *)                                                                                     
Section A.
Variable a:nat.
Definition b := a.
Goal a=1 -> b=1.
intros.
subst a. (* Was failing *)
Admitted.

End A.
