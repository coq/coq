(* Checking no anomaly on some unexpected intropattern *)

Ltac ih H := induction H as H.
Ltac ih' H H' := induction H as H'.

Goal True -> True.
Fail intro H; ih H.
intro H; ih' H ipattern:([]).
exact I.
Qed.

