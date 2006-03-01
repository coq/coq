Goal (n:nat)(n=O)->(n=O).
Intros.
Rename n into p.
NewInduction p; Auto.
Qed.

(* Submitted by Iris Loeb (#842) *)

Section rename.

Variable A:Prop.

Lemma Tauto: A->A.
rename A into B.
tauto.
Qed.

End rename.
