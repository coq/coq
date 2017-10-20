Goal forall n : nat, n = 0 -> n = 0.
intros.
rename n into p.
induction p; auto.
Qed.

(* Submitted by Iris Loeb (BZ#842) *)

Section rename.

Variable A:Prop.

Lemma Tauto: A->A.
rename A into B.
tauto.
Qed.

End rename.
