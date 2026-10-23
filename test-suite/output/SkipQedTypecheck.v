(* coq-prog-args: ("-skip-qed-typecheck") *)

Axiom ax : True.

Lemma uses_ax : True.
Proof. exact ax. Qed.

Lemma plain : 1 + 1 = 2.
Proof. reflexivity. Qed.

Lemma uses_plain : 1 + 1 = 2 /\ True.
Proof. split; [exact plain | exact uses_ax]. Qed.

Definition transparent : 2 + 2 = 4 := eq_refl.

Lemma uses_transparent : 2 + 2 = 4.
Proof. exact transparent. Defined.

Unset Guard Checking.
Fixpoint loop (n : nat) : True := loop n.
Set Guard Checking.

Lemma uses_loop : True.
Proof. exact (loop 0). Qed.
Lemma uses_abstract : 3 + 3 = 6.
Proof. abstract reflexivity. Qed.

Print Assumptions uses_ax.
Print Assumptions plain.
Print Assumptions uses_plain.
Print Assumptions transparent.
Print Assumptions uses_transparent.
Print Assumptions uses_loop.
Print Assumptions uses_abstract.
