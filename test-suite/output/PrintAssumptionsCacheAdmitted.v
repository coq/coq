(* Print Assumptions reuses traversals across queries in one environment.
   An Admitted lemma is an axiom, and it must still be reported when it is
   reached only through a constant an earlier query already traversed. *)

Lemma adm : nat. Proof. exact 0. Admitted.
Definition mid := adm + 1.
Definition top := mid.
Lemma goal : top = top. Proof. reflexivity. Qed.
Lemma goal2 : mid = mid. Proof. reflexivity. Defined.
Print Assumptions top.
Print Assumptions goal.
Print Assumptions goal2.
Print Assumptions goal goal2.
