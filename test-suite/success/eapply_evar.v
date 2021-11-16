(* Test propagation of evars from subgoal to brother subgoals *)

(* This does not work (oct 2008) because "match goal" sees "?evar = O"
   and not "O = O" *)

Lemma eapply_evar : O=O -> 0=O.
intro H; eapply eq_trans;
  [apply H | match goal with |- ?x = ?x => reflexivity end].
Qed.
