(* Former open goals in nested proofs were lost *)

(* This used to fail with "Incorrect number of goals (expected 1 tactic)." *)

Inductive foo := a | b | c.
Goal foo -> foo.
  intro x.
  simple refine (match x with
                 | a => _
                 | b => ltac:(exact b)
                 | c => _
                 end); [exact a|exact c].
Abort.

(* This used to leave the goal on the shelf and fails at reflexivity *)

Goal (True/\0=0 -> True) -> True.
  intro f.
  refine
   (f ltac:(split; only 1:exact I)).
  reflexivity.
Qed.

(* The "Unshelve" used to not see the explicitly "shelved" goal *)

Lemma f (b:comparison) : b=b.
refine (match b with
   Eq => ltac:(shelve)
 | Lt => ltac:(give_up)
 | Gt => _
 end).
exact (eq_refl Gt).
Unshelve.
exact (eq_refl Eq).
Fail auto. (* Check that there are no more regular subgoals *)
Admitted.

(* The "Unshelve" used to not see the explicitly "shelved" goal *)

Lemma f2 (b:comparison) : b=b.
refine (match b with
   Eq => ltac:(shelve)
 | Lt => ltac:(give_up)
 | Gt => _
 end).
Unshelve. (* Note: Unshelve puts goals at the end *)
exact (eq_refl Gt).
exact (eq_refl Eq).
Fail auto. (* Check that there are no more regular subgoals *)
Admitted.

(* The "unshelve" used to not see the explicitly "shelved" goal *)

Lemma f3 (b:comparison) : b=b.
unshelve refine (match b with
   Eq => ltac:(shelve)
 | Lt => ltac:(give_up)
 | Gt => _
 end).
(* Note: unshelve puts goals at the beginning *)
exact (eq_refl Eq).
exact (eq_refl Gt).
Fail auto. (* Check that there are no more regular subgoals *)
Admitted.
