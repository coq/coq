Create HintDb db1.
Axiom eq_tt : tt = tt.
#[local] Hint Resolve eq_tt : db1.

Goal exists u, u = tt.
Proof.
  eexists.
  Succeed solve [exact eq_tt].
  solve [auto with nocore db1].
Qed.

Create HintDb db2.
Axiom True_eq_tt : True -> tt = tt.
#[local] Hint Resolve True_eq_tt : db2.

Goal True -> exists u, u = tt.
Proof.
  intros. eexists.
  solve [auto with nocore db2].
Qed.
