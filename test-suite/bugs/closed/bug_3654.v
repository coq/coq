Tactic Notation "mysimpl" "in" ne_hyp_list(hyps) := simpl in hyps.

Goal 0+0=0->0+0=0->0=0.
intros H1 H2.
mysimpl in H1 H2.
match goal with H:0=0 |- _ => exact H end.
Qed.
