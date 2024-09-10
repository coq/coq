Goal 1 = 1.
eassert (Some _ = Some _) as H.
2:injection H;intros H';exact H'.
reflexivity.
Qed.
