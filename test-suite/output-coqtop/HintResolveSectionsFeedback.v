Create HintDb hrs_feedback.

Inductive FeedbackRel : nat -> nat -> Prop :=
| feedback_rel_trans : forall mid,
    FeedbackRel 0 mid -> FeedbackRel mid 0 -> FeedbackRel 0 0.

Section Outer.
  Context (A : Type).

  Section Inner.
    Context (mid : nat).

    Definition feedback_hint :
      FeedbackRel 0 mid -> FeedbackRel mid 0 -> FeedbackRel 0 0 :=
      feedback_rel_trans mid.

    #[global] Hint Resolve feedback_hint : hrs_feedback.
  End Inner.
End Outer.
