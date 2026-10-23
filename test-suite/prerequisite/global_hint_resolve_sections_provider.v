Create HintDb ghrs_vo_export.
Create HintDb ghrs_vo_global.

Inductive VoPred (A : Type) : Prop :=
| vo_pred_intro : A -> VoPred A.

Module Exported.
  Section HintSection.
    Context (A : Type) (a : A).

    Lemma exported_hint : VoPred A.
    Proof. exact (vo_pred_intro A a). Qed.

    #[export] Hint Resolve exported_hint : ghrs_vo_export.
  End HintSection.
End Exported.

Module Globalized.
  Section HintSection.
    Context (A : Type) (a : A).

    Lemma global_hint : VoPred A.
    Proof. exact (vo_pred_intro A a). Qed.

    #[global] Hint Resolve global_hint : ghrs_vo_global.
  End HintSection.
End Globalized.
