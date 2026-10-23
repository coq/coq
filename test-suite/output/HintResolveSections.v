Create HintDb hrs_errors.

Inductive OutputPattern (A : Type) : Prop :=
| output_pattern_intro : A -> OutputPattern A.

Section ExplicitPattern.
  Context (A : Type) (a : A).

  Lemma explicit_pattern_hint : OutputPattern A.
  Proof. exact (output_pattern_intro A a). Qed.

  Fail #[global] Hint Resolve explicit_pattern_hint | 0 (OutputPattern A) : hrs_errors.
  Fail #[export] Hint Resolve explicit_pattern_hint | 0 (OutputPattern A) : hrs_errors.
End ExplicitPattern.

Section DirectSectionVariable.
  Context (h : True).

  Fail #[global] Hint Resolve h : hrs_errors.
End DirectSectionVariable.

Section IndirectSectionVariableHead.
  Context (P : Prop) (p : P).

  Lemma indirect_hint : P.
  Proof. exact p. Qed.

  Fail #[global] Hint Resolve indirect_hint : hrs_errors.
End IndirectSectionVariableHead.

Section DirectionalVariableHead.
  Context (A B : Prop) (ab : A <-> B).

  Lemma variable_head_iff : A <-> B.
  Proof. exact ab. Qed.

  Fail #[global] Hint Resolve -> variable_head_iff : hrs_errors.
  Fail Check variable_head_iff_proj_l2r.
  Fail #[export] Hint Resolve <- variable_head_iff : hrs_errors.
  Fail Check variable_head_iff_proj_r2l.
End DirectionalVariableHead.

Create HintDb hrs_multiplicity.

Definition output_alias := forall P : Prop, True.
Definition output_alias_hint : output_alias := fun _ => I.

Section MultiplicityOuter.
  Section MultiplicityInner.
    #[global] Hint Resolve output_alias_hint : hrs_multiplicity.
  End MultiplicityInner.
End MultiplicityOuter.

Print HintDb hrs_multiplicity.

Create HintDb hrs_repeated_import.

Module RepeatedImport.
  Section Empty.
    #[export] Hint Resolve output_alias_hint : hrs_repeated_import.
  End Empty.
End RepeatedImport.

Import RepeatedImport.
Import RepeatedImport.

Print HintDb hrs_repeated_import.

Create HintDb hrs_eauto_transition.

Inductive OutputRel : nat -> nat -> Prop :=
| output_rel_01 : OutputRel 0 1
| output_rel_10 : OutputRel 1 0
| output_rel_trans : forall mid,
    OutputRel 0 mid -> OutputRel mid 0 -> OutputRel 0 0.

#[global] Hint Resolve output_rel_01 output_rel_10 : hrs_eauto_transition.

Section FeedbackOuter.
  Context (A : Type).

  Section FeedbackInner.
    Context (mid : nat).

    Definition eauto_transition_hint :
      OutputRel 0 mid -> OutputRel mid 0 -> OutputRel 0 0 :=
      output_rel_trans mid.

    #[global] Hint Resolve eauto_transition_hint : hrs_eauto_transition.
  End FeedbackInner.
End FeedbackOuter.

Goal OutputRel 0 0.
Proof. eauto with hrs_eauto_transition nocore. Qed.
