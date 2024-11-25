Require Corelib.Program.Wf.

Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.

Inductive PolyType (R: Set): Set :=
  | prt_leading: PolyType R.

Definition poly_deg {R: Set} (p: PolyType R): nat.
Admitted.

Definition RootExtensionType {F: Set} (p: PolyType F) (Hp: p <> p): Set.
Admitted.

Program Fixpoint SplittingExtensionType {K: Set} (p: PolyType K) {measure (poly_deg p)}: Set :=
  match p with
  | prt_leading _ => SplittingExtensionType (_: PolyType (RootExtensionType p _))
  end.
Next Obligation.
Admitted.
Next Obligation.
admit.
Defined. (* anomaly "in Univ.repr: Universe Top.3 undefined." fixed by #18642 *)
Next Obligation.
Admitted.
Next Obligation.
Admitted.
