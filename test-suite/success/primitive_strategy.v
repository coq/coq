#[projections(primitive)]
Record r := R { f : unit }.

Definition rv := {| f := tt |}.

Module Reduction.
  Ltac syn_eq := lazymatch goal with |- tt = tt => reflexivity end.

  Goal rv.(f) = tt.
  Proof.
    Succeed lazy; syn_eq.
    Fail with_strategy opaque [f] lazy; syn_eq.

    Succeed cbn; syn_eq.
    Fail with_strategy opaque [f] cbn; syn_eq.

    Succeed simpl; syn_eq.
    Fail with_strategy opaque [f] simpl; syn_eq.

    Succeed cbv; syn_eq.
    Fail with_strategy opaque [f] cbv; syn_eq.
  Abort.
End Reduction.
