Require Extraction.

Set Universe Polymorphism.
Definition foo@{s| |} := tt.

Definition bar := foo@{Prop|}.

Fail Extraction bar.

(* the actual problem only appears once we have inductives with sort poly output *)
