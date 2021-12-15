(* Bugs #3787 and #3723 on reinitializing camlp5 levels *)

Definition a := True.
Reserved Notation "-- x" (at level 50, x at level 20).
Reserved Notation "--- x" (at level 20).
Reset a.
