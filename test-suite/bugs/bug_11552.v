From Ltac2 Require Import Ltac2.

Goal True.
Proof.
  Search unit.
  (* Unbound constructor Search *)
  Check tt.
  (* Unbound constructor Check *)
Abort.
