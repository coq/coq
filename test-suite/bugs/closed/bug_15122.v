Require Import Ltac2.Ltac2.

Axiom P : Prop.
Axiom p : P.

Goal P.
Proof.
now (); apply p.
(* This should parse as (now ((); apply p)) *)
Qed.
