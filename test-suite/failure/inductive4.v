(* This used to succeed in versions 8.1 to 8.3 *)

Require Import Logic.
Require Hurkens.
Definition Ti := Type.
Inductive prod (X Y:Ti) := pair : X -> Y -> prod X Y.
Definition B : Prop := let F := prod True in F Prop. (* Aie! *)
Definition p2b (P:Prop) : B := pair True Prop I P.
Definition b2p (b:B) : Prop := match b with pair _ P => P end.
Lemma L1 : forall A : Prop, b2p (p2b A) -> A.
Proof (fun A x => x).
Lemma L2 : forall A : Prop, A -> b2p (p2b A).
Proof (fun A x => x).
Check Hurkens.paradox B p2b b2p L1 L2.

