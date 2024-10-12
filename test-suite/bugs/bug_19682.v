Axiom admit : False.

Inductive foo (A : Type) : Prop := I.

Lemma bar : foo Type.
Proof.
change foo with (fun x : Type => foo x). (* We shouldn't lose the constraint here *)
cbv beta.
elim admit.
Defined. (* Illegal application error *)
