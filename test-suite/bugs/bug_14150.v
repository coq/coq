Axiom a : forall A B : Prop, B -> A.
Axiom t : unit -> Set.
Axiom H: forall (m : unit) (p : t m), p = p.

Goal True.
eapply a.
rewrite H.
elim tt.
Abort.
