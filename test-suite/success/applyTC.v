Axiom P : nat -> Prop.

Class class (A : Type) := { val : A }.

Lemma usetc {t : class nat} : P (@val nat t).
Admitted.

Notation "{val:= v }" := (@val _ v).

Instance zero : class nat := {| val := 0 |}.

Lemma test : P 0.
Fail apply usetc.
pose (tmp := usetc); apply tmp; clear tmp.
Qed.
