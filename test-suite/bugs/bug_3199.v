Axiom P : nat -> Prop.
Axiom admit : forall n : nat, P n -> P n -> n = S n.
Axiom foo : forall n, P n.

Create HintDb bar.
#[export] Hint Extern 3 => symmetry : bar.
#[export] Hint Resolve admit : bar.
#[export] Hint Immediate foo : bar.

Lemma qux : forall n : nat, n = S n.
Proof.
intros n.
eauto with bar.
Defined.

Goal True.
pose (e := eq_refl (qux 0)); unfold qux in e.
match type of e with context [eq_sym] => fail 1 | _ => idtac end.
Abort.
