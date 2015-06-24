Inductive two : bool -> Prop :=
| Zero : two false
| One : two true.

Ltac dup :=
  let H := fresh in assert (forall (P : Prop), P -> P -> P) as H by (intros; trivial);
  apply H; clear H.

Lemma transform : two false <-> two true.
Proof. split; intros _; constructor. Qed.

Goal two false /\ two true /\ two false /\ two true /\ two true /\ two true.
Proof.
  do 2 dup.
  - repeat split.
    [2, 4-99, 100-3]:idtac.
    [2-5]:exact One.
    par:exact Zero.
  - repeat split.
    [3-6]:swap 1 4.
    [1-5]:swap 1 5.
    [0-4]:exact One.
    all:exact Zero.
  - repeat split.
    [1, 3]:exact Zero.
    [1, 2, 3, 4]: exact One.
  - repeat split.
    all:apply transform.
    [2, 4, 6]:apply transform.
    all:apply transform.
    [1-5]:apply transform.
    [1-6]:exact One.
Qed.