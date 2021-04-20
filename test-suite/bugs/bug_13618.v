Require Import Setoid CRelationClasses CMorphisms.

Definition equiv@{i} (A B : Type@{i}) : Type@{i} :=
  iffT A B.

Section Equiv.

  Hypothesis equiv_equiv : Equivalence equiv.
  Hypothesis equiv_sum : Proper (equiv ==> equiv ==> equiv) sum.

  Goal forall X, equiv X bool -> equiv (unit + unit) X.
  Proof.
    intros X H.
    rewrite H.
  Abort.

  Definition sum' : Type -> Type -> Type := sum.

  Hypothesis equiv_sum' : Proper (equiv ==> equiv ==> equiv) sum'.

  Goal forall X, equiv X (bool : Type) -> equiv (sum' X X) X.
  Proof.
    intros X H. rewrite H.
  Abort.

End Equiv.
