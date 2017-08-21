Require Import Coq.Arith.Arith.

Module A.

  Fixpoint foo (n:nat) :=
  match n with
  | 0 => 0
  | S n => bar n
  end

  with bar (n:nat) :=
  match n with
  | 0 => 0
  | S n => foo n
  end.

  Lemma using_foo:
    forall (n:nat), foo n = 0 /\ bar n = 0.
  Proof.
    induction n ; split ; auto ;
    destruct IHn ; auto.
  Qed.

End A.


Module B.
  
  Module A := A.
  Import A.

End B.

Module E.

  Module B := B.
  Import B.A.

  (* Bug 1 *)
  Lemma test_1:
    forall (n:nat), foo n = 0.
  Proof.
    intros ; destruct n.
    reflexivity.
    specialize (A.using_foo (S n)) ; intros.
    simpl in H.
    simpl.
    destruct H.
    assumption.
  Qed.

End E.
