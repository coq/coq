(* subst with section variables *)

(* Version courte *)

Section A.
Variable a:nat.
Definition b := a.
Goal a=1 -> a=b.
intros.
subst a. (* was not clearing H *)
Fail clear H.
Admitted.

End A.

(* Version originale *)

Module B.

Axiom proc : Type.
Axiom mkproc : nat -> nat -> proc.

Section WithParams.
  Context (input aggregatorIn : nat).

  Definition MapReduceImpl : proc := mkproc input aggregatorIn.

  Inductive R: proc -> proc -> Prop :=
  | BuildR : forall pr1 pr2,
      pr1 = MapReduceImpl ->
      pr2 = MapReduceImpl ->
      R pr1 pr2.

  Goal forall pr1 pr2,
      input = aggregatorIn ->
      R pr1 pr2 /\ aggregatorIn = input.
  Proof.
    intros.
    subst input. 
    Fail clear H.
  Admitted.

End B.
