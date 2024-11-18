Set Universe Polymorphism.
(* Set Polymorphic Inductive Cumulativity. *)
Set Debug "UnivVariances".
Inductive eq@{s|u|} (A:Type@{s|u}) (x:A) : A -> Prop :=
  eq_refl : eq A x x.

Inductive bool@{s| |} : Type@{s|0} := true | false.

Set Debug "loop-checking-global".
Set Debug "univMinim".
Set Debug "backtrace".
Lemma foo@{s| |} : forall (b : bool@{s|}),
    eq _ b true ->
    eq _ match b with
    | true => b
    | false => b end b.
Proof.
  Show Universes.
  intros b H.
  rewrite H.
  reflexivity.
  Qed.
