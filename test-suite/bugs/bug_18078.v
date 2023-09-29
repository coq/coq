(* Meaning: P implies Q and the only reasonable way to
   prove Q is to try proving P. *)
Definition safe_implication(P: Prop)(Q: Prop): Prop := P -> Q.

Create HintDb safe_implication.

Ltac apply_safe_implication :=
  lazymatch goal with
  | |- ?Q =>
      let H := fresh in
      eassert (safe_implication _ Q) as H by (typeclasses eauto with safe_implication);
      unfold safe_implication in H;
      apply H;
      clear H
  end.

Parameter f: nat -> nat -> Prop.
Parameter g: nat -> Prop.
Parameter h: nat -> Prop.

Axiom f_same_args: forall x, safe_implication (g x) (f x x).
Axiom f_first_arg_0: forall x, safe_implication (h x) (f 0 x).

#[export] Hint Resolve f_first_arg_0 f_same_args : safe_implication.

#[global] Hint Mode safe_implication - + : safe_implication.

Goal forall a, 0 < a -> h a -> exists b, f 0 b /\ 0 < b.
Proof.
  intros. eexists. split.

  apply_safe_implication.

  all: eassumption.
Qed.
