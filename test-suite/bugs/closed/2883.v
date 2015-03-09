Require Import TestSuite.admit.
Require Import List.
Require Import Coq.Program.Equality.

Inductive star {genv state : Type}
  (step : genv -> state -> state -> Prop)
  (ge : genv) : state -> state -> Prop :=
  | star_refl : forall s : state, star step ge s s
  | star_step :
    forall (s1 : state) (s2 : state)
      (s3 : state),
      step ge s1 s2 ->
      star step ge s2 s3 ->
      star step ge s1 s3.

Parameter genv expr env mem : Type.
Definition genv' := genv.
Inductive state : Type :=
 | State : expr -> env -> mem -> state.
Parameter step : genv' -> state -> state -> Prop.

Section Test.

Variable ge : genv'.

Lemma compat_eval_steps:
  forall a b e a' b',
  star step ge (State a e b) (State a' e b') ->
  True.
Proof.
  intros. dependent induction H.
  trivial.
  eapply IHstar; eauto.
  replace s2 with (State a' e b') by admit. eauto.
Qed. (* Oups *)
