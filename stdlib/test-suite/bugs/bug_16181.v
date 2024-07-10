From Stdlib Require Import Equality.

Inductive star {genv state : Type}
  (step : genv -> state -> state -> Prop)
  (ge : genv) : state -> state -> Prop :=
  | star_refl : forall s : state, star step ge s s
.

Parameter genv expr env mem : Type.

Inductive state : Type :=
 | State : expr -> env -> mem -> state.
Parameter step : genv -> state -> state -> Prop.

Section Test.

Variable ge : genv.
Axiom admit:False.

Set Printing Universes. Set Printing All.
Lemma compat_eval_steps
   a b e a' b'
  (H:star step ge (State a e b) (State a' e b'))
  : True.
Proof.
  intro_block H.

  generalize_eqs_vars H.
  destruct admit.
Qed.
(* Error: Illegal application:
The term "@eq_refl" of type "forall (A : Type@{eq.u0}) (x : A), @eq A x x"
cannot be applied to the terms
 "Type@{foo.11}" : "Type@{foo.11+1}"
 "genv" : "Type@{genv.u0}"
The 1st term has type "Type@{foo.11+1}" which should be coercible to "Type@{eq.u0}".
 *)
End Test.
