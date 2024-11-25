From Corelib Require Import ssreflect.

Axiom subnn : forall n : nat, n - n = 0.
Parameter G : (nat -> nat) -> nat -> nat.
Axiom eq_G :
  forall F1 F2 : nat -> nat,
    (forall n : nat, F1 n = F2 n) ->
    forall n : nat, G F1 n = G F2 n.

Ltac show := match goal with [|-?g] => idtac g end.

Lemma example_G (n : nat) : G (fun n => n - n) n >= 0.
under eq_G => m do [show; rewrite subnn].
show.
Abort.

Parameters (R Rbar : Set) (R0 : R) (Rbar0 : Rbar).
Parameter Rbar_le : Rbar -> Rbar -> Prop.
Parameter Lub_Rbar : (R -> Prop) -> Rbar.
Parameter Lub_Rbar_eqset :
  forall E1 E2 : R -> Prop,
    (forall x : R, E1 x <-> E2 x) ->
    Lub_Rbar E1 = Lub_Rbar E2.

Lemma test_Lub_Rbar (E : R -> Prop)  :
  Rbar_le Rbar0 (Lub_Rbar (fun x => x = R0 \/ E x)).
Proof.
under Lub_Rbar_eqset => r do show.
show.
Abort.
