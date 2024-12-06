From Stdlib Require Import Vector.

Axiom exfalso : False.

Fixpoint all_then_someV (n:nat) (l:Vector.t bool n) {struct l}:
(Vector.fold_left orb false l) = false ->
(forall p, (Vector.nth l p  ) = false).
Proof.
intros.
destruct l.
inversion p.
revert h l H.
set (P := fun n p => forall (h : bool) (l : t bool n),
fold_left orb false (cons bool h n l) = false -> @eq bool (@nth bool (S n) (cons bool h n l) p) false).
revert n p.
fix loop 1.
unshelve eapply (@Fin.rectS P).
+ elim exfalso.
+ unfold P.
  intros.
  eapply all_then_someV.
  exact H0.
Fail Defined.
Abort.
