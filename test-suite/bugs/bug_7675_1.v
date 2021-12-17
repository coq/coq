Require Import Setoid CMorphisms.

Parameter A: Type.

Inductive R :  A ->  A -> Type :=
| perm1 l: R l l
| perm2 l l' : R l l' -> R l l'.
(* requires at least two constructors for the issue to appear *)

#[local] Instance HR : Transitive R. Admitted.

Goal forall h k, R h k -> R h k.
Proof.
  intros h k H.
  Succeed rewrite H.
  assumption.
Qed.
