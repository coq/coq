Require Export NAxioms.

(* We would like to have a signature for the predecessor: first, to be
able to provide an efficient implementation, and second, to be able to
use this function in the signatures defining other functions, e.g.,
subtraction. If we just define predecessor by recursion in
NatProperties functor, we would not be able to use it in other
signatures. *)

Module Type NPredSignature.
Declare Module Export NatModule : NatSignature.
Open Local Scope NatScope.

Parameter Inline P : N -> N.

Add Morphism P with signature E ==> E as P_wd.

Axiom P_0 : P 0 == 0.
Axiom P_S : forall n, P (S n) == n.

End NPredSignature.

Module NDefPred (Import NM : NatSignature) <: NPredSignature.
Module NatModule := NM.
Open Local Scope NatScope.

Definition P (n : N) : N := recursion 0 (fun m _ : N => m) n.

Add Morphism P with signature E ==> E as P_wd.
Proof.
intros; unfold P.
now apply recursion_wd with (EA := E); [| unfold eq_fun2; now intros |].
Qed.

Theorem P_0 : P 0 == 0.
Proof.
unfold P; now rewrite recursion_0.
Qed.

Theorem P_S : forall n, P (S n) == n.
Proof.
intro n; unfold P; now rewrite (recursion_S E); [| unfold fun2_wd; now intros |].
Qed.

End NDefPred.
