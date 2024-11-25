From Corelib Require Import ssreflect.

Axiom T : Type.
Axiom R : T -> T -> Type.

(** Check that internal exceptions are correctly caught in the monad *)
Goal forall (a b : T) (Hab : R a b), True.
Proof.
intros.
try (case: Hab).
Abort.
