Require Import ssreflect.


Axiom app : forall T, list T -> list T -> list T.
Arguments app {_}.
Infix "++" := app.

Lemma test (aT rT : Type)
           (pmap : (aT -> option rT) -> list aT -> list rT)
           (perm_eq : list rT -> list rT -> Prop)
           (f : aT -> option rT)
           (g : rT -> aT)
           (s t : list aT)
           (E : forall T : list aT -> Type,
               (forall s1 s2 s3 : list aT,
                  T (s1 ++ s2 ++ s3) -> T (s2 ++ s1 ++ s3)) ->
                 T s -> T t) :
        perm_eq (pmap f s) (pmap f t).
Proof.
elim/E: (t).
Admitted.


Lemma test2 (a b : nat) : a = b -> b = 1.
Proof.
elim.
match goal with |- a = 1 => idtac end.
Admitted.

