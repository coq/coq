Set Universe Polymorphism.

Definition demo@{srt|u |} : True.
Proof.
  abstract exact I.
Defined.

(* abstract doesn't restrict named qualities and universes
   (debatable behaviour but that's what it does currently) *)
Check demo@{Type|Set}.

Definition baz@{q|u|} (A:Type@{q|u}) (x:A) : A.
Proof.
  abstract exact x.
Defined.
