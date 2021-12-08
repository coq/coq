(* Fix and Cofix were missing in tactic unification *)

Goal exists e, (fix foo (n : nat) : nat := match n with O => e | S n' => foo n' end)
               = (fix foo (n : nat) : nat := match n with O => O | S n' => foo n' end).
Proof.
  eexists.
  reflexivity.
Qed.

CoInductive stream := cons : nat -> stream -> stream.

Goal exists e, (cofix foo := cons e foo) = (cofix foo := cons 0 foo).
Proof.
  eexists.
  reflexivity.
Qed.
