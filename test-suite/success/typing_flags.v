
Print Typing Flags.
Unset Guard Checking.
Fixpoint f' (n : nat) : nat := f' n.

Fixpoint f (n : nat) : nat.
Proof.
  exact (f n).
Defined.

Fixpoint bla (A:Type) (n:nat) := match n with 0 =>0 | S n => n end.

Print Typing Flags.

Set Guard Checking.

Print Assumptions f.

Unset Universes Checking.

Definition T := Type.
Fixpoint g (n : nat) : T := T.

Print Typing Flags.
Set Universes Checking.

Fail Definition g2 (n : nat) : T := T.

Fail Definition e := fix e (n : nat) : nat := e n.

Unset Positivity Checking.

Inductive Cor :=
| Over : Cor
| Next : ((Cor -> list nat) -> list nat) -> Cor.

Set Positivity Checking.
Print Assumptions Cor.
