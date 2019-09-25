
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

Unset Universe Checking.

Definition T := Type.
Fixpoint g (n : nat) : T := T.

Print Typing Flags.
Set Universe Checking.

Fail Definition g2 (n : nat) : T := T.

Fail Definition e := fix e (n : nat) : nat := e n.

Unset Positivity Checking.

Inductive Cor :=
| Over : Cor
| Next : ((Cor -> list nat) -> list nat) -> Cor.

Set Positivity Checking.
Print Assumptions Cor.

Inductive Box :=
| box : forall n, f n = n -> g 2 -> Box.

Print Assumptions Box.

Unset Guard Checking.
Set Sized Typing.

(* Fails with guard checking but not with sized typing *)
Fixpoint div x y :=
  match x with
  | O => O
  | S x' => S (div (minus x' y) y)
  end.

(* The below are lifted from theories/Init/Nat.v *)

Fixpoint divmod x y q u :=
  match x with
  | 0 => (q,u)
  | S x' =>
    match u with
    | 0 => divmod x' y (S q) y
    | S u' => divmod x' y q u'
    end
  end.

Definition modulo x y :=
  match y with
  | 0 => y
  | S y' => y' - snd (divmod x y' 0 y')
  end.

Infix "mod" := modulo (at level 40, no associativity) : nat_scope.

(* Fails with sized typing but not with guard checking *)
Fail Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (b mod (S a')) (S a')
  end.
