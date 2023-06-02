Inductive foo : nat -> Type :=
| fz : foo 0
| fs : forall {n}, foo (S n).

Definition test (n : nat) : foo n -> nat.
refine (
  match n with
  | 0 =>
    fun f =>
      match f in foo n return match n with 0 => nat | S _ => unit end with
      | fz => 0
      | fs => tt
      end
  | S n =>
    fun f =>
      match f in foo n return match n with 0 => unit | S _ => nat end with
      | fz => tt
      | fs => 42
      end
  end).
Qed.

Definition test2 n : foo n -> nat.
  refine (
  match n with
  | 0 =>
    fun (f: foo 0) =>
      match f in foo n return match n with 0 => nat | S _ => unit end with
      | fz => 0
      | fs => tt
      end
  | S n =>
    fun f =>
      match f in foo n return match n with 0 => unit | S _ => nat end with
      | fz => tt
      | fs => 42
      end
  end).
Qed.

Definition test3 (n : nat) : foo n -> nat :=
  match n with
  | 0 =>
    fun f =>
      match f in foo n return match n with 0 => nat | S _ => unit end with
      | fz => 0
      | fs => tt
      end
  | S n =>
    fun f =>
      match f in foo n return match n with 0 => unit | S _ => nat end with
      | fz => tt
      | fs => 42
      end
  end.

Definition test4 (n : nat) : bool -> foo n -> nat :=
  match n with
  | 0 =>
    fun b f =>
      match f in foo n return match n with 0 => nat | S _ => unit end with
      | fz => 0
      | fs => tt
      end
  | S _ =>
    fun b f =>
      match f in foo n return match n with 0 => unit | S _ => nat end with
      | fz => tt
      | fs => 42
      end
  end.
