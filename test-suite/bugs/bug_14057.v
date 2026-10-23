Module Mono.
  Module Transparent.
    Fixpoint F (n : nat) (A : Type) {struct n} : nat
    with G (n : nat) (A:Type)  {struct n} : nat.
    Proof.
      1: pose (match n with S n => G n A | 0 => 0 end).
      all: exact 0.
    Defined.
  End Transparent.

  Module Opaque.
    Fixpoint F (n : nat) (A : Type) {struct n} : nat
    with G (n : nat) (A:Type)  {struct n} : nat.
    Proof.
      1: pose (match n with S n => G n A | 0 => 0 end).
      all: exact 0.
    Qed.
  End Opaque.
End Mono.

Module Poly.
  Set Universe Polymorphism.
  Module Transparent.
    Fixpoint F (n : nat) (A : Type) {struct n} : nat
    with G (n : nat) (A:Type)  {struct n} : nat.
    Proof.
      1: refine (match n with S n => G n A | 0 => 0 end).
      1: refine (match n with S n => F n A | 0 => 0 end).
    Defined.
    Check F@{_}. Check G@{_}.
  End Transparent.

  Module Opaque.
    Fixpoint F (n : nat) (A : Type) {struct n} : nat
    with G (n : nat) (A:Type)  {struct n} : nat.
    Proof.
      1: pose (match n with S n => G n A | 0 => 0 end).
      all: exact 0.
    Qed.
    Check F@{_}. Check G@{_ _}.
  End Opaque.
End Poly.
