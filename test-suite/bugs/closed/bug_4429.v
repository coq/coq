Require Import Arith.Compare_dec.
Require Import Unicode.Utf8.

Fixpoint my_nat_iter (n : nat) {A} (f : A → A) (x : A) : A :=
  match n with
    | O    => x
    | S n' => f (my_nat_iter n' f x)
  end.

Definition gcd_IT_F (f : nat * nat → nat) (mn : nat * nat) : nat :=
  match mn with
    | (0, 0)       => 0
    | (0, S n')    => S n'
    | (S m', 0)    => S m'
    | (S m', S n') =>
      match le_gt_dec (S m') (S n') with
        | left  _ => f (S m', S n' - S m')
        | right _ => f (S m' - S n', S n')
      end
  end.

Axiom max_correct_l : ∀ m n : nat, m <= max m n.
Axiom max_correct_r : ∀ m n : nat, n <= max m n.

Hint Resolve max_correct_l max_correct_r : arith.

Theorem foo : ∀ p p' p'' : nat, p'' < S (max p (max p' p'')).
Proof.
  intros.
  Timeout 3 eauto with arith.
Qed.
