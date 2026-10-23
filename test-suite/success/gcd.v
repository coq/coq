(* Preserve the original Euclidean definition as a guard-checking test:
   modulo produces a strict subterm through subtraction. *)
Module TraversingSubterm.
Fixpoint gcd a b :=
  match a with
  | O => b
  | S a' => gcd (Nat.modulo b (S a')) (S a')
  end.

Example gcd_S a b : gcd (S a) b = gcd (Nat.modulo b (S a)) (S a).
Proof. reflexivity. Qed.
End TraversingSubterm.

Example gcd_0 b : Nat.gcd 0 b = b.
Proof. reflexivity. Qed.

Example gcd_S a b :
  Nat.gcd (S a) b = Nat.gcd (Nat.modulo b (S a)) (S a).
Proof.
  Fail reflexivity.
  apply Nat.gcd_S.
Qed.

Example gcd0_spec a k b : Nat.gcd0 a k b = Nat.gcd (a - k) b.
Proof. apply Nat.gcd0_spec. Qed.

Example gcd_examples :
  Nat.gcd 0 0 = 0 /\ Nat.gcd 0 7 = 7 /\ Nat.gcd 7 0 = 7 /\
  Nat.gcd 12 12 = 12 /\ Nat.gcd 12 18 = 6 /\ Nat.gcd 18 12 = 6 /\
  Nat.gcd 7 13 = 1.
Proof. repeat split; reflexivity. Qed.

Example gcd_matches_original :
  Nat.gcd 12 18 = TraversingSubterm.gcd 12 18.
Proof. reflexivity. Qed.
