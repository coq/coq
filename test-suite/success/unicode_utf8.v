(* Check correct separation of identifiers followed by unicode symbols *)
  Notation "x 〈 w" := (plus x w) (at level 30).
  Check fun x => x〈x.

(* Check Greek letters *)
Definition test_greek : nat -> nat := fun Δ => Δ.
Parameter ℝ : Set.
Parameter π : ℝ.

(* Check indices *)
Definition test_indices : nat -> nat := fun x₁ => x₁.
Definition π₂ := snd.
