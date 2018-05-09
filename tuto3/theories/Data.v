Class EvenNat n := {half : nat; half_prop : 2 * half = n}.

Instance EvenNat2 : EvenNat 2 := {half := 1; half_prop := eq_refl}.

Instance EvenNat4 : EvenNat 4 := {half := 2; half_prop := eq_refl}.

Definition tuto_div2 n (p : EvenNat n) := @half n p.


