Definition wtf (n : nat) : nat :=
  (match n with
       0 => (fun H : n = 0 => 0)
     | S n' => (fun H : n = S n' => 0)
   end) (eq_refl n).
