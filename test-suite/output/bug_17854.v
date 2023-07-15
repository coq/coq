Fail Check fun b : bool
      => match b, b with
         | true as a, true as a | true as a, _ => true
         | _, _ => false
         end.

Fail Check fun b : bool
      => match b, b with
         | true as a, true as a => true
         | _, _ => false
         end.

Definition f b :=
         match b, b with
         | true as a as a, true as b => true
         | _, _ => false
         end.
