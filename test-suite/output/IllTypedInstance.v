Set Primitive Projections.

Record prod A B := pair { fst: A; snd : B }.
Arguments pair {_ _}.

Record Apply (A B : Type) : Type := {apply : A -> B}.
Fail Check fun (T : Type) (b : T) => eq_refl : @apply (prod T T) T _ (pair _ _) = @apply T T _ b.
