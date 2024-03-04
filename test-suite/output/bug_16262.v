Declare Scope foo.
Delimit Scope foo with foo.
Check (nat -> nat).
Notation "a -> b" := (a,b)
   (b at level 200, only printing, right associativity, at level 99,
   format "a -> b") : foo.
Check (nat -> nat).
Check (1,2).
Reserved Notation "a -> b"
   (b at level 200, only printing, right associativity, at level 99,
   format "a -> b").
Check (nat -> nat).
