Require Import List.
Program Fixpoint f (a : nat) : { x : nat | x > 0 } := 
  match a with
  | 0 => 1
  | S a' => g a a'
  end
with g (a b : nat) { struct b } : { x : nat | x > 0 } := 
  match b with
  | 0 => 1
  | S b' => f b'
  end.

Check f.
Check g.





