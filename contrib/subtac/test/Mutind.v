Fixpoint f (a : nat) : nat := match a with 0 => 0
| S a' => g a a'
  end
with g (a b : nat) { struct b } : nat := 
  match b with 0 => 0
  | S b' => f b'
  end.