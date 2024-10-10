Module Bool.
Definition eqb (b1 b2 : bool) :=
  if b1 then if b2 then true else false else if b2 then false else true.
End Bool.
