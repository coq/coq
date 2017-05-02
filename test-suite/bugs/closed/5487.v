(* Was a collision between an ltac pattern variable and an evar *)

Goal forall n, exists m, n = m :> nat.
Proof.
  eexists.
  Fail match goal with
  | [ |- ?x = ?y ]
    => match x with y => idtac end
  end.
