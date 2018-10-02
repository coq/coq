(* Use of idents bound to ltac names in a "match" *)

Definition foo : Type.
Proof.
  let x := fresh "a" in
  refine (forall k : nat * nat, let '(x, _) := k in (_ : Type)).
  exact (a = a).
Defined.
Goal foo.
intros k. elim k. (* elim because elim keeps names *)
intros.
Check a. (* We check that the name is "a" *)
