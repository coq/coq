(** Occur-check for Meta (up to application of already known instances) *)

Goal forall (f: nat -> nat -> Prop) (x:bool)
  (H: forall  (u: nat), f u u -> True)
  (H0: forall x0, f (if x then x0 else x0) x0),
False.

intros.
Fail apply H in H0. (* should fail without exhausting the stack *)
