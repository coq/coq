(* An occur-check test was done too early *)

Goal forall B C : nat -> nat -> Prop, forall k,
  (exists A, (forall k', C A k' -> B A k') -> B A k).
Proof.
  intros B C k.
  econstructor.
  intros X.
  apply X. (* used to fail here *)
