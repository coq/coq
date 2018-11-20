
Module Type T.
  Parameter foo : nat -> nat.
End T.

Module F (A:T).
  Inductive ind (n:nat) : nat -> Prop :=
  | C : (forall x, x < n -> ind (A.foo n) x) -> ind n n.
End F.

Module A. Definition foo (n:nat) := n. End A.

Module M := F A.
(* Note: M.ind could be seen as having 1 recursively uniform
   parameter, but module substitution does not recognize it, so it is
   treated as a non-uniform parameter. *)
