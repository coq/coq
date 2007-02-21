(* Check that dependent rewrite applies on arbitrary terms *)

Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n : nat, nat -> listn n -> listn (S n).

Axiom
  ax :
    forall (n n' : nat) (l : listn (n + n')) (l' : listn (n' + n)),
    existS _ (n + n') l = existS _ (n' + n) l'.

Lemma lem :
 forall (n n' : nat) (l : listn (n + n')) (l' : listn (n' + n)),
 n + n' = n' + n /\ existT _ (n + n') l = existT _ (n' + n) l'.
Proof.
intros n n' l l'.
 dependent rewrite (ax n n' l l').
split; reflexivity.
Qed.

(* Used to raise an anomaly instead of an error in 8.1 *)
(* Submitted by Y. Makarov *)

Parameter N : Set.
Parameter E : N -> N -> Prop.

Axiom e : forall (A : Set) (EA : A -> A -> Prop) (a : A), EA a a.

Theorem th : forall x : N, E x x.
intro x. try rewrite e.
Abort.
