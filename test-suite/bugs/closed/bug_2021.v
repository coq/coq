(* correct failure of injection/discriminate on types whose inductive
   status derives from the substitution of an argument *)

Unset Structural Injection.

Inductive t : nat -> Type :=
| M : forall n: nat, nat -> t n.

Lemma eq_t : forall n n' m m',
   existT (fun B : Type => B) (t n) (M n m) =
   existT (fun B : Type => B) (t n') (M n' m') -> True.
Proof.
  intros.
  injection H.
  intro Ht.
  exact I.
Qed.

Lemma eq_t' : forall n n' : nat,
   existT (fun B : Type => B) (t n) (M n 0) =
   existT (fun B : Type => B) (t n') (M n' 1) -> True.
Proof.
  intros.
  discriminate H || exact I.
Qed.
