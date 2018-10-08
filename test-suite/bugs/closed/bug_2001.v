(* Automatic computing of guard in "Theorem with"; check that guard is not
   computed when the user explicitly indicated it *)

Unset Automatic Introduction.

Inductive T : Set :=
| v : T.

Definition f (s:nat) (t:T) : nat.
fix f 2.
intros s t.
refine
  match t with
  | v => s
  end.
Defined.

Lemma test :
  forall s, f s v = s.
Proof.
reflexivity.
Qed.
