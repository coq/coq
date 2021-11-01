(* Test the behaviour of hnf and simpl *)

Parameter n:nat.
Definition a:=0.

Eval simpl in (fix plus (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (p + m)
  end) a a.

Eval hnf in match (plus (S n) O) with S n => n | _ => O end.

(* only 1 cast *)
Lemma foo : 1 + 1 = 2.
Proof.
  do 5 simpl; exact (eq_refl 2).
Defined.
Set Printing All.
Print foo.
