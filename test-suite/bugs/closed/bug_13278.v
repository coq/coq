Inductive even: nat -> Prop :=
| evenB: even 0
| evenS: forall n, even n -> even (S (S n)).

Goal even 1 -> False.
Proof.
  refine (fun a => match a with end).
Qed.

Goal even 1 -> False.
Proof.
  refine (fun a => match a in even n
                   return match n with 1 => False | _ => True end : Prop
                   with evenB => I | evenS _ _ => I end).
Qed.
