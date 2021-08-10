Set Warnings "-remaining-shelved-goals".
Goal 1 + 1 = 2.
Proof.
  Fail match goal with |- ?l = ?l => idtac end.
  let p := open_constr:(_ + _) in simpl p.
  match goal with |- ?l = ?l => idtac end.
  reflexivity.
Qed.
