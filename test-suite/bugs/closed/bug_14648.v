Lemma foo : Prop.
Proof.
  let bad := open_constr:(_ : nat) in
  unshelve let bod := open_constr:((fun x : nat => _ : Prop) bad) in
  let bod := eval cbv in bod in
  exact bod.
  exact True.

  Set Warnings "+remaining-shelved-goals".
  Fail Qed.
  Set Warnings "-remaining-shelved-goals".
Qed.
