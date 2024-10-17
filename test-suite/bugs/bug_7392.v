Class ElimInv {X Y : Type} (Pout : X -> Y) (Pclose : X -> option Y) :=
  elim_inv : False.

Class IntoAcc {X Y : Type} (E1 E2 : nat) (α β : X -> Y) :=
  into_acc : False.

Global Instance elim_inv_acc_with_close {X Y : Type} E1 E2 α β (foo : nat -> nat -> Y -> Y) :
  IntoAcc E1 E2 α β ->
  ElimInv (X:=X) (Y:=Y) α (fun x => Some (foo E1 E2 (β x))).
Proof. intros []. Qed.

Lemma tac_inv_elim {X Y : Type} Pout Pclose :
  ElimInv (X:=X) (Y:=Y) Pout Pclose ->
  False.
Proof. intros []. Qed.

Global Instance into_acc_na E n :
  IntoAcc (X:=unit) (Y:=nat) E E (fun _ => 0) (fun _ => 5 + n).
Proof. Admitted.

Goal False.
eapply tac_inv_elim with (Pclose:=(fun xx => Some _)).
eapply @elim_inv_acc_with_close.
eapply @into_acc_na. (* EXPLOSION *)
Abort.
