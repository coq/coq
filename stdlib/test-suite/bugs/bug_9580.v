From Stdlib Require Import List.
From Stdlib Require Import Decidable PeanoNat.

Theorem count_occ_cons: forall l1 l2 (p1 p2:nat) n, count_occ Nat.eq_dec l1 p1 + n =
    count_occ Nat.eq_dec l2 p1 ->
    count_occ Nat.eq_dec (p2 :: l1) p1 + n = count_occ Nat.eq_dec (p2 :: l2) p1.
Proof.
  intros. destruct (Nat.eq_dec p2 p1).
  - eapply eq_trans.
    + eapply eq_ind_r with (A:=nat) (x:= _) (P:= (fun x => x + n = _)).
      eapply eq_refl. eapply count_occ_cons_eq. apply e.
    + eapply eq_trans. (* <-- Error used to be: Anomaly "Uncaught exception Not_found." *)
Abort.
