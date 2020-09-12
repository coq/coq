

Definition nat_eq_dec(i j:nat) : {i=j}+{i<>j}.
Proof.
  pose (diseq := false).
  decide equality.
Defined.

Set Mangle Names.
Definition nat_eq_dec_mangle (i j:nat) : {i=j}+{i<>j}.
Proof.
  decide equality. (*Error: Anomaly "variable diseq unbound." ...*)
Defined.
