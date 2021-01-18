#[if(SHELL)] Goal True.
Proof.
idtac.
#[if(USER = " me ")] exact 1.
#[if(not(USER = " you "))] exact I.
Qed.
