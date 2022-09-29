Definition foo1 : nat.
Proof.
    abstract (exact 1) using toto1.
    Print toto1.
Defined.
Print toto1.

Definition foo2 : nat := ltac:(abstract (exact 1) using toto2).
Print toto2.

Definition foo3 : nat.
Proof.
    abstract (exact 1) using toto3.
Admitted.
Fail Print toto3.

Definition foo4 : nat.
Proof.
    abstract (exact 1) using toto4.
Qed.
Fail Print toto4.

Definition foo5 : nat.
Proof.
    abstract (exact 1) using toto5.
Abort.
Print toto5.
