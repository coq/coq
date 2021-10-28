Section Test.
  Variables (bool_var : bool) (clashing_name : nat) (All : unit).
  Collection clashing_name := bool_var.

  Collection redefined_col := bool_var.
  Collection redefined_col := bool_var.

  Fail Collection All := bool_var.

  Lemma foo : True.
  Proof using clashing_name.
    trivial.
  Qed.

  Lemma bar : True.
  Proof using All.
    trivial.
  Qed.

End Test.

Check foo : bool -> True.
Check bar : bool -> nat -> unit -> True.
