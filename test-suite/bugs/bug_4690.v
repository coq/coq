(* Check that @f is not allowed in notation when f is a notation variable *)

Fail Notation "# g" := (@g O) (at level 0).
